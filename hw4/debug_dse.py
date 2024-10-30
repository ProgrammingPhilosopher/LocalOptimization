import sys
import json
from collections import defaultdict, deque
from form_blocks import form_blocks
from util import flatten

def construct_cfg(blocks):
    labels = []
    block_map = {}
    for idx, block in enumerate(blocks):
        if 'label' in block[0]:
            label = block[0]['label']
        else:
            label = f'<bb{idx}>'
        labels.append(label)
        block_map[label] = block

    cfg = {label: [] for label in labels}
    for idx, block in enumerate(blocks):
        label = labels[idx]
        last_instr = block[-1] if block else None
        if last_instr and 'op' in last_instr:
            op = last_instr['op']
            if op == 'br':
                cfg[label].extend(last_instr['labels'])
            elif op == 'jmp':
                cfg[label].append(last_instr['labels'][0])
            else:
                if idx + 1 < len(blocks):
                    cfg[label].append(labels[idx + 1])
        else:
            if idx + 1 < len(blocks):
                cfg[label].append(labels[idx + 1])
    return cfg, labels

def alias_analysis(blocks, cfg, labels, func_args, alloc_sites):
    block_map = dict(zip(labels, blocks))
    in_state = {label: {} for label in labels}
    out_state = {label: {} for label in labels}

    # Initialize the analysis state
    init_state = {}
    for arg in func_args:
        init_state[arg] = set(['unknown'])

    worklist = deque(labels)
    while worklist:
        label = worklist.popleft()
        block = block_map[label]
        in_map = {}
        preds = [pred for pred in cfg if label in cfg[pred]]
        if preds:
            for pred in preds:
                pred_out = out_state[pred]
                for var in pred_out:
                    in_map.setdefault(var, set()).update(pred_out[var])
        else:
            in_map = {var: locs.copy() for var, locs in init_state.items()}

        # **Add this line to update in_state**
        in_state[label] = in_map.copy()

        old_out = out_state[label]
        out_map = analyze_block(block, in_map, alloc_sites)
        out_state[label] = out_map
        if out_map != old_out:
            for succ in cfg[label]:
                if succ not in worklist:
                    worklist.append(succ)
        print(f"[Alias Analysis] Block: {label}, In-State: {in_map}")
        print(f"[Alias Analysis] Block: {label}, Out-State: {out_map}")
    return in_state, out_state

def analyze_block(block, in_map, alloc_sites):
    state = {var: locs.copy() for var, locs in in_map.items()}
    for instr in block:
        if 'op' in instr:
            op = instr['op']
            dest = instr.get('dest')
            args = instr.get('args', [])
            if op == 'alloc':
                # x = alloc n: x points to this allocation
                alloc_site = alloc_sites[id(instr)]
                state[dest] = set([alloc_site])
            elif op == 'id':
                y = args[0]
                if y in state:
                    # Only update if y is in state
                    state[dest] = state[y].copy()
            elif op == 'ptradd':
                p = args[0]
                if p in state:
                    # Only update if p is in state
                    state[dest] = state[p].copy()
            elif op == 'load':
                # x = load p: x points to all memory locations
                state[dest] = set(['unknown'])
            elif op == 'call':
                # Function calls can change pointers conservatively
                state[dest] = set(['unknown'])
            # Do not update state for non-pointer variables
    return state

def memory_liveness_analysis(blocks, cfg, labels, alias_info):
    block_map = dict(zip(labels, blocks))
    live_in = {label: set() for label in labels}
    live_out = {label: set() for label in labels}
    changed = True
    while changed:
        changed = False
        for label in reversed(labels):
            block = block_map[label]
            alias_maps = alias_info[label]
            out_set = set()
            succs = cfg.get(label, [])
            for succ in succs:
                out_set.update(live_in[succ])
            old_in = live_in[label].copy()
            live_out[label] = out_set.copy()
            in_set = analyze_memory_uses(block, live_out[label], alias_maps)
            live_in[label] = in_set
            if live_in[label] != old_in:
                changed = True
    print(f"[Liveness] Block: {label}, Live-In: {live_in[label]}")
    print(f"[Liveness] Block: {label}, Live-Out: {live_out[label]}")
    return live_in, live_out

def analyze_memory_uses(block, live_out_set, alias_maps):
    live_set = live_out_set.copy()
    for idx in reversed(range(len(block))):
        instr = block[idx]
        alias_map = alias_maps[idx]
        if 'op' in instr:
            op = instr['op']
            args = instr.get('args', [])
            if op == 'ret':
                if args:
                    ret_var = args[0]
                    pts = alias_map.get(ret_var, set())
                    live_set.update(pts)
            elif op == 'store':
                p = args[0]
                pts = alias_map.get(p, set())
                print(f"[Store Operation] Address: {p}, Points-To: {pts}, Live-Set Before: {live_set}")
                live_set.update(pts)
            elif op == 'load':
                p = args[0]
                pts = alias_map.get(p, set())
                live_set.update(pts)
            elif op == 'free':
                p = args[0]
                pts = alias_map.get(p, set())
                live_set -= pts
            elif op == 'call':
                for arg in args:
                    pts = alias_map.get(arg, set())
                    live_set.update(pts)
    return live_set

def remove_dead_stores(func, alias_info, live_out):
    blocks = list(form_blocks(func['instrs']))
    cfg, labels = construct_cfg(blocks)
    block_map = dict(zip(labels, blocks))
    for label in labels:
        block = block_map[label]
        alias_maps = alias_info[label]
        live_vars = live_out[label].copy()
        new_block = []
        for idx in reversed(range(len(block))):
            instr = block[idx]
            alias_map = alias_maps[idx]
            if 'op' in instr and instr['op'] == 'store':
                p = instr['args'][0]
                pts = alias_map.get(p, set())
                if pts.isdisjoint(live_vars) and 'unknown' not in pts and 'unknown' not in live_vars:
                    print(f"[Remove Decision] Store Instruction: {instr}, Points-To: {pts}, Live Vars: {live_vars}")
                    # Store is dead, eliminate it
                    continue
                print(f"[Keep Decision] Store Instruction: {instr}, Points-To: {pts}, Live Vars: {live_vars}")
            if 'op' in instr:
                op = instr['op']
                args = instr.get('args', [])
                if op == 'load':
                    p = args[0]
                    pts = alias_map.get(p, set())
                    live_vars.update(pts)
                elif op == 'free':
                    p = args[0]
                    pts = alias_map.get(p, set())
                    live_vars -= pts
                elif op == 'ret':
                    if args:
                        ret_var = args[0]
                        pts = alias_map.get(ret_var, set())
                        live_vars.update(pts)
                elif op == 'call':
                    for arg in args:
                        pts = alias_map.get(arg, set())
                        live_vars.update(pts)
            new_block.append(instr)
        block[:] = reversed(new_block)
    func['instrs'] = flatten([block_map[label] for label in labels])


def collect_alloc_sites(func):
    alloc_sites = {}
    counter = 0
    for instr in func['instrs']:
        if 'op' in instr and instr['op'] == 'alloc':
            alloc_sites[id(instr)] = f'alloc_{counter}'
            counter += 1
    return alloc_sites

def get_func_args(func):
    args = []
    for arg in func.get('args', []):
        args.append(arg['name'])
    return args

def optimize_function(func):
    blocks = list(form_blocks(func['instrs']))
    print("\nBlocks:", blocks)
    cfg, labels = construct_cfg(blocks)
    print("\nCFG:", cfg)
    print("\nLabels:", labels)
    alloc_sites = collect_alloc_sites(func)
    print("\nAlloc Sites:", alloc_sites)
    func_args = get_func_args(func)
    print("\nFunction Arguments:", func_args)
    # Perform alias analysis
    in_alias, out_alias = alias_analysis(blocks, cfg, labels, func_args, alloc_sites)
    print("\nIn Alias:", in_alias)
    print("\nOut Alias:", out_alias)
    # Get alias info at each instruction
    alias_info = {}
    block_map = dict(zip(labels, blocks))
    print("\nBlock Map:", block_map)
    for label in labels:
        print("\nCurrent Label:", label)
        block = block_map[label]
        print("\nCurrent Block:", block)
        state = {var: locs.copy() for var, locs in in_alias.get(label, {}).items()}
        print("\nState:", state)
        alias_maps = []
        for instr in block:
            print("\nCurrent Instruction:", instr)
            alias_maps.append(state.copy())
            if 'op' in instr:
                op = instr['op']
                dest = instr.get('dest')
                args = instr.get('args', [])
                if op == 'alloc':
                    alloc_site = alloc_sites[id(instr)]
                    state[dest] = set([alloc_site])
                    print("\nop=='alloc', Alloc Site:", alloc_site)
                elif op == 'id':
                    y = args[0]
                    state[dest] = state.get(y, set()).copy()
                    print("\nop=='id', Y:", y)
                elif op == 'ptradd':
                    p = args[0]
                    state[dest] = state.get(p, set()).copy()
                    print("\nop=='ptradd', P:", p)
                elif op == 'load':
                    state[dest] = set(['unknown'])
                    print("\nop=='load'")
                elif op == 'call':
                    state[dest] = set(['unknown'])
                    print("\nop=='call'")
        alias_info[label] = alias_maps  # Store the list of alias maps
        print("\nAlias Info[label]:", alias_info[label])
    # Perform memory liveness analysis
    live_in, live_out = memory_liveness_analysis(blocks, cfg, labels, alias_info)
    print("\nLive-In:", live_in)
    print("\nLive-Out:", live_out)
    # Remove dead stores
    remove_dead_stores(func, alias_info, live_out)

def main():
    program = json.load(sys.stdin)
    for func in program['functions']:
        print("Current Function:", func)
        optimize_function(func)
    # print(program)
    # json.dump(program, sys.stdout, indent=2)

if __name__ == '__main__':
    main()
