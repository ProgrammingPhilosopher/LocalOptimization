import sys
import json
from collections import defaultdict, deque
from form_blocks import form_blocks
from util import flatten

def is_essential(instr):
    return 'op' in instr and instr['op'] in {'print', 'br', 'jmp', 'ret', 'call', 'store', 'free'}

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

def liveness_analysis(blocks, cfg, labels):
    block_map = dict(zip(labels, blocks))
    live_in = {label: set() for label in labels}
    live_out = {label: set() for label in labels}
    uses = {}
    defines = {}
    for label in labels:
        block = block_map[label]
        defs = set()
        use = set()
        for instr in block:
            if 'op' in instr:
                args = instr.get('args', [])
                dest = instr.get('dest')
                for arg in args:
                    if arg not in defs:
                        use.add(arg)
                if dest:
                    defs.add(dest)
        uses[label] = use
        defines[label] = defs

    changed = True
    while changed:
        changed = False
        for label in reversed(labels):
            in_old = live_in[label].copy()
            out_old = live_out[label].copy()
            succs = cfg[label]
            live_out[label] = set()
            for succ in succs:
                live_out[label].update(live_in[succ])
            live_in[label] = uses[label].union(live_out[label] - defines[label])
            if live_in[label] != in_old or live_out[label] != out_old:
                changed = True
    return live_in, live_out

def remove_dead_code(func):
    blocks = list(form_blocks(func['instrs']))
    cfg, labels = construct_cfg(blocks)
    live_in, live_out = liveness_analysis(blocks, cfg, labels)
    block_map = dict(zip(labels, blocks))
    for label in labels:
        block = block_map[label]
        live_vars = live_out[label].copy()
        updated_block = []
        for instr in reversed(block):
            if 'op' not in instr:
                updated_block.append(instr)
                continue
            dest = instr.get('dest')
            args = instr.get('args', [])
            if is_essential(instr) or (dest and dest in live_vars):
                updated_block.append(instr)
                if dest:
                    live_vars.discard(dest)
                live_vars.update(args)
            else:
                pass
        block[:] = reversed(updated_block)
    func['instrs'] = flatten([block_map[label] for label in labels])

def main():
    program = json.load(sys.stdin)
    for func in program['functions']:
        remove_dead_code(func)
    json.dump(program, sys.stdout, indent=2)

if __name__ == '__main__':
    main()
