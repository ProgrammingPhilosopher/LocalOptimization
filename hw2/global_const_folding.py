import sys
import json
from collections import namedtuple
from form_blocks import form_blocks

Analysis = namedtuple('Analysis', ['forward', 'init', 'merge', 'transfer'])

BOTTOM = '⊥'
TOP = 'top'

def merge_values(vals):
    vals = set(vals)
    if len(vals) == 1:
        return vals.pop()
    if BOTTOM in vals:
        vals.remove(BOTTOM)
    if len(vals) == 1:
        return vals.pop()
    return TOP

def transfer_function(block, in_vals):
    out_vals = in_vals.copy()
    for instr in block:
        if instr['op'] == 'const':
            out_vals[instr['dest']] = instr['value']
        elif 'args' in instr:
            args = instr['args']
            op = instr['op']
            if all(out_vals.get(arg) not in {BOTTOM, TOP} for arg in args):
                const_val = fold_constants(op, [out_vals[arg] for arg in args])
                if const_val is not None:
                    out_vals[instr['dest']] = const_val
                else:
                    out_vals[instr['dest']] = TOP
            else:
                out_vals[instr['dest']] = TOP

            if op == 'ptradd' and out_vals.get(args[1]) == 0:
                out_vals[instr['dest']] = out_vals[args[0]]
                
            if op == 'id' and out_vals.get(args[0]) is not BOTTOM:
                out_vals[instr['dest']] = out_vals[args[0]]
    return out_vals

def merge_function(pred_vals):
    """Merge constant information from multiple predecessor blocks."""
    merged = {}
    vars = set().union(*(vals.keys() for vals in pred_vals))
    for var in vars:
        var_vals = [vals.get(var, BOTTOM) for vals in pred_vals]
        merged[var] = merge_values(var_vals)
    return merged

def fold_constants(op, values):
    """Fold constants for supported operations."""
    ops = {
        'add': lambda a, b: a + b,
        'mul': lambda a, b: a * b,
        'sub': lambda a, b: a - b,
        'div': lambda a, b: a // b,
        'lt': lambda a, b: int(a < b),
        'gt': lambda a, b: int(a > b),
        'eq': lambda a, b: int(a == b),
        'le': lambda a, b: int(a <= b),
        'ge': lambda a, b: int(a >= b),
        'ne': lambda a, b: int(a != b),
        'and': lambda a, b: int(a and b),
        'or': lambda a, b: int(a or b),
        'not': lambda a: int(not a),
    }
    try:
        if op in ops:
            return ops[op](*values)
    except Exception:
        pass
    return None

def name_blocks(blocks):
    named_blocks = {}
    block_count = 0
    for block in blocks:
        if block and 'label' in block[0]:
            block_name = block[0]['label']
            block_instructions = block[1:]
        else:
            block_name = f'block{block_count}'
            block_count += 1
            block_instructions = block
        named_blocks[block_name] = block_instructions
    return named_blocks

def edges(blocks):
    preds = {name: [] for name in blocks}
    succs = {name: [] for name in blocks}
    block_names = list(blocks.keys())
    
    for i, (block_name, block_instrs) in enumerate(blocks.items()):
        if not block_instrs:
            continue
        last_instr = block_instrs[-1]
        
        if last_instr['op'] == 'jmp':
            target = last_instr['labels'][0]
            succs[block_name].append(target)
            preds[target].append(block_name)
            
        elif last_instr['op'] == 'br':
            target_true = last_instr['labels'][0]
            target_false = last_instr['labels'][1]
            succs[block_name].extend([target_true, target_false])
            preds[target_true].append(block_name)
            preds[target_false].append(block_name)
            
        elif last_instr['op'] == 'ret':
            pass
        
        else:
            if i + 1 < len(block_names):
                next_block = block_names[i + 1]
                succs[block_name].append(next_block)
                preds[next_block].append(block_name)
    
    return preds, succs

def reassemble(blocks):
    instrs = []
    for block_name, block_instrs in blocks.items():
        if not block_name.startswith('block'):
            instrs.append({'label': block_name})
        instrs.extend(block_instrs)
    return instrs

def df_worklist(blocks, analysis):
    preds, succs = edges(blocks)

    if analysis.forward:
        in_edges = preds
        out_edges = succs
    else:
        in_edges = succs
        out_edges = preds

    in_ = {block: analysis.init.copy() for block in blocks}
    out = {block: analysis.init.copy() for block in blocks}

    worklist = list(blocks.keys())

    while worklist:
        node = worklist.pop(0)
        pred_blocks = in_edges.get(node, [])
        if pred_blocks:
            merged_in = analysis.merge([out[pred] for pred in pred_blocks])
        else:
            merged_in = analysis.init.copy()

        if merged_in != in_[node]:
            in_[node] = merged_in
            out_val = analysis.transfer(blocks[node], merged_in)
            if out_val != out[node]:
                out[node] = out_val
                for succ in out_edges.get(node, []):
                    if succ not in worklist:
                        worklist.append(succ)
    return in_, out

def global_constant_propagation(blocks):
    named_blocks = name_blocks(blocks)

    vars = set()
    for block in named_blocks.values():
        for instr in block:
            if 'dest' in instr:
                vars.add(instr['dest'])
            if 'args' in instr:
                vars.update(instr['args'])

    init = {var: BOTTOM for var in vars}

    analysis = Analysis(
        forward=True,
        init=init,
        merge=merge_function,
        transfer=transfer_function
    )

    in_, out = df_worklist(named_blocks, analysis)

    for block_name, block in named_blocks.items():
        for instr in block:
            if 'args' in instr:
                args = instr['args']
                if all(out[block_name].get(arg) not in {BOTTOM, TOP} for arg in args):
                    op = instr['op']
                    const_val = fold_constants(op, [out[block_name][arg] for arg in args])
                    if const_val is not None:
                        instr['op'] = 'const'
                        instr['value'] = const_val
                        instr.pop('args', None)
    return named_blocks

def remove_redundant_instructions(blocks):
    for block in blocks.values():
        new_block = []
        for instr in block:
            if instr['op'] == 'id' and instr['args'][0] == instr['dest']:
                continue
            if instr['op'] == 'ptradd' and instr['args'][1] == 0:
                continue
            new_block.append(instr)
        block[:] = new_block
    return blocks

def lvn_program(bril):
    for func in bril['functions']:
        blocks = form_blocks(func['instrs'])
        optimized_blocks = global_constant_propagation(blocks)
        optimized_blocks = remove_redundant_instructions(optimized_blocks)
        func['instrs'] = reassemble(optimized_blocks)

if __name__ == '__main__':
    bril_program = json.load(sys.stdin)
    lvn_program(bril_program)
    json.dump(bril_program, sys.stdout, indent=2, sort_keys=True)
