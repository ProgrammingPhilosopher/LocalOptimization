"""Local value numbering for Bril.
"""
import json
import sys
import itertools
from collections import namedtuple

TERMINATORS = 'br', 'jmp', 'ret'
def form_blocks(instrs):
    """Given a list of Bril instructions, generate a sequence of
    instruction lists representing the basic blocks in the program.

    Every instruction in `instr` will show up in exactly one block. Jump
    and branch instructions may only appear at the end of a block, and
    control can transfer only to the top of a basic block---so labels
    can only appear at the *start* of a basic block. Basic blocks may
    not be empty.
    """

    # Start with an empty block.
    cur_block = []

    for instr in instrs:
        if 'op' in instr:  # It's an instruction.
            # Add the instruction to the currently-being-formed block.
            cur_block.append(instr)

            # If this is a terminator (branching instruction), it's the
            # last instruction in the block. Finish this block and
            # start a new one.
            if instr['op'] in TERMINATORS:
                yield cur_block
                cur_block = []

        else:  # It's a label.
            # End the block here (if it contains anything).
            if cur_block:
                yield cur_block

            # Start a new block with the label.
            cur_block = [instr]

    # Produce the final block, if any.
    if cur_block:
        yield cur_block

def flatten(ll):
    """Flatten an iterable of iterable to a single list.
    """
    return list(itertools.chain(*ll))

Value = namedtuple('Value', ['op', 'args'])

class Numberings:
    def __init__(self):
        self.var_to_num = {}
        self.val_to_num = {}
        self.num_to_const = {}
        self.next_num = 0

    def new_number(self):
        num = self.next_num
        self.next_num += 1
        return num
    
def canonicalize(value):
    if value.op in {'add', 'mul'}:
        return Value(value.op, tuple(sorted(value.args)))
    return value

def lvn_block(block):
    state = Numberings()
    for var in get_first_reads(block):
        num = state.new_number()
        state.var_to_num[var] = num

    new_block = []
    for instr in block:
        args = instr.get('args', [])
        arg_nums = [state.var_to_num[arg] for arg in args]
        if 'dest' in instr:
            dest = instr['dest']
            op = instr['op']
            if 'args' in instr and op != 'call':
                val = canonicalize(Value(op, tuple(arg_nums)))
                num = state.val_to_num.get(val)
                if num is not None:
                    state.var_to_num[dest] = num
                else:
                    num = state.new_number()
                    state.var_to_num[dest] = num
                    state.val_to_num[val] = num
                    const_val = fold_constants(state.num_to_const, val)
                    if const_val is not None:
                        state.num_to_const[num] = const_val
                        instr['op'] = 'const'
                        instr['value'] = const_val
                        instr.pop('args', None)
            else:
                num = state.new_number()
                state.var_to_num[dest] = num
                if op == 'const':
                    state.num_to_const[num] = instr['value']
        new_block.append(instr)
    block[:] = new_block

def get_first_reads(instrs):
    read_vars = set()
    written_vars = set()
    for instr in instrs:
        read_vars.update(set(instr.get('args', [])) - written_vars)
        if 'dest' in instr:
            written_vars.add(instr['dest'])
    return read_vars

def fold_constants(num_to_const, val):
    ops = {
        'add': lambda a, b: a + b,
        'mul': lambda a, b: a * b,
        'sub': lambda a, b: a - b,
        'div': lambda a, b: a // b,
        'gt':  lambda a, b: a > b,
        'lt':  lambda a, b: a < b,
        'ge':  lambda a, b: a >= b,
        'le':  lambda a, b: a <= b,
        'ne':  lambda a, b: a != b,
        'eq':  lambda a, b: a == b,
        'or':  lambda a, b: a or b,
        'and': lambda a, b: a and b,
        'not': lambda a: not a,
    }
    if val.op in ops:
        try:
            const_args = [num_to_const[arg_num] for arg_num in val.args]
            return ops[val.op](*const_args)
        except KeyError:
            return None
    return None

def lvn_program(bril):
    for func in bril['functions']:
        blocks = list(form_blocks(func['instrs']))
        for block in blocks:
            lvn_block(block)
        func['instrs'] = flatten(blocks)

if __name__ == '__main__':
    bril_program = json.load(sys.stdin)
    lvn_program(bril_program)
    json.dump(bril_program, sys.stdout, indent=2, sort_keys=True)