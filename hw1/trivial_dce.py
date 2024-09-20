import json
import sys
import itertools
from collections import namedtuple

# Instructions that terminate a basic block.
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

def trivial_dce_pass(func):
    blocks = list(form_blocks(func["instrs"]))

    used_vars = set()
    
    for block in blocks:
        for instr in block:
            if "args" in instr:
                used_vars.update(instr["args"])

    modified = False

    for block in blocks:
        filtered_block = [instr for instr in block if 'dest' not in instr or instr['dest'] in used_vars]

        if len(filtered_block) != len(block):
            modified = True

        block[:] = filtered_block

    func["instrs"] = flatten(blocks)
    
    return modified

def trivial_dce(func):
    while trivial_dce_pass(func):
        pass

if __name__ == "__main__":
    import json
    import sys

    program = json.load(sys.stdin)

    for function in program["functions"]:
        trivial_dce(function)

    json.dump(program, sys.stdout, indent=2, sort_keys=True)
