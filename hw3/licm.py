from copy import deepcopy
from collections import OrderedDict
import sys
import json

# Constants for loop invariance and loop preheader labeling
LOOP_INVARIANT = True
NOT_LOOP_INVARIANT = False

LOOP_PREHEADER_COUNTER = 0
NEW_LOOP_PREHEADER_BASE = "new.loop.preheader"

# Constants for instruction blocks
INSTRS = "instrs"
PREDS = "preds"
SUCCS = "succs"
ARGS = "args"
DEST = "dest"
LABELS = "labels"
TYPE = "type"
OP = "op"
VALUE = "value"
LABEL = "label"
FUNCS = "funcs"
NAME = "name"
INT = "int"
BOOL = "bool"
CONST = "const"
ADD = "add"
SUB = "sub"
MUL = "mul"
DIV = "div"
EQ = "eq"
LT = "lt"
GT = "gt"
LE = "le"
GE = "ge"
NOT = "not"
AND = "and"
OR = "or"
JMP = "jmp"
BR = "br"
CALL = "call"
RET = "ret"
ID = "id"
PRINT = "print"
NOP = "nop"
PHI = "phi"
BRIL_BINOPS = [
    ADD, SUB, MUL, DIV,
    EQ, LT, GT, LE, GE,
    AND, OR,
]
COMP_OPS = [LT, GT, LE, GE, EQ]
LOGIC_OPS = [NOT, AND, OR]
BOOL_OPS = [NOT, AND, OR, LT, GT, LE, GE, EQ]
INT_OPS = [ADD, SUB, MUL, DIV]
BRIL_UNOPS = [NOT]
BRIL_CORE_OPS = [*BRIL_BINOPS, *BRIL_UNOPS]
BRIL_CORE_INSTRS = [
    *BRIL_BINOPS, *BRIL_UNOPS,
    JMP, BR, CALL, RET,
    ID, PRINT, NOP, PHI, CONST,
]
BRIL_COMMUTE_BINOPS = [
    ADD, MUL, AND, OR, EQ
]
BRIL_CORE_TYPES = [
    INT, BOOL
]
TERMINATORS = [JMP, BR, RET]
OP_TO_TYPE = {**{b: BOOL for b in BOOL_OPS}, **{i: INT for i in INT_OPS}}
SIDE_EFFECT_OPS = [
    PRINT, DIV
]
NUM_BINARY_ARGS = 2
NUM_UNARY_ARGS = 1
ARGUMENT = "argument"
FUNCTIONS = "functions"
MAIN = "main"

def form_blocks(body):
    current_block = []

    for instruction in body:
        if "op" in instruction:
            current_block.append(instruction)
            if instruction["op"] in TERMINATORS:
                yield current_block
                current_block = []
        else:
            if current_block:
                yield current_block
            current_block = [instruction]

    if current_block:
        yield current_block

def form_block_dict(blocks):
    block_dict = OrderedDict()

    for index, block in enumerate(blocks):
        if 'label' in block[0]:
            block_name = block[0]['label']
        else:
            block_name = f'b{index}'
        block_dict[block_name] = block

    return block_dict

def get_cfg_w_blocks(block_name_to_block):
    cfg_with_successors = OrderedDict()

    for index, (block_name, block) in enumerate(block_name_to_block.items()):
        if block:
            last_instruction = block[-1]
            if 'op' in last_instruction and last_instruction['op'] in ['jmp', 'br']:
                successors = last_instruction['labels']
            elif 'op' in last_instruction and last_instruction['op'] == 'ret':
                successors = []
            else:
                if index == len(block_name_to_block) - 1:
                    successors = []
                else:
                    successors = [list(block_name_to_block.keys())[index + 1]]
            cfg_with_successors[block_name] = {INSTRS: block, SUCCS: successors, PREDS: []}
        else:
            if index == len(block_name_to_block) - 1:
                successors = []
            else:
                successors = [list(block_name_to_block.keys())[index + 1]]
            cfg_with_successors[block_name] = {INSTRS: block, SUCCS: successors, PREDS: []}

    cfg_with_predecessors = OrderedDict()
    for block_name in cfg_with_successors:
        predecessors = []
        for pred_block_name, block_data in cfg_with_successors.items():
            if block_name in block_data[SUCCS]:
                predecessors.append(pred_block_name)
        cfg_with_predecessors[block_name] = predecessors

    final_cfg = OrderedDict()
    for block_name, block_data in cfg_with_successors.items():
        final_cfg[block_name] = {
            INSTRS: block_data[INSTRS],
            PREDS: cfg_with_predecessors[block_name],
            SUCCS: block_data[SUCCS]
        }

    return final_cfg

def form_cfg_w_blocks(func):
    return get_cfg_w_blocks(form_block_dict(form_blocks(func['instrs'])))

def join_cfg(cfg):
    assert isinstance(cfg, OrderedDict)

    combined_instructions = []

    for label, block_data in cfg.items():
        block_instructions = block_data[INSTRS]
        if block_instructions and 'label' not in block_instructions[0]:
            combined_instructions.append({'label': label})
        elif not block_instructions:
            combined_instructions.append({'label': label})

        for instruction in block_instructions:
            combined_instructions.append(instruction)

    return combined_instructions

def get_cfg(block_name_to_block):
    cfg_successors = OrderedDict()

    for index, (block_name, block) in enumerate(block_name_to_block.items()):
        if block:
            last_instruction = block[-1]
            if 'op' in last_instruction and last_instruction['op'] in ['jmp', 'br']:
                successors = last_instruction['labels']
            elif 'op' in last_instruction and last_instruction['op'] == 'ret':
                successors = []
            else:
                if index == len(block_name_to_block) - 1:
                    successors = []
                else:
                    successors = [list(block_name_to_block.keys())[index + 1]]
            cfg_successors[block_name] = successors
        else:
            if index == len(block_name_to_block) - 1:
                successors = []
            else:
                successors = [list(block_name_to_block.keys())[index + 1]]
            cfg_successors[block_name] = successors

    return cfg_successors

def block_map(blocks):
    block_mapping = OrderedDict()

    for index, block in enumerate(blocks):
        if 'label' in block[0]:
            block_name = block[0]['label']
            block = block[1:]
        else:
            block_name = f'b{index}'
        block_mapping[block_name] = block

    return block_mapping

def form_cfg(function):
    return get_cfg(block_map(form_blocks(function['instrs'])))

def form_cfg_succs_preds(function_body):
    assert isinstance(function_body, list)

    # Form blocks and map block names to blocks
    basic_blocks = form_blocks(function_body)
    block_name_to_block = form_block_dict(basic_blocks)

    # Get CFG with successors
    cfg_successors = get_cfg(block_name_to_block)

    # Build predecessor CFG by analyzing successors
    cfg_predecessors = OrderedDict()
    for block_name in cfg_successors:
        predecessors = []
        for other_block_name, successors in cfg_successors.items():
            if block_name in successors:
                predecessors.append(other_block_name)
        cfg_predecessors[block_name] = predecessors

    # Combine successors and predecessors into a single CFG representation
    cfg = OrderedDict()
    for block_name in cfg_successors:
        cfg[block_name] = {PREDS: cfg_predecessors[block_name], SUCCS: cfg_successors[block_name]}

    return cfg

def get_predecessors(block_name, cfg):
    predecessors = set()
    for other_block_name, successors in cfg.items():
        if block_name in successors:
            predecessors.add(other_block_name)
    return list(predecessors)

def solve_worklist(entry, cfg, blocks, init, merge, transfer):
    in_dict = OrderedDict()
    for name in blocks:
        in_dict[name] = init if name == entry else set()

    out_dict = OrderedDict()
    for name in blocks:
        out_dict[name] = init

    worklist = [(name, blocks[name]) for name in blocks]

    while worklist:
        block_name, block = worklist.pop()

        # Get predecessors and their corresponding outputs
        pred_names = get_predecessors(block_name, cfg)
        predecessors = [out_dict[name] for name in pred_names if name in out_dict]

        # For the entry block, we check if the init is non-empty
        if not predecessors and in_dict[entry]:
            predecessors.append(in_dict[entry])

        # Merge inputs from predecessors
        in_b = merge(predecessors)
        in_dict[block_name] = in_b

        # Transfer function to compute new outputs
        new_out_b = transfer(in_b, block)
        old_out_b = out_dict[block_name]

        if new_out_b != old_out_b:
            successor_names = cfg[block_name]
            successors = [(succ_name, blocks[succ_name]) for succ_name in successor_names if succ_name in blocks]
            worklist += successors

        out_dict[block_name] = new_out_b

    return in_dict, out_dict

def solve_worklist_backwards(entry, cfg, blocks, init, merge, transfer):
    out_dict = OrderedDict()
    for name in blocks:
        out_dict[name] = init if name == entry else set()

    in_dict = OrderedDict()
    for name in blocks:
        in_dict[name] = init

    worklist = [(name, blocks[name]) for name in blocks]

    while worklist:
        block_name, block = worklist.pop()

        # Get successors and their corresponding inputs
        succ_names = cfg[block_name]
        successors = [in_dict[name] for name in succ_names if name in in_dict]

        # For the entry block, we check if the init is non-empty
        if not successors and out_dict[entry]:
            successors.append(out_dict[entry])

        # Merge inputs from successors
        out_b = merge(successors)
        out_dict[block_name] = out_b

        # Transfer function to compute new inputs
        new_in_b = transfer(out_b, block)
        old_in_b = in_dict[block_name]

        if new_in_b != old_in_b:
            predecessor_names = get_predecessors(block_name, cfg)
            predecessors = [(pred_name, blocks[pred_name]) for pred_name in predecessor_names if pred_name in blocks]
            worklist += predecessors

        in_dict[block_name] = new_in_b

    return in_dict, out_dict

def number_instrs(blocks):
    i = 1
    new_blocks = {}
    for key, block in blocks.items():
        new_block = []
        for instr in block:
            new_block.append((i, instr))
            i += 1
        new_blocks[key] = new_block
    return new_blocks

def diff(in_block, kills):
    final = set()
    for (i1, var1) in in_block:
        killed = any(var1 == var2 for _, var2 in kills)
        if not killed:
            final.add((i1, var1))
    return final

def kills(block):
    kill_set = set()
    for i, instr in block:
        if DEST in instr:
            kill_set.add((i, instr[DEST]))
    return kill_set

def defs(block):
    last_assignment = {}
    for idx, instr in block:
        if DEST in instr:
            last_assignment[instr[DEST]] = idx

    return {(idx, dst) for dst, idx in last_assignment.items()}

def merge(blocks):
    merged_set = set()
    for block in blocks:
        merged_set.update(block)
    return merged_set

def transfer(in_block, block):
    return defs(block).union(diff(in_block, kills(block)))

def reaching_defs_func(function):
    cfg = form_cfg(function)
    assert cfg
    entry = list(cfg.keys())[0]
    blocks = number_instrs(form_block_dict(form_blocks(function["instrs"])))
    init = set()
    if ARGS in function:
        args = function[ARGS]
        init.update((-i, arg[NAME]) for i, arg in enumerate(args, 1))
    return solve_worklist(entry, cfg, blocks, init, merge, transfer)

def has_side_effects(instr):
    return OP in instr and instr[OP] in SIDE_EFFECT_OPS

def is_label(instr):
    assert type(instr) == dict
    return LABEL in instr

def is_jmp(instr):
    assert type(instr) == dict
    return OP in instr and instr[OP] == JMP

def is_br(instr):
    assert type(instr) == dict
    return OP in instr and instr[OP] == BR

# Utility function used to compute the intersection of sets in a list
def big_intersection(sets_list):
    assert isinstance(sets_list, list)
    if not sets_list:
        return set()
    
    result = sets_list[0]
    assert isinstance(result, set)

    for s in sets_list:
        result = result.intersection(s)
    
    return result

# Helper function for depth-first search
def dfs(cfg, current_block, visited_blocks):
    visited_blocks.add(current_block)
    for successor in cfg[current_block][SUCCS]:
        if successor not in visited_blocks:
            visited_blocks.update(dfs(cfg, successor, visited_blocks))
    return visited_blocks

# Core function to calculate dominators and dominance tree
def get_dominators_helper(cfg, entry_block=None):
    if entry_block is None:
        entry_block = list(cfg.keys())[0]
    
    dominators_by = OrderedDict()
    reachable_blocks = set()
    
    if len(cfg) >= 1:
        reachable_blocks = dfs(cfg, entry_block, set())
    
    for block_name in cfg:
        if block_name == entry_block:
            dominators_by[block_name] = {block_name}
        elif block_name in reachable_blocks:
            dominators_by[block_name] = reachable_blocks
    
    dominators_changed = True
    while dominators_changed:
        old_dominators = deepcopy(dominators_by)
        
        for block_name in [name for name in cfg if name in reachable_blocks]:
            predecessors_dominators = [dominators_by[p] for p in cfg[block_name][PREDS] if p in reachable_blocks]
            
            if block_name == entry_block:
                continue
            
            intersection_result = big_intersection(predecessors_dominators)
            dominators_by[block_name] = {block_name}.union(intersection_result)
        
        dominators_changed = old_dominators != dominators_by
    
    for node in cfg:
        if node not in reachable_blocks:
            dominators_by[node] = {entry_block}
    
    dominators = OrderedDict()
    for block in cfg:
        dominates = {other_block for other_block, dominated_by in dominators_by.items() if block in dominated_by}
        dominators[block] = list(dominates)
    
    return dominators, dominators_by

# Function to calculate dominators for a given function
def get_dominators(func):
    function_instructions = func["instrs"]
    cfg = form_cfg_succs_preds(function_instructions)
    return get_dominators_helper(cfg)

# Function to compute strict dominators
def get_strict_dominators(dominators):
    strict_dominators = OrderedDict()
    
    for block_name, doms in dominators.items():
        strict_dominators[block_name] = list(set(doms) - {block_name})
    
    return strict_dominators

# Function to compute immediate dominators from strict dominators
def get_immediate_dominators(strict_dominators):
    immediate_dominators = OrderedDict()
    
    for block, block_strict_doms in strict_dominators.items():
        immediate = []
        
        for dom_candidate in block_strict_doms:
            can_add = True
            for other_dom in block_strict_doms:
                if dom_candidate != other_dom and dom_candidate in strict_dominators[other_dom]:
                    can_add = False
                    break
            if can_add:
                immediate.append(dom_candidate)
        
        if immediate:
            assert len(immediate) == 1
            immediate_dominators[block] = immediate[0]
        else:
            immediate_dominators[block] = block
    
    return immediate_dominators

# Helper function to build the dominance tree
def build_dominance_tree_helper(dominators_by):
    strict_dominators = get_strict_dominators(dominators_by)
    immediate_dominators = get_immediate_dominators(strict_dominators)

    dominance_tree = OrderedDict()
    nodes = OrderedDict()

    for block, immediate_dom in immediate_dominators.items():
        nodes[block] = None
        
        if block != immediate_dom:
            if immediate_dom not in dominance_tree:
                dominance_tree[immediate_dom] = [block]
            else:
                dominance_tree[immediate_dom].append(block)
        
        if block not in dominance_tree:
            dominance_tree[block] = []

    return dominance_tree, nodes

# Function to build the dominance tree from a function
def build_dominance_tree(func):
    _, dominators_by = get_dominators(func)
    return build_dominance_tree_helper(dominators_by)

# Helper function to find back edges in the CFG
def get_backedges_helper(cfg, dominators):
    backedges = []
    
    for block_A in cfg:
        for block_B in cfg:
            if block_B in cfg[block_A][SUCCS] and block_A in dominators[block_B]:
                backedges.append((block_A, block_B))
    
    return backedges

# Function to find back edges in a function
def get_backedges(func):
    function_instructions = func["instrs"]
    cfg = form_cfg_succs_preds(function_instructions)
    dominators, _ = get_dominators(func)
    return get_backedges_helper(cfg, dominators)

# Function to find natural loops in a function
def get_natural_loops(func):
    function_instructions = func["instrs"]
    cfg = form_cfg_succs_preds(function_instructions)
    backedges = get_backedges(func)
    loops = []
    
    for (A, B) in backedges:
        natural_loop = [A, B]
        continue_expanding = True
        
        while continue_expanding:
            expanded_loop = deepcopy(natural_loop)
            
            for node in natural_loop:
                if node != B:
                    for predecessor in cfg[node][PREDS]:
                        if predecessor not in natural_loop:
                            expanded_loop.append(predecessor)
            
            if expanded_loop == natural_loop:
                continue_expanding = False
            natural_loop = expanded_loop
        
        is_valid_loop = True
        for node in [n for n in cfg if n not in natural_loop]:
            for successor in cfg[node][SUCCS]:
                if successor != B and successor in natural_loop:
                    is_valid_loop = False
        
        if is_valid_loop:
            exits = []
            for node in natural_loop:
                for successor in cfg[node][SUCCS]:
                    if successor not in natural_loop:
                        exits.append((node, successor))
            
            header = B
            loops.append((natural_loop, (A, B), header, exits))
    
    return loops

# Helper function to generate unique loop preheaders
def gen_loop_preheader():
    global LOOP_PREHEADER_COUNTER
    LOOP_PREHEADER_COUNTER += 1
    return f"{NEW_LOOP_PREHEADER_BASE}.{LOOP_PREHEADER_COUNTER}"

# Function to insert loop preheaders into natural loops
def insert_preheaders(natural_loops, instrs_w_blocks):
    headers = set()
    preheadermap = OrderedDict()
    backedgemap = OrderedDict()
    preheaders = set()

    # Build the backedgemap to track back edges in the natural loops
    for _, (backedge_src, _), header, _ in natural_loops:
        backedgemap.setdefault(header, []).append(backedge_src)

    new_instrs = []

    # Process instructions and insert preheaders
    for instr, instr_block in instrs_w_blocks:
        if is_label(instr):
            for loop_blocks, _, header, _ in natural_loops:
                if header == instr[LABEL] and header not in headers:
                    headers.add(header)
                    preheader = gen_loop_preheader()
                    preheaders.add(preheader)
                    preheadermap[header] = preheader

                    new_preheader_instr = {LABEL: preheader}

                    # Update branch/jump instructions in current and new instruction sets
                    for (inner_instr, block) in instrs_w_blocks + new_instrs:
                        if (is_br(inner_instr) or is_jmp(inner_instr)) and block not in loop_blocks:
                            if header in inner_instr[LABELS]:
                                inner_instr[LABELS] = [
                                    preheader if label == header else label for label in inner_instr[LABELS]
                                ]

                    new_instrs.append((new_preheader_instr, preheader))
        new_instrs.append((instr, instr_block))

    # Return the preheader map and final instructions list
    return preheadermap, [instr for instr, _ in new_instrs]


def identify_li_recursive(cfg, reaching_definitions, function_arguments, loop_blocks, current_block, instruction_invariant_map, variable_invariant_map):
    in_dict, _ = reaching_definitions

    # Iterate over each block in the loop
    for loop_block in loop_blocks:
        instructions = cfg[loop_block][INSTRS]

        # Process each instruction in the block
        for instruction in instructions:

            # Case 1: Check for constant assignment (no arguments)
            if VALUE in instruction and DEST in instruction:
                destination = instruction[DEST]
                is_constant_loop_invariant = True

                # Check if the constant is defined more than once within the loop
                for other_block in loop_blocks:
                    for other_instruction in cfg[other_block][INSTRS]:
                        if DEST in other_instruction and id(instruction) != id(other_instruction):
                            if other_instruction[DEST] == destination:
                                is_constant_loop_invariant = False

                # Update the invariance maps based on the check result
                if is_constant_loop_invariant:
                    instruction_invariant_map[id(instruction)] = LOOP_INVARIANT
                    variable_invariant_map[destination] = LOOP_INVARIANT
                else:
                    instruction_invariant_map[id(instruction)] = NOT_LOOP_INVARIANT
                    variable_invariant_map[destination] = NOT_LOOP_INVARIANT

            # Case 2: Instructions with arguments
            elif ARGS in instruction and DEST in instruction:
                arguments = instruction[ARGS]
                destination = instruction[DEST]
                is_argument_loop_invariant = True

                # Condition 1: Argument must be defined outside the loop
                for argument in arguments:
                    argument_defined_outside_loop = True

                    for block in cfg:
                        for _, variable in in_dict[block]:
                            if variable == destination and block in loop_blocks:
                                argument_defined_outside_loop = False
                                break
                        if not argument_defined_outside_loop:
                            break

                    if argument_defined_outside_loop:
                        continue

                    # Condition 2: Argument is defined exactly once in the function and marked as loop-invariant
                    definition_count = 0

                    # Check for definitions in function arguments
                    for function_argument in function_arguments:
                        if function_argument == destination:
                            definition_count += 1

                    # Check for definitions in the instructions
                    for defined_instruction in instructions:
                        if DEST in defined_instruction:
                            defined_destination = defined_instruction[DEST]
                            if defined_destination == destination:
                                definition_count += 1

                    if definition_count != 1 or (argument in variable_invariant_map and not variable_invariant_map[argument]):
                        is_argument_loop_invariant = False
                        break

                # Update the invariance maps based on the check result
                if is_argument_loop_invariant:
                    instruction_invariant_map[id(instruction)] = LOOP_INVARIANT
                    variable_invariant_map[destination] = LOOP_INVARIANT
                else:
                    instruction_invariant_map[id(instruction)] = NOT_LOOP_INVARIANT
                    variable_invariant_map[destination] = NOT_LOOP_INVARIANT

            # Default case: Mark as not loop-invariant
            else:
                instruction_invariant_map[id(instruction)] = NOT_LOOP_INVARIANT

    return instruction_invariant_map, variable_invariant_map


def identify_loop_invariant_instrs(cfg, function_arguments, loop_blocks, loop_instructions, loop_header, reaching_definitions):
    # Ensure the loop header is part of the loop blocks
    assert loop_header in loop_blocks

    # Initialize the instruction invariant map, marking all instructions as not loop invariant
    instruction_invariant_map = OrderedDict()
    for loop_instruction, _ in loop_instructions:
        instruction_invariant_map[id(loop_instruction)] = NOT_LOOP_INVARIANT

    continue_analysis = True

    # Repeat the analysis until the instructions remain unchanged
    while continue_analysis:
        # Make a deep copy of the loop instructions to compare later
        previous_loop_instructions = deepcopy(loop_instructions)

        # Initialize the variable invariant map
        variable_invariant_map = OrderedDict()
        for loop_instruction, _ in loop_instructions:
            if DEST in loop_instruction:
                destination_variable = loop_instruction[DEST]
                variable_invariant_map[destination_variable] = NOT_LOOP_INVARIANT

        # Call the recursive function to identify loop-invariant instructions
        instruction_invariant_map, variable_invariant_map = identify_li_recursive(
            cfg,
            reaching_definitions,
            function_arguments,
            loop_blocks,
            loop_header,
            instruction_invariant_map,
            variable_invariant_map
        )

        # If the loop instructions are unchanged, stop the analysis
        if loop_instructions == previous_loop_instructions:
            continue_analysis = False

    return instruction_invariant_map, variable_invariant_map


def gather_nodes(node, dominator_tree, natural_loop_nodes):
    gathered_nodes = [node]

    # Recursively gather child nodes that belong to the natural loop
    for child in dominator_tree[node]:
        if child in natural_loop_nodes:
            gathered_nodes += gather_nodes(child, dominator_tree, natural_loop_nodes)

    return gathered_nodes


def filter_loop_invariant_instrs(cfg, natural_loop, dominator_tree, loop_instructions, loop_instruction_map, id_to_instruction):
    natural_loop_nodes, _, header, exits = natural_loop

    # Filter for instructions marked as loop invariant
    invariant_instructions = []
    for identifier, status in loop_instruction_map.items():
        if status:
            invariant_instructions.append(identifier)

    # Check that the instruction dominates all its uses within the loop
    dominate_filter = []
    for identifier in invariant_instructions:
        defining_instruction, defining_block = id_to_instruction[identifier]
        destination_variable = defining_instruction[DEST]

        # Find the position of the instruction within the block
        position = None
        for i, instruction in enumerate(cfg[defining_block][INSTRS]):
            if id(instruction) == identifier:
                position = i
                break
        assert position is not None

        # Check within the block to ensure the instruction dominates all its uses
        dominates_within_block = True
        for i, instruction in enumerate(cfg[defining_block][INSTRS]):
            if ARGS in instruction and destination_variable in instruction[ARGS]:
                if i < position:
                    dominates_within_block = False
                    break

        # Accumulate all blocks dominated by the current instruction
        dominated_blocks = set(gather_nodes(defining_block, dominator_tree, natural_loop_nodes))
        all_dominated_blocks_in_loop = set(gather_nodes(header, dominator_tree, natural_loop_nodes))
        non_dominated_blocks = all_dominated_blocks_in_loop.difference(dominated_blocks)

        # Check if the instruction dominates all blocks in the loop where it is used
        for block in non_dominated_blocks:
            for instruction in cfg[block][INSTRS]:
                if ARGS in instruction and destination_variable in instruction[ARGS]:
                    dominates_within_block = False
                    break

        if dominates_within_block:
            dominate_filter.append(identifier)

    # Filter out instructions that have multiple definitions within the loop
    definition_filter = []
    for identifier in dominate_filter:
        defining_instruction, _ = id_to_instruction[identifier]
        destination_variable = defining_instruction[DEST]

        definition_count = 0
        for instruction, _ in loop_instructions:
            if DEST in instruction and instruction[DEST] == destination_variable:
                definition_count += 1

        if definition_count <= 1:
            definition_filter.append(identifier)

    # Ensure that the instruction dominates all exit blocks
    exit_filter = []
    for identifier in definition_filter:
        defining_instruction, defining_block = id_to_instruction[identifier]

        # Gather all blocks dominated by the defining block
        dominated_blocks = set(gather_nodes(defining_block, dominator_tree, natural_loop_nodes))

        # Check if the instruction dominates all exit nodes
        dominates_exits = True
        for exit_block, _ in exits:
            if exit_block not in dominated_blocks:
                dominates_exits = False

        # Check if the variable is used after the loop and has no side effects
        used_after_loop = False
        for after_block in cfg:
            if after_block not in natural_loop_nodes:
                for after_instruction in cfg[after_block][INSTRS]:
                    if ARGS in after_instruction and DEST in defining_instruction:
                        if defining_instruction[DEST] in after_instruction[ARGS]:
                            used_after_loop = True

        has_no_side_effects = not has_side_effects(defining_instruction)

        # Allow the instruction to exit if it has no side effects and is not used after the loop
        if not used_after_loop and has_no_side_effects:
            dominates_exits = True

        if dominates_exits:
            exit_filter.append(identifier)

    return exit_filter


def insert_into_bb(cfg, basic_block, instr):
    instrs = cfg[basic_block][INSTRS]
    if len(instrs) > 0 and OP in instrs[-1] and instrs[-1][OP] in TERMINATORS:
        instrs.insert(-1, instr)
        cfg[basic_block][INSTRS] = instrs
    else:
        cfg[basic_block][INSTRS].append(instr)


def remove_from_bb(cfg, basic_block, identifier):
    new_instrs = []
    for instr in cfg[basic_block][INSTRS]:
        if id(instr) != identifier:
            new_instrs.append(instr)
    cfg[basic_block][INSTRS] = new_instrs


def recursively_move_instructions(cfg, loop_header, preheader_map, instructions_to_move, target_variable, id_to_instruction, variables_inside_loop, moved_variables):
    matching_identifier = None

    # Find the identifier matching the target variable
    for current_identifier in instructions_to_move:
        instruction, _ = id_to_instruction[current_identifier]
        destination_variable = instruction[DEST]
        if destination_variable == target_variable:
            matching_identifier = current_identifier

    if matching_identifier is None:
        return False

    # Get the matching instruction and its block
    instruction_to_move, instruction_block = id_to_instruction[matching_identifier]
    destination_variable = instruction_to_move[DEST]

    # Recursively move the instruction's arguments if they are inside the loop and not already moved
    if ARGS in instruction_to_move:
        for argument in instruction_to_move[ARGS]:
            if argument not in moved_variables and argument in variables_inside_loop:
                result = recursively_move_instructions(
                    cfg, loop_header, preheader_map, instructions_to_move, argument, id_to_instruction, variables_inside_loop, moved_variables
                )
                if not result:
                    return False

    # Move the instruction to the loop preheader
    preheader_block = preheader_map[loop_header]
    insert_into_bb(cfg, preheader_block, instruction_to_move)
    remove_from_bb(cfg, instruction_block, matching_identifier)

    # Mark the destination variable as moved
    moved_variables.add(destination_variable)
    return True

def move_instructions(cfg, loop_header, preheader_map, instructions_to_move, id_to_instruction, variables_inside_loop, moved_variables):
    for identifier in instructions_to_move:
        instruction, basic_block = id_to_instruction[identifier]

        skip_instruction = False

        # Check if the instruction has arguments and move them recursively if needed
        if ARGS in instruction:
            for argument in instruction[ARGS]:
                if argument not in moved_variables and argument in variables_inside_loop:
                    result = recursively_move_instructions(
                        cfg, loop_header, preheader_map, instructions_to_move, argument, id_to_instruction, variables_inside_loop, moved_variables
                    )
                    if not result:
                        skip_instruction = True

        if skip_instruction:
            continue

        destination_variable = instruction[DEST]

        # If the destination variable is already moved, skip it
        if destination_variable in moved_variables:
            continue

        # Move the instruction to the preheader
        preheader_block = preheader_map[loop_header]
        insert_into_bb(cfg, preheader_block, instruction)
        remove_from_bb(cfg, basic_block, identifier)

        # Mark the destination variable as moved
        moved_variables.add(destination_variable)

    return

def loop_licm(natural_loop, cfg, function_arguments, preheader_map, reaching_definitions, dominance_tree):
    # Gather all instructions in the loop
    loop_blocks, _, loop_header, _ = natural_loop
    loop_instructions = []
    variables_inside_loop = set()

    for block_name in cfg:
        if block_name in loop_blocks:
            for instruction in cfg[block_name][INSTRS]:
                loop_instructions.append((instruction, block_name))
                if DEST in instruction:
                    variables_inside_loop.add(instruction[DEST])

    # Identify loop-invariant instructions
    loop_instructions_map, _ = identify_loop_invariant_instrs(
        cfg, function_arguments, loop_blocks, loop_instructions, loop_header, reaching_definitions
    )

    # Build a map from instruction ID to the actual instruction
    id_to_instruction = OrderedDict()
    for identifier in loop_instructions_map:
        for instruction, block_name in loop_instructions:
            if id(instruction) == identifier:
                id_to_instruction[identifier] = (instruction, block_name)

    # Filter the loop-invariant instructions
    instructions_to_move = filter_loop_invariant_instrs(
        cfg, natural_loop, dominance_tree, loop_instructions, loop_instructions_map, id_to_instruction
    )

    # Move the instructions
    move_instructions(
        cfg, loop_header, preheader_map, instructions_to_move,
        id_to_instruction, variables_inside_loop, set()
    )

    return cfg

def func_licm(function):
    natural_loops = get_natural_loops(function)
    old_cfg = form_cfg_w_blocks(function)
    
    instructions_with_blocks = []
    for block in old_cfg:
        for instruction in old_cfg[block][INSTRS]:
            instructions_with_blocks.append((instruction, block))

    # Insert preheaders
    preheader_map, new_instructions = insert_preheaders(natural_loops, instructions_with_blocks)
    function[INSTRS] = new_instructions

    # Rebuild the control flow graph
    cfg = form_cfg_w_blocks(function)

    # Perform reaching definitions and dominance analysis
    reaching_definitions = reaching_defs_func(function)
    dominance_tree, _ = build_dominance_tree(function)

    # Gather function arguments
    function_arguments = []
    if ARGS in function:
        for argument in function[ARGS]:
            function_arguments.append(argument[NAME])

    # Apply loop invariant code motion for each natural loop
    for natural_loop in natural_loops:
        cfg = loop_licm(natural_loop, cfg, function_arguments, preheader_map, reaching_definitions, dominance_tree)

    return join_cfg(cfg)


def licm_program(program):
    for func in program["functions"]:
        modified_func_instrs = func_licm(func)
        func["instrs"] = modified_func_instrs
    return program


def main():
    prog = json.load(sys.stdin)
    final_prog = licm_program(prog)
    json.dump(final_prog, sys.stdout, indent=2)


if __name__ == "__main__":
    main()