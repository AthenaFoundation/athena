import sys
sys.path.append('/mnt/c/code/python')
from utils1 import *


def findNthOccurrence(s,pat,n):
    start = -1
    for _ in range(n):
        start = s.find(pat,start+1)
        if start == -1:
            return -1
    return start

def grabLines(L,i,N):
    j = i
    block = []
    while not(L[j].startswith("]]]]")) and j < N: 
        block.append(L[j])
        j += 1
    if j < N:
        block.append(L[j])
    return (block,j)

def getProofBlocks(L):
    i = 0
    N = len(L)
    blocks = []
    while (i < N):
        if L[i].startswith("[[[["):
            (block, j) = grabLines(L,i,N)
            blocks.append(block)
            i = j + 1
        else:
            i += 1
    return blocks 


def updateParenState(paren_state,c):
    if c == '(':
        paren_state['parens'] += 1
    elif c == '[':
        paren_state['brackets'] += 1
    elif c == '{':
        paren_state['braces'] += 1
    elif c == ')':
        paren_state['parens'] -= 1
    elif c == ']':
        paren_state['brackets'] -= 1
    elif c == '}':
        paren_state['braces'] -= 1
    else:
        pass

def checkBalance(text):
    paren_state = {'parens':0, 'brackets':0, 'braces':0}
    for c in text:
        updateParenState(paren_state,c)
    return paren_state

def balanced(paren_state):
    return paren_state['parens'] == 0 and paren_state['brackets'] == 0  and paren_state['braces'] == 0 

def balanceText(text,paren_state): 
    # It's assumed that the input paren_state is unbalanced. 
    N = len(text)
    i = 0
    res = ''
    while (i < N):
        c = text[i]
        res = res + c
        updateParenState(paren_state,c)
        #print("Inside the loop, i: " + str(i) + ", c: " + c + ", and paren_state: " + str(paren_state))
        if balanced(paren_state):
            return res
        else: 
            i += 1
    if balanced(paren_state):
        return res
    else: 
        print("UNABLE TO BALANCE REMAINDER!")
        raise Exception("UNABLE TO BALANCE REMAINDER!")

def getBalancedText(lines,start_pos,end_pos):
    '''
    lines:A string of lines representing the entire literal contents of the original source file for the proof of interest 
    start_pos: A pair of integers (line,pos), 0-indexed, representing the starting position (line and column number) for the proof or subproof of interest 
    end_pos: A pair of integers (line,pos), 0-indexed, representing the ending position (line and column number) for the proof or subproof of interest 
    Output: The text of the unique proof that starts at start_pos and ends either at end_pos or beyond. 
    '''
    (line1,pos1) = start_pos
    (line2,pos2) = end_pos
    subtract = len(lines[line2])-pos2
    span_text = ''.join(lines[line1:line2+1])[pos1:]
    span_text_clipped = span_text[:-subtract]
    remaining_text_starting_line = lines[line2][pos2:]
    all_remaining_lines = [remaining_text_starting_line] + lines[line2+1:]
    all_remaining_text = ''.join(all_remaining_lines)
    paren_state = checkBalance(span_text_clipped)
    if balanced(paren_state):
        return span_text_clipped
    else:
        return span_text_clipped + balanceText(all_remaining_text,paren_state)


def getSingleFidContent(single_fid_text):
    #print("\nWorking on this single fid entry: " + single_fid_text)
    s = single_fid_text
    chunks = [chunk.strip() for chunk in s.split(' || ')]
    # By convention, we must have exactly three ||-separated chunks: 
    assert len(chunks) == 3
    fid_name_literal, fid_type_literal, fid_value_literal = 'fidName:', 'fidType:', 'fidValue:'
    # Get name first: 
    fid_name = chunks[0][len(fid_name_literal):].strip()
    # Then get type: 
    fid_type = chunks[1][len(fid_type_literal):].strip()
    # And finally value: 
    fid_value = chunks[2][len(fid_value_literal):].strip()
    return {'fid_name': fid_name, 'fid_type': fid_type, 'fid_value': fid_value}

def getFidBlockInfo(fid_content):
    F = {}
    i = 0
    while (fid_content.find("fidName: ",i)) >= 0: 
        i = fid_content.find("fidName: ",i)
        next = fid_content.find("fidName: ",i + 1 + len('fidName: '))
        single_fid_text = fid_content[i:] if next < 0 else fid_content[i:next].strip()
        r = getSingleFidContent(single_fid_text)
        F[r['fid_name']] = {'fid_type': r['fid_type'], 'fid_value': r['fid_value']}
        i = next 
    return F

def getRange(text): 
    line_index_1 = findNthOccurrence(text,':',2)
    pos_index_1 = text.find(':',line_index_1+1)
    starting_line = int(text[line_index_1+1:pos_index_1].strip())
    pos_1_end = text.find("and ending at: ") 
    if pos_1_end < 0:
        pos_1_end = len(text)
    starting_pos = int(text[pos_index_1+1:pos_1_end].strip())
    return (starting_line,starting_pos)

def subproofStartingAndEndingPositions(subproof_chunk): 
    (starting_line,starting_pos) = getRange(subproof_chunk)
    pat = " and ending at: "
    pos_1_end = subproof_chunk.find(pat)
    rem_text = subproof_chunk[pos_1_end+4:subproof_chunk.find('\n')]
    (ending_line,ending_pos) = getRange(rem_text)
    return ((starting_line-1,starting_pos-1), (ending_line-1,ending_pos-1))

def getSubproofs(subproof_content,source_file,all_source_file_lines): 
    chunks = [chunk.strip() for chunk in subproof_content.split("||\n")]
    R = []
    for chunk in chunks:
        (subproof_starting_pos,subproof_ending_pos) = subproofStartingAndEndingPositions(chunk)
        subproof_text = getBalancedText(all_source_file_lines,subproof_starting_pos,subproof_ending_pos)
        R.append({'subproof_text': subproof_text, 'file': source_file, 'starting_pos': {'line': subproof_starting_pos[0], 'col': subproof_starting_pos[1]}, 'ending_pos': {'line': subproof_ending_pos[0], 'col': subproof_ending_pos[1]}})
    return R 

def processFsymChunk(chunk,D,file_name,all_source_file_lines):
    toks = [t.strip() for t in chunk.split(" || ")]
    assert (len(toks) == 3)
    sym_name = getSymbolName(toks[0])
    sym_type = getSymbolType(toks[1])
    sym_signature = getSignate
    if sym_type == 'constructor':
        getStructureDefs(toks[2])
    else:
        
    
def processFsymContent(fsym_content,file_name,all_source_file_lines):
    chunks = [chunk.strip() for chunk in fsym_content.split("||\n")]
    D = {}
    for chunk in chunks:    
        processFsymChunk(chunk,D,file_name,all_source_file_lines)
    return D

def analyzeBlock(block):
    '''
    This function takes a proof block and extracts the proof and the proof's metadata from it. The input block is just a list of lines,
    and the output is a dictionary of this form:
    {'proof_text':  <the text of the proof>,
     'file':        <the file of the proof>,
     'start_pos':   <the starting position>,
     'end_pos':     <the ending position>,
     'conclusion':  <the conclusion of the proof, pretty-formatted>,
     'subproofs':   <a list of all the subdeductions, each represented as a dictionary with at least one field: 'subproof_text'>
     'free-ids':    <a dictionary mapping each free-identifier name in the proof to a dictionary of the form {'fid_type': ..., 'fid_value': ...}> 
     'fun-syms':    <a dictionary mapping each function-symbol name that appears in the proof to its signature>,
     'structures':  <a list of all the relevant structure definitions. Each structure contains its file, start and end pos, and the text of the definition>,
     'domains':     <a list of all non-structure domains that appear in the signatures of 'fun-syms'
    ''' 
    text = ''.join(block)
    header_line = block[1]
    assert header_line.startswith('qqq')
    file_start_pos = header_line.find('position: ') + 10
    file_end_pos = header_line.find(':',file_start_pos)
    file_name = header_line[file_start_pos:file_end_pos]
    line_start_pos = file_end_pos+1
    column_start_pos = header_line.find(':',line_start_pos)+1
    diff = column_start_pos - line_start_pos - 1 
    line_number = header_line[line_start_pos:line_start_pos+diff]
    col_number = header_line[column_start_pos:].strip()
    proof_starting_position = {'line': int(line_number)-1, 'col': int(col_number)-1}
    second_line = block[2]
    i = findNthOccurrence(second_line,':',3)
    proof_end_line = int(second_line[1+findNthOccurrence(second_line,':',2):i])-1
    proof_end_pos = int(second_line[i+1:].strip())-1
    all_source_file_lines = getTotallyLiteralLines(file_name)
    proof_text = getBalancedText(all_source_file_lines,(proof_starting_position['line'],proof_starting_position['pos']),(proof_end_line,proof_end_pos))    
    lines_in_proof_text = proof_text.count('\n')
    last_eol_pos = proof_text.rstrip().rfind('\n')
    last_eol_pos = 0 if last_eol_pos < 0 else last_eol_pos
    last_chunk = proof_text[1+last_eol_pos:].rstrip()
    proof_ending_position = {'line': proof_starting_position['line']+lines_in_proof_text-1,'col': len(last_chunk)-1}
    # So far: proof_text, file_name,proof_starting_position, proof_ending_position 
    conclusion_pat = 'Conclusion:\n{{{'
    conclusion_pos = text.find(conclusion_pat)
    conclusion_start = conclusion_pos + len(conclusion_pat)
    conclusion_end = text.find('}}}',conclusion_start)
    conclusion_text = text[conclusion_start:conclusion_end].strip()
    #**** Free ids:
    fid_pat = 'Free id values and types:\n{{{'
    fid_start_pos = text.find(fid_pat)
    fid_end_pos = text.find("}}}",fid_start_pos+len(fid_pat))
    fid_content = text[fid_start_pos+len(fid_pat):fid_end_pos].strip()
    fid_dict = getFidBlockInfo(fid_content)
    #**** Subproofs: 
    subproof_pat = "All subdeductions:\n{{{"
    subproofs_start = text.find(subproof_pat)
    subproofs_end = text.find('}}}',subproofs_start+len(subproof_pat))
    subproof_content = text[subproofs_start+len(subproof_pat):subproofs_end].strip()
    subproof_list = sorted(getSubproofs(subproof_content,file_name,all_source_file_lines),key=lambda subproof: len(subproof['subproof_text']))
    #**** Function Symbols: 
    fsym_pat = "Function symbols:\n{{{"
    fsym_start_pos = text.find(fsym_pat)
    fsym_end_pos = text.find('}}}',fsym_start_pos+len(fsym_pat))
    fsym_content = text[fsym_start_pos+len(fsym_pat):fsym_end_pos].strip()
    fsym_dict = processFsymContent(fsym_content,file_name,all_source_file_lines)

def processFile(file):
    L = getTotallyLiteralLines(file) 
    blocks = getProofBlocks(L)
    return ''

file = 'chapter03.txt'


#L = getTotallyLiteralLines(file) 
#blocks = getProofBlocks(L)
#b = blocks[32]
#block = b
