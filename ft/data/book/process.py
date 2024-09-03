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

def getText(lines,start,end):
    (line1,pos1) = start
    (line2,pos2) = end
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

def analyzeBlock(block):
    '''
    This function takes a proof block and extracts the proof and the proof's metadata from it. The input block is just a list of lines,
    and the output is a dictionary of this form:
    {'proof': <the text of the proof>,
     'file':  <the file of the proof>,
     'start_pos': <the starting position>,
     'end_pos':   <the ending position>,
     'conclusion': <the conclusion of the proof, pretty-formatted>,
     'free-ids':   <a dictionary, mapping each free identifier in the proof to its value> 
     'fun-syms':   <a dictionary mapping function symbols that appear in the proof to their signatures>,
     'structures': <a list of all the relevant structure definitions. Each structure contains its file, start and end pos, and the text of the definition>,
     'domains':    <a list of all non-structure domains that appear in the signatures of 'fun-syms'
    ''' 
    text = '\n'.join(block)
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
    proof_starting_position = {'file':file_name, 'line': int(line_number)-1, 'pos': int(col_number)-1}
    second_line = block[2]
    i = findNthOccurrence(second_line,':',3)
    proof_end_line = int(second_line[1+findNthOccurrence(second_line,':',2):i])-1
    proof_end_pos = int(second_line[i+1:].strip())-1
    L = getTotallyLiteralLines(file_name)
    proof_text = getText(L,(proof_starting_position['line'],proof_starting_position['pos']),(proof_end_line,proof_end_pos))
    print('\n=== PROOF TEXT:\n' + proof_text)

def processFile(file):
    L = getLiteralLines(file) 
    blocks = getProofBlocks(L)
    return ''

file = 'chapter03.txt'

for b in blocks:
    analyzeBlock(b)
