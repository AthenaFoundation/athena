import sys, json, os, re
import requests
import random
import numpy as np
import pandas as pd 
import time
import tempfile
import glob
import importlib
from pathlib import Path
import yaml
import pprint
snlp = None

def filenameStem(f):
    return Path(f).stem

def filenameExtension(f):
    return Path(f).suffix

def filenameDir(f):
    (d,_) = os.path.split(f)
    return d

def pathFilename(f):
    (_,f) = os.path.split(f)
    return f

def pp(x):
    pp = pprint.PrettyPrinter(width=41, compact=True)
    pp.pprint(x)

#========================== Uncomment the following 5 lines to get isEnglishWord working.... 
# nltk.download('words')
# nltk.download('wordnet')
# ps = PorterStemmer()
# lemmatizer = WordNetLemmatizer()
# english_words = set(words.words())

def isEnglishWord(word,normalization='stemming'):
    #Note: Stemming works better than lemmatization (e.g., the latter fails to get 'inhibiting').
    stem = ps.stem(word.lower())
    lemmatized_word = lemmatizer.lemmatize(word)
    return word in english_words or spell.correction(word) == word or stem in english_words or lemmatized_word in english_words

def segmentSentences(text):
    doc = snlp(text)
    return [sentence.text for sentence in doc.sentences]

def pos(text):
    doc = snlp(text)
    return [(word,word.pos) for sent in doc.sentences for word in sent.words]

def hasVerb(text):
    return not(all([(p[1] != 'VERB') for p in pos(text)]))

def hasNoun(text):
    return not(all([(p[1] != 'NOUN' and p[1] != 'PROPN') for p in pos(text)]))

def zipLists(L1,L2):
    m = min(len(L1),len(L2))
    res = []
    for i in range(m):
        res.append((L1[i],L2[i]))
    return res 
    
def unzipFile(f):
    os.system("unzip " + f)

def getAllFiles(dir):
    return [f for f in os.listdir(dir) if os.path.isfile(os.path.join(dir, f))]

def getAllFilesRecursively(dir):
    files = []
    path = Path(dir).resolve()
    for file in path.rglob('*'):
        if file.is_file():
            files.append(str(file))
    return files

def getAllSubDirsRecursively(dir):
    files = []
    path = Path(dir).resolve()
    for file in path.rglob('*'):
        if not(file.is_file()):
            files.append(str(file))
    return files

def highlightSection(s,i,j,window=20):
    return f"{s[(i-window):i]}\033[1;32;40m{s[i:j]}\033[m{s[j:(j+window)]}"

def findSubstringOccsBounded(pat, base, a, b):
    slice_base = base[a:b]
    indices = []
    start = 0
    while start < len(slice_base):
        pos = slice_base.find(pat, start)
        if pos != -1:  # if substring found
            indices.append(pos+a)  # adjust index relative to original string
            start = pos + len(pat)  # start next search after this substring
        else:
            start += 1
    return indices

def findSubstringOccsBoundedAccum(pat,base,a,b,results):
    if a >= b:
        return results
    i = base.find(pat,a)
    return results if i < 0 or i > b else findSubstringOccsBoundedAccum(pat,base,i+len(pat),b,[i] + results)

def findSubstringOccsBounded(pat,base,a,b):
    return list(reversed(findSubstringOccsBoundedAccum(pat,base,a,b,[])))
    
def findAndShowAllRegexOccurrences(p,s,window=20,show=True,msg=""):
# Print the list of all (start,end) occurrences of regex pattern p inside the string s, and then return that list. 
    matches = re.finditer(p,s)
    range_pairs = [(match.start(), match.end()) for match in matches]
    counter = 0
    for (start,end) in range_pairs:
        counter += 1
        if show:
            print(msg + "Match #" + str(counter) + ": (" + str(start) + ", " + str(end) + ") --> " + highlightSection(s,start,end,window))
    return range_pairs

def findAllRegexOccurrences(p,s,window=20,show=True,msg=""):
# Find the list of all (start,end) occurrences of regex pattern p inside the string s, and then return that list. 
    matches = re.finditer(p,s)
    range_pairs = [(match.start(), match.end()) for match in matches]
    return range_pairs

def copies(s,n):
    return '' if n < 1 else s + copies(s,n-1)

def insertString(base_string,new_string,pos):
    return base_string[:pos] + new_string + base_string[pos:]

import re

def findFlex(s, s1):
    s1_pattern = '\s*'.join(s1.split())
    matches = re.finditer(s1_pattern, s)
    return [match.start() for match in matches]

google_Search_API_key = "AIzaSyAs7rHGHbSrOdiQ3ZvOQ8B3ji_jR298mhQ"

google_search_engine_id = "964d901822ec646e8"

def readChar():
    print("Press Enter...")
    return sys.stdin.read(1)

def googleSearch(search_term, **kwargs):
    url = "https://www.googleapis.com/customsearch/v1"
    params = {
        'q': search_term,
        'key': google_Search_API_key,
        'cx': google_search_engine_id,
        **kwargs
    }
    response = requests.get(url, params=params)
    return response.json()

def googleSearchTotalResultNumber(search_term, **kwargs):
    url = "https://www.googleapis.com/customsearch/v1"
    params = {
        'q': search_term,
        'key': google_Search_API_key,
        'cx': google_search_engine_id,
        **kwargs
    }
    response = requests.get(url, params=params)
    response_json = response.json()
    if "spelling" in response_json:
        auto_corrected = response_json['spelling']['correctedQuery'] 
    else:
        auto_corrected = ''
    return {'result_count':int(response_json['searchInformation']['totalResults']),
            'auto_corrected': auto_corrected}

def googleKnowledeGraphQueryResults(query):
    service_url = "https://kgsearch.googleapis.com/v1/entities:search"
    params = {
        "query": query,
        "limit": 10,
        "indent": True,
        "key": google_Search_API_key
    }
    response = requests.get(service_url, params=params)
    response_json = response.json()
    #for element in response_json["itemListElement"]:
    #   print(json.dumps(element, indent=2))
    return response_json 

def googleKnowledeGraphQuery(query):
    D = googleKnowledeGraphQueryResults(query)
    if len(D) > 0 and 'itemListElement' in D:
        top_result = D['itemListElement'][0]
        return json.dumps(top_result, indent=2)
    else:
        print("No results found")
        return ''
    
def list_files(directory):
    path = Path(directory)
    for file in path.rglob('*'):
        print(file)

# Replace 'your_directory_path' with the path to the directory you want to traverse
list_files('your_directory_path')

def loopOverFiles(directory,processFile):    
    for filename in os.listdir(directory):
        f = os.path.join(directory, filename)
        if os.path.isfile(f):
            print("About to process this file: " + f)
            processFile(f)
            
def readFileAsString(filename):
    text_file = open(filename, "r")
    data = text_file.read()
    text_file.close()
    return data

def getNonStrippedLiteralLines(filename):
    with open(filename) as f:
        content = f.readlines()
    L = [l for l in content]        
    return L

def getLines(filename):
    with open(filename,errors='replace') as f:
        content = f.readlines()
    L = [l.strip() for l in content if l]
    return [l for l in L if l]

def getLiteralLines(filename):
    with open(filename) as f:
        content = f.readlines()
    L = [l.strip() for l in content]        
    return L

def getTotallyLiteralLines(filename):
    L = []
    with open(filename) as f:
        L = f.readlines()
    return L

def filterOutLines(file,filterOut):
    return [l for l in getLines(file) if not(filterOut(l))]

def filterLines(file,filter):
    return [l for l in getLines(file) if filter(l)]

def replaceLines(filename,replacementFunction):
    L = getLines(filename)
    res = []
    for l in L:
        l1 = l
        try:
            l1 = replacementFunction(l)
        except:
            pass
        res.append(l1)
    return res

def writeFile(L,filename):
    with open(filename, 'w') as f:
        for item in L:
            f.write("%s\n" % item)    

def writeStringToFile(s,filename):
    file = open(filename,"wt")
    n = file.write(s)
    file.close()

def removeMultipleNewlines(f_in,f_out):
    L = getNonStrippedLiteralLines(f_in)
    R = []
    for i in range(len(L)):
        if L[i].strip() == '':
            if i > 0 and L[i-1].strip() == '':
                pass
            else:
                R.append(L[i])
        else:
            R.append(L[i])
    writeStringToFile(''.join(R),f_out)
    
def appendToFile(s,filename):
    with open(filename, "a") as myfile:
        myfile.write(s)

def dedupFile(f):
    D = {}
    L = getLines(f)
    for l in L:
        if not(l in D):
            D[l] = True
    writeFile(D.keys(),f + "_deduped.txt")

def getJsonLines(file):
    L = getLines(file)
    dicts = []
    for l in L:
        D = json.loads(l)
        dicts.append(D)
    return dicts

def processPatterns(premise_sentences,row_start,row_end):
    R = {}
    total = 0
    for i in range(row_start,row_end):
        if i > 0 and i % 500 == 0:
            total += 500
            print("Processed " + str(total) + " records...")
        for s in premise_sentences:
            if s in df.loc[i]['TEXT']:
                R[s] = df.loc[i]['ROW_ID']        
    return R


def doItPlain(source,target,N=20000):
    start = time.time()
    for i in range(N):
        res = target in source
    end = time.time()
    return (end-start)    

def doItTrie(source,target,N=20000):
    A = ahocorasick.Automaton()
    sentences = source.split(".")
    index = 0
    for s in sentences:
        A.add_word(s,(index,s))
        index += 1
    start = time.time()        
    for i in range(N):
        res = target in A
    end = time.time()        
    return (end-start)

def compareTimes(source,target,N=20000):
    times_to_repeat = 100
    plain_times = []
    for _ in range(times_to_repeat):
        plain_times.append(doItPlain(source,target,N))
    plain_time = np.mean(plain_times)
    trie_times = []
    for _ in range(times_to_repeat):   
        trie_times.append(doItTrie(source,target,N))
    trie_time = np.mean(trie_times)                            
    q = plain_time/trie_time
    print("Plain time: " + str(plain_time) + ", trie time: " + str(trie_time) + ", quotient: " + str(q))

def process(premise_sentences,row_start,row_end,out_file="results_out.txt"):
    R = processPatterns(premise_sentences,row_start,row_end)
    L = []
    for s in R:
        L.append(s + " ||| " + str(R[s]))
    writeFile(L,out_file)
    print("\nDone, found " + str(len(L)) + " entries...\n")
    return R

def construct_prompt(instruction, input_text):
    instruction = instruction.strip()
    input_text = input_text.strip()
    if not instruction:
        return ""
    if input_text:
        prompt = f"Below is an instruction that describes a task, paired with an input that provides further context. Write a response that appropriately completes the request.\n\n### Instruction:\n{instruction}\n\n### Input:\n{input_text}\n\n### Response:"
    else:
        prompt = f"Below is an instruction that describes a task. Write a response that appropriately completes the request.\n\n### Instruction:\n{instruction}\n\n### Response:"
    return prompt

def aboutRight(cutpoint_delta,first):
    if first:
        return cutpoint_delta > 2200
    else:
        return cutpoint_delta > 1700        
        
def addNewPart(s,last_cutpoint,i,parts):
    new_part = {'start':last_cutpoint,
                'end':i}
    parts.append(new_part)
                
def partSize(part):
    return part['end'] - part['start']

def tooSmall(part):
    return partSize(part) < 500

def spaces(n):
    return "" if n < 1 else (" " + spaces(n-1))

def getProperty(s):
    return s.split("-")[0].lower()

def getArgument(s):
    return s.split(":")[1]

def inRange(x,a,b):
    return x >= a and x < b

def fallInside(spans,chunk):
    start,end = chunk['start'],chunk['end']
    for (a,b) in spans:
        if not(inRange(a,start,end)) or not(inRange(b,start,end)):
            return False
    return True
        
def isBracket(s):
    return s == "[" or s == "]"

def makeTextFileName(ann_file_name):
    toks = ann_file_name.split(".")
    res = (''.join(toks[:len(toks)-1])) + ".txt"
    return res

def findFirst(L,pred):
    for x in L:
        if pred(x):
            return x
    return None

def writeAll(examples,out_file):
    s = examplesToString(examples)
    writeStringToFile(s,out_file)    
    
def null_intersection(L1,L2):
     I = set(L1).intersection(set(L2))
     if I:
         return False
     return True        

def non_null_intersection(L1,L2): 
    return not(null_intersection(L1,L2))

def sleepFor(seconds):
    time.sleep(seconds)

def processAllFiles(directory,file_pattern,processor):
    file_pattern = directory + "/" + file_pattern
    all_matching_files = glob.glob(file_pattern)
    N = len(all_matching_files)
    print_progress = False
    if N > 1000:
        print_progress = True
        print("Will process " + str(N) + " files in " + directory + ".")
    counter = 0
    for file in all_matching_files:
        processor(file)        
        counter += 1
        if counter % 100 == 0:
            print("Processed " + str(counter) + " files so far, " + str(N-counter) + " to go...")

def forall(L,pred):
    for x in L:
        if not(pred(x)):
            return False
    return True

def forSome(L,pred):
    for x in L:
        if pred(x):
            return True
    return False

def tokenize(input_string, usual_delimiters, delimiters_to_keep):
    # Escaping delimiters
    usual_delimiters = [re.escape(d) for d in usual_delimiters]
    delimiters_to_keep = [re.escape(d) for d in delimiters_to_keep]
    # Creating regex
    usual_regex = '|'.join(usual_delimiters)
    keep_regex = '({})'.format('|'.join(delimiters_to_keep))
    # Splitting string
    tokens = re.split(usual_regex, input_string)
    # Splitting tokens again, keeping the delimiters
    tokens = [re.split(keep_regex, t) for t in tokens]
    # Flattening list of tokens and removing empty strings
    tokens = [t for sublist in tokens for t in sublist if t]
    return tokens


def isPunctChar(c):
    return c in ['(', ')', '[', ']', '.', ':', ',']

def isEnglishWordModuloPunctuationAux(t1,t2):
    google_search_result_threshold = 10
    #t1 ends with '-' and t2 is a word, but might end in punctuation, e.g. a comma.
    #Also, t1 might start with something like a parenthesis.
    s1 = t1[:-1] # Drop the dash at the end of t1 
    s2 = t2
    # if t1 starts with a punctuation character:
    if isPunctChar(t1[0]): 
        s1 = t1[1:]
    # if t2 ends with a punctuation character:        
    if isPunctChar(t2[-1]):
        s2 = t2[:-1]
    joined_option_minus_hyphen = s1 + s2
    joined_option_with_hyphen = s1 + '-' + s2
    hits_minus_hyphen = googleSearchTotalResultNumber(joined_option_minus_hyphen)['result_count']
    hits_with_hyphen = googleSearchTotalResultNumber(joined_option_minus_hyphen)['result_count']
    return (hits_minus_hyphen > 10 and hits_minus_hyphen > hits_with_hyphen) or (hits_minus_hyphen > 2000000000 and hits_minus_hyphen >= hits_with_hyphen)

def isEnglishWordModuloPunctuation(t1,t2):
    try:
        return isEnglishWordModuloPunctuationAux(t1,t2)
    except:
        return False 
    
def joinHyphenatedWordsAux(L):
    R = []
    iteration = 0
    for l in L:
        line = l
        if l.endswith('\n'):
            l = l[:-1]
        iteration += 1
        if iteration % 200 == 0:
            print("On line: " + str(iteration))
        toks = l.split(' ')
        new_toks = []
        N = len(toks)
        i = 0
        while i < N:
            t = toks[i]
            if t.endswith("-"):
                if i < N-1 and isEnglishWordModuloPunctuation(t,toks[i+1]): 
                    joined = t[:-1] + toks[i+1]
                    print("About to replace '" + t + " " + toks[i+1] + "' with: " + joined)
                    new_toks.append(joined)
                    i += 2
                else:
                    new_toks.append(t)
                    i += 1
            else:
                new_toks.append(t)
                i += 1
        new_line = ' '.join(new_toks)
        if line.endswith('\n'):
            new_line = new_line + '\n'
        R.append(new_line)
    return R

def joinHyphenatedWords(file):
    L = getNonStrippedLiteralLines(file)
    return joinHyphenatedWordsAux(L)

def removeCharWithOrd(in_file,ord_code,out_file):
    # Read the file contents
    with open(in_file, 'r', encoding='utf-8') as file:
        contents = file.read()
    # Remove the character with the given ord code
    filtered_contents = ''.join([char for char in contents if ord(char) != ord_code])
    # Write the filtered contents back to the file
    with open(out_file, 'w', encoding='utf-8') as file:
        file.write(filtered_contents)

def collapseMultipleAdjacentBlanks(input_file, output_file):
    # Read the content from the input file
    with open(input_file, 'r') as file:
        content = file.read()
    # Replace multiple spaces with a single space
    collapsed_content = re.sub(r'^\s+', '',content)
    collapsed_content2 = re.sub(r' +', ' ',collapsed_content)
    # Write the modified content to the output file
    with open(output_file, 'w') as file:
        file.write(collapsed_content2)

def stripLines(file_in,file_out):
    # Read the file line by line, strip leading white space, and store lines in a list
    lines =  getLiteralLines(file_in)
    R = []
    for l in lines:
        if l.isspace():
            R.append(l)
        else:
            R.append(l.lstrip())
    writeFile(R,file_out)        

def yamlToJson(yaml_file):
    with open(yaml_file, 'r') as file:
        data = yaml.safe_load(file)
        return data
