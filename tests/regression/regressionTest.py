#
# A simple script that does a regression run on on a set of Athena tests. The tests are
# extensive enough that they should catch any correctness-affecting changes in behavior 
# introduced by modifying Athena's source code. The function runAthenaTests returns the total
# number of errors detected, so this will be 0 if all tests pass and some positive number
# otherwise, which is capped at an upper bound of 124 to ensure that this script can be
# used with git bisect for debugging purposes. Detailed output is always written in the
# file regression_results.txt, which can be manually inspected after the testing is done.
#
# A point specific to FPMICS: The code of chapter 5 deliberately introduces a couple of 
# proof errors for illustration purposes. To avoid failing the regression test due to these
# buggy proofs, either comment them out, or else make another copy of that chapter's code 
# that altogether omits these proofs, and use that copy in book_test_files below.
#

import os
import sys

basic_test_files = ['basic/sets_unittest', 'basic/fmaps_unittest', 'basic/dmaps_unittest']

main_test_files_1 = ['nat-gcd','integer-times','order_unittest','ordered-list_unittest','fast-power_unittest','group_unittest','ring_unittest']
main_test_files_2 = ['integral-domain_unittest','integer-power-series','integer-power-series-group','power_unittest','transitive-closure_unittest']
main_test_files = [('main/' + w) for w in main_test_files_1 + main_test_files_2]

search_test_files = ['search/binary-search-tree-nat','search/binary-search-tree_unittest','search/binary-search_unittest','search/binary-search-nat','search/binary-search1-nat']

memory_test_files_1 = ['memory_unittest','count-range_unittest','trivial-iterator_unittest','forward-iterator_unittest','binary-search-range_unittest']
memory_test_files_2 = ['bidirectional-iterator_unittest','random-access-iterator_unittest','replace-range_unittest','reverse-range_unittest']
memory_test_files_3 = ['copy-range_unittest','copy-range-backward_unittest','ordered-range_unittest','range_unittest','swap-implementation_unittest']
memory_test_files = [('memory-range/' + w) for w in memory_test_files_1 + memory_test_files_2 + memory_test_files_3]

algebra_test_files = ['algebra/Z-poly','algebra/Z-as-integral-domain','algebra/Z-poly-as-group','algebra/function_unittest','algebra/permutation_unittest']

chapters = ['01','03','08','09','11','12','13','14','15','04','05','06','07','10','17','18']
book_test_files = ['tests/regression/book/chapter' + c for c in chapters] 

test_files = basic_test_files + main_test_files + search_test_files + memory_test_files + algebra_test_files + book_test_files

def readLines(file_name):
    with open(file_name,'r',errors='ignore') as file:
        lines = [l.strip() for l in file.readlines()]
        return [l for l in lines if l]

def errorLine(l):
    error_phrases = ['failed application of', 'failed existential', 'failed universal']
    l = l.lower()
    toks = l.split()    
    return 'error:' in toks or any([l.startswith(p) for p in error_phrases])

def runAthenaTests(athena_executable="sml @SMLload=athena_image.x86-linux"):
    output_file = "regression_results.txt"
    os.system('echo "" > ' + output_file)
    res_files=[]
    total_errors = 0   
    for f in test_files:
        f_out = f.replace("/","_")
        res_file = "res_" + f_out + ".txt"
        res_files.append(res_file)
        input_file = f
        print("\nGenerating results for test file " + input_file + " ...")
        cmd = athena_executable + ' ' + input_file + ' > ' + res_file
        if not(athena_executable.startswith('sml @SMLload=')):
            cmd = athena_executable + ' ' + input_file + ' quit > ' + res_file
        print(cmd)
        os.system(cmd)
    for f in res_files:
        lines = readLines(f)
        errors = 0
        for l in lines:
            if errorLine(l):
                errors += 1
        if errors > 0:
           print("\nFound " + str(errors) + " errors in file " + f + "\n")
           total_errors += errors                       
        else:
           print("\nAll tests passed for " + f + "!")
    all_files = ' '.join(res_files)
    cmd = "cat " + all_files + " > " + output_file
    os.system(cmd)
    os.system('rm ' + all_files)   
    print("\nTotal number of errors: " + str(total_errors) + ", all output found in " + output_file + ".\n")
    if total_errors > 0:
        return max(total_errors,124)
    else:
        return 0

if __name__ == "__main__":
    if len(sys.argv) == 2:
        runAthenaTests(sys.argv[1])
    else:
        runAthenaTests()

