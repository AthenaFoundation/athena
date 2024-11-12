import sys
import socket
import sys
import json
from utils import *

def extract_response(sock):
    chunks = []
    while True:
        chunk = sock.recv(40960)
        if not chunk:  # Connection closed by server
            break
        chunks.append(chunk)
    return b''.join(chunks).decode('utf-8')


# Note: send_request_to_server_simple should only be used if the corresponding server uses readAllSimple.

def send_request_to_server_simple(request: str, port=10000) -> str:
    server_address = 'localhost'
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        sock.settimeout(4)  # Set a 5-second timeout for demonstration
        try:
            sock.connect((server_address, port))
            sock.sendall(request.encode('utf-8'))
            sock.sendall(''.encode('utf-8'))
            sock.shutdown(socket.SHUT_WR)
            return extract_response(sock)
        except socket.timeout:
            print("Connection timed out.")
            return ""
        except Exception as e:
            print(f"An error occurred: {e}")
            return ""

# The default implementation of send_request_to_server encodes the size of the 
# Athena payload into the first 4 bytes of the request (thus allowing payloads up to 4GB). 
# This must be used in conjunction with readAll on the server side, which first extracts
# the leading 4 bytes of the client's request, transforms those into the integer value N 
# they represent, and then reads exactly N bytes from the connection. 

def send_request_to_server(request: str, port=10000) -> str:
    server_address = 'localhost'
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        sock.settimeout(4)
        try:
            sock.connect((server_address, port))
            # Send length as 4-byte integer first
            request_bytes = request.encode('utf-8')
            length = len(request_bytes)
            sock.sendall(length.to_bytes(4, byteorder='big'))
            sock.sendall(request_bytes)
            sock.shutdown(socket.SHUT_WR)
            return extract_response(sock)
        except socket.timeout:
            print("Connection timed out.")
            return ""
        except Exception as e:
            print(f"An error occurred: {e}")
            return ""

def spaces(i):
    if i < 1:
        return ""
    else:
        return " " + spaces(i-1)

def checkProof(line):
#
# This function takes a string representing a line from a .jsonl file like gpt_and_english_proofs_230.jsonl 
# and checks whether or not the formal proof that can be found in that line is valid. If it is, it returns
# a pair of the form (True,<theorem>), where the string <theorem> is a formula representing the conclusion of the proof.
# If the proof is not valid, then the result is a pair of the form (False,<error message>), where the string <error message>
# provides more detail on where exactly the proof went wrong, and what exactly was wrong (a syntax error, a logic error, and if
# so, the type of error, etc.). 
#
    D = json.loads(line)
    premises = D['premises']
    goal = D['goal']
    assumes = '\n'.join([spaces(index) + "assume premise-" + str(index+1) + " := " + premises[index] for index in range(len(premises))])
    proof = assumes + "\nconclude " + goal + "\n" + D['ndlProof']
    athena_response = send_request_to_server(proof)
    athena_response_lower = athena_response.lower() 
    if 'error' in athena_response_lower or 'failed' in athena_response_lower: 
        return (False,athena_response)
    else:
        return (True,athena_response)

def checkAll(file):
#
# This function works with an entire jsonl file like gpt_and_english_proofs_230.jsonl. It basically
# iterates the single-line function checkProof over all the contents of the jsonl file. The result
# is a list of pairs (boolean_flag,<details>), as produced by checkProof, one for each line in the jsonl file.
#
    L = getLines(file)
    R = []
    send_request_to_server('declare A, B, C, D, E, F, G, H, J, I, K: Boolean')
    for i in range(len(L)):
        print("About to work on proof #" + str(i))
        response = checkProof(L[i])        
        R.append(response)
    return R

# Example use (where file is a path like "../data/gpt_generated_athena_and_english_proofs_raw_data_230.ath"):
# R = checkAll(file) 
# This will give all successful/valid proofs: 
# T = [r for r in R if r[0]]
# And this will give all incorrect proofs:
# F = [r for r in R if not(r[0])]
