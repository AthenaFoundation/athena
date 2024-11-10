import sys
import socket
import sys
import json
sys.path.append('/mnt/c/code/python')
from utils import *

def send_request_to_server(request: str,port=10000) -> str:
    # Define server address and port
    server_address = 'localhost'
    # Create a TCP/IP socket
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        # Connect to the server
        sock.connect((server_address, port))
        try:
            # Send the request string encoded as bytes
            sock.sendall(request.encode('utf-8'))
            # Receive the response from the server
            response = sock.recv(4096)  # Buffer size is 4096 bytes
            # Decode the response from bytes to a string
            return response.decode('utf-8')
        except Exception as e:
            print(f"An error occurred: {e}")
            return ""

def send_request_to_server(request: str, port=10000) -> str:
    server_address = 'localhost'
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        sock.settimeout(5)  # Set a 5-second timeout for demonstration
        try:
            sock.connect((server_address, port))
            sock.sendall(request.encode('utf-8'))
            response = sock.recv(4096)
            return response.decode('utf-8')
        except socket.timeout:
            print("Connection timed out.")
            return ""
        except Exception as e:
            print(f"An error occurred: {e}")
            return ""

class PersistentClient:
    def __init__(self, port=10000):
        self.server_address = 'localhost'
        self.port = port
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.sock.connect((self.server_address, self.port))

    def send_request(self, request: str) -> str:
        try:
            self.sock.sendall(request.encode('utf-8'))
            response = self.sock.recv(4096)
            return response.decode('utf-8')
        except Exception as e:
            print(f"An error occurred: {e}")
            return ""

    def close(self):
        self.sock.close()

# Example usage
#client = PersistentClient()

def send_request_to_server(request: str, port=10000) -> str:
    server_address = 'localhost'
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        sock.settimeout(4)  # Set a 5-second timeout for demonstration
        try:
            sock.connect((server_address, port))
            sock.sendall(request.encode('utf-8'))
            response = sock.recv(4096)
            return response.decode('utf-8')
        except socket.timeout:
            print("Connection timed out.")
            return ""
        except Exception as e:
            print(f"An error occurred: {e}")
            return ""


declaration_line = 'declare A, B, C, D, E, F, G, H, J, I, K: Boolean'
#send_request_to_server(declaration_line)

def spaces(i):
    if i < 1:
        return ""
    else:
        return " " + spaces(i-1)

def checkProof(line):
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

file = "./ft/data/gpt_and_english_proofs_230.jsonl"
#L = getLines(file)
def checkAll(file):
    L = getLines(file)
    R = []
    for i in range(len(L)):
        print("About to work on proof #" + str(i))
        response = checkProof(L[i])        
        R.append(response)
    return R

# R = checkAll(file) 
