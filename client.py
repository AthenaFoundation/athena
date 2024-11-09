import sys
sys.path.append('/mnt/c/code/python')
from utils1 import *
import socket

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

