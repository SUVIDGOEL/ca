import os
import subprocess



def create_plaintext():
    with open("plaintext.txt", "w") as f:
        f.write(os.urandom(16).hex() + "\n")
        f.write(os.urandom(16).hex() + "\n")

def memory_trace_genrator():
    subprocess.run("gcc analysis.c -o run -lcrypto", shell=True)
    subprocess.run("pin -t pintool.so -- ./run", shell=True)
    
def check_result():
    file1 = "memory_traces/Memory_Trace_iter_0.out"
    file2 = "memory_traces/Memory_Trace_iter_1.out"
    mapping = {}

    with open(file1, 'r') as f:
        for line in f:
            parts = line.strip().split()
            if len(parts) != 2:
                continue
            first, second = parts
            if first not in mapping:
                mapping[first] = set()
            mapping[first].add(second)

    # Compare with file2
    count = 0

    with open(file2, 'r') as f:
        for line in f:
            parts = line.strip().split()
            if len(parts) != 2:
                continue
            first, second = parts

            if first in mapping and second not in mapping[first]:
                count += 1
    return count

create_plaintext()
memory_trace_genrator()
res = check_result()
if res==0 : print("Test Pass")
else: print("Test Fails")
