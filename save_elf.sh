#!/bin/bash
cd mm0-rs
./target/release/mm0-rs compile ../examples/calculator_demo.mm1 2>&1 | \
sed -n '/^.*info.*"\\x7fELF/,/"[^"]*$/{s/^[^"]*"//;s/"[^"]*$//;p}' | \
tr -d '\n' | \
python3 -c '
import sys
data = sys.stdin.read()
# Process escape sequences
binary = bytearray()
i = 0
while i < len(data):
    if i + 3 < len(data) and data[i:i+2] == "\\x":
        binary.append(int(data[i+2:i+4], 16))
        i += 4
    else:
        binary.append(ord(data[i]))
        i += 1
        
with open("../calculator_demo.elf", "wb") as f:
    f.write(bytes(binary))
print(f"Wrote {len(binary)} bytes")
'