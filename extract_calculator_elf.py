#!/usr/bin/env python3
import subprocess
import re
import sys

# Run the compiler
result = subprocess.run([
    './target/release/mm0-rs', 'compile', '../examples/calculator_demo.mm1'
], capture_output=True, text=True, cwd='mm0-rs')

# Find the info line with ELF data
match = re.search(r'info.*?"(.+?)"', result.stderr, re.DOTALL)
if not match:
    print("No ELF data found in output")
    sys.exit(1)

escaped_data = match.group(1)

# Convert the escaped string to bytes
binary_data = bytearray()
i = 0
while i < len(escaped_data):
    if escaped_data[i] == '\\' and i + 1 < len(escaped_data):
        if escaped_data[i+1] == 'x' and i + 3 < len(escaped_data):
            # Hex escape
            hex_str = escaped_data[i+2:i+4]
            binary_data.append(int(hex_str, 16))
            i += 4
        elif escaped_data[i+1] == 'n':
            binary_data.append(10)  # newline
            i += 2
        elif escaped_data[i+1] == 'r':
            binary_data.append(13)  # carriage return
            i += 2
        elif escaped_data[i+1] == 't':
            binary_data.append(9)   # tab
            i += 2
        elif escaped_data[i+1] == '\\':
            binary_data.append(92)  # backslash
            i += 2
        else:
            # Unknown escape, just add the backslash
            binary_data.append(ord('\\'))
            i += 1
    else:
        # Regular character
        binary_data.append(ord(escaped_data[i]))
        i += 1

# Write to file
with open('calculator_demo.elf', 'wb') as f:
    f.write(bytes(binary_data))

print(f"ELF written to calculator_demo.elf ({len(binary_data)} bytes)")

# Make it executable
import os
os.chmod('calculator_demo.elf', 0o755)