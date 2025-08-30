#!/usr/bin/env python3
import subprocess
import sys

# Run MM0 compiler
result = subprocess.run(
    ["cargo", "run", "--release", "--", "compile", "test_arm64_write_exe.mm1"],
    capture_output=True,
    text=False  # Get bytes, not text
)

# The output is in the last line of stdout or stderr
output = result.stdout + result.stderr
lines = output.split(b'\n')

# Find the last non-empty line (which should be our string)
binary_line = None
for line in reversed(lines):
    if line.strip():
        binary_line = line
        break

if not binary_line:
    print("No output found", file=sys.stderr)
    sys.exit(1)

# The line should be a quoted string with escape sequences
# Remove quotes if present
if binary_line.startswith(b'"') and binary_line.endswith(b'"'):
    binary_line = binary_line[1:-1]

# Decode escape sequences
output = bytearray()
i = 0
while i < len(binary_line):
    if binary_line[i:i+1] == b'\\' and i + 1 < len(binary_line):
        if binary_line[i+1:i+2] == b'x' and i + 3 < len(binary_line):
            # Handle \xNN
            try:
                hex_value = int(binary_line[i+2:i+4], 16)
                output.append(hex_value)
                i += 4
                continue
            except:
                pass
        elif binary_line[i+1:i+2] == b'\\':
            output.append(ord('\\'))
            i += 2
            continue
        elif binary_line[i+1:i+2] == b'n':
            output.append(ord('\n'))
            i += 2
            continue
        elif binary_line[i+1:i+2] == b'r':
            output.append(ord('\r'))
            i += 2
            continue
        elif binary_line[i+1:i+2] == b'"':
            output.append(ord('"'))
            i += 2
            continue
    
    # Regular character
    output.append(binary_line[i])
    i += 1

# Write to file
with open('test_arm64_exe', 'wb') as f:
    f.write(output)

print(f"Written {len(output)} bytes to test_arm64_exe")