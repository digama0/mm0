#!/usr/bin/env python3
import sys

# Read the escaped string from stdin or file
if len(sys.argv) > 1:
    with open(sys.argv[1], 'rb') as f:
        data = f.read()
else:
    data = sys.stdin.buffer.read()

# The data starts after 'info: "' and ends before the final '"'
# Find where the actual string starts
start = data.find(b'info: "') + 7
end = data.rfind(b'"')

if start < 7 or end < 0 or end <= start:
    print("Error: Could not find string boundaries", file=sys.stderr)
    sys.exit(1)

escaped_str = data[start:end]

# Convert the escaped string to bytes
output = bytearray()
i = 0
while i < len(escaped_str):
    if escaped_str[i] == ord('\\') and i + 1 < len(escaped_str):
        next_char = escaped_str[i + 1]
        if next_char == ord('x') and i + 3 < len(escaped_str):
            # Handle \xNN
            try:
                hex_value = int(escaped_str[i+2:i+4], 16)
                output.append(hex_value)
                i += 4
                continue
            except:
                pass
        elif next_char == ord('\\'):
            output.append(ord('\\'))
            i += 2
            continue
        elif next_char == ord('n'):
            output.append(ord('\n'))
            i += 2
            continue
        elif next_char == ord('r'):
            output.append(ord('\r'))
            i += 2
            continue
        elif next_char == ord('"'):
            output.append(ord('"'))
            i += 2
            continue
    
    # Regular character
    output.append(escaped_str[i])
    i += 1

# Write the binary output
sys.stdout.buffer.write(output)