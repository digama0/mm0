#!/usr/bin/env python3
import subprocess
import re

# Run MM0 compiler
result = subprocess.run(
    ["cargo", "run", "--release", "--", "compile", "test_arm64_write_exe.mm1"],
    capture_output=True,
    text=True
)

# The output contains the binary as an escaped string after "info:"
output = result.stderr

# Find the line that contains the info output with the binary
info_match = re.search(r'info.*?:\s*.*?"([^"]+)"', output, re.DOTALL)
if not info_match:
    print("Could not find info output with binary string")
    exit(1)

escaped_string = info_match.group(1)

# Decode escape sequences
output_bytes = bytearray()
i = 0
while i < len(escaped_string):
    if escaped_string[i] == '\\' and i + 1 < len(escaped_string):
        if escaped_string[i+1] == 'x' and i + 3 < len(escaped_string):
            # Handle \xNN
            try:
                hex_value = int(escaped_string[i+2:i+4], 16)
                output_bytes.append(hex_value)
                i += 4
                continue
            except:
                pass
        elif escaped_string[i+1] == '\\':
            output_bytes.append(ord('\\'))
            i += 2
            continue
        elif escaped_string[i+1] == 'n':
            output_bytes.append(ord('\n'))
            i += 2
            continue
        elif escaped_string[i+1] == 'r':
            output_bytes.append(ord('\r'))
            i += 2
            continue
        elif escaped_string[i+1] == '"':
            output_bytes.append(ord('"'))
            i += 2
            continue
    
    # Regular character
    output_bytes.append(ord(escaped_string[i]))
    i += 1

# Write to file
with open('test_arm64_exe', 'wb') as f:
    f.write(output_bytes)

print(f"Written {len(output_bytes)} bytes to test_arm64_exe")

# Verify it's a Mach-O file
if len(output_bytes) >= 4:
    magic = output_bytes[:4]
    if magic == b'\xcf\xfa\xed\xfe':
        print("✓ Valid Mach-O ARM64 file")
    else:
        print(f"⚠ Invalid magic: {magic.hex()}")