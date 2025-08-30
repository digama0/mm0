#!/usr/bin/env python3
"""Extract ARM64 binary from MM0 compiler output."""

import subprocess
import re
import sys

# Run the MM0 compiler
result = subprocess.run(
    ['target/debug/mm0-rs', 'compile', 'test_arm64_hexdump.mm1'],
    capture_output=True,
    text=True
)

# Look for the info line with the binary data
lines = result.stdout.split('\n')
for i, line in enumerate(lines):
    if '[94minfo[0m:' in line:
        # The binary data is on this line between quotes
        match = re.search(r'\[94minfo\[0m: \[1m"(.*)"\[0m', line)
        if match:
            escaped_data = match.group(1)
            # Convert the escaped string to binary
            binary_data = escaped_data.encode('utf-8').decode('unicode_escape').encode('latin-1')
            
            # Write to file
            with open('hello_arm64', 'wb') as f:
                f.write(binary_data)
            
            print(f"Wrote {len(binary_data)} bytes to hello_arm64")
            
            # Show first few bytes to verify
            print(f"First 16 bytes: {' '.join(f'{b:02x}' for b in binary_data[:16])}")
            
            # Check if it's a valid Mach-O
            if binary_data[:4] == b'\xcf\xfa\xed\xfe':
                print("✓ Valid Mach-O ARM64 binary detected!")
            
            sys.exit(0)

print("Failed to extract binary data")
sys.exit(1)