#!/usr/bin/env python3
"""Save ARM64 binary from MM0 output."""

import subprocess
import sys

# Run the MM0 compiler and capture output
result = subprocess.run(
    ['target/debug/mm0-rs', 'compile', 'test_arm64_hexdump.mm1'],
    capture_output=True,
    text=True
)

# Find the line with the binary data
# It should contain the Mach-O magic number
for line in result.stdout.split('\n'):
    if r'\xcf\xfa\xed\xfe' in line:
        # Extract the string between quotes
        start = line.find('"') + 1
        end = line.rfind('"')
        if start > 0 and end > start:
            escaped_data = line[start:end]
            # Convert escaped string to binary
            try:
                binary_data = escaped_data.encode('utf-8').decode('unicode_escape').encode('latin-1')
                # Write to file
                with open('hello_arm64', 'wb') as f:
                    f.write(binary_data)
                print(f"Successfully wrote {len(binary_data)} bytes to hello_arm64")
                # Verify Mach-O header
                if binary_data[:4] == b'\xcf\xfa\xed\xfe':
                    print("✓ Valid Mach-O ARM64 binary!")
                    print(f"First 16 bytes: {' '.join(f'{b:02x}' for b in binary_data[:16])}")
                sys.exit(0)
            except Exception as e:
                print(f"Error decoding: {e}")

print("Failed to find binary data in output")
sys.exit(1)