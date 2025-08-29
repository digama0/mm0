#!/usr/bin/env python3
import sys
import re

# Read all input
data = sys.stdin.read()

# Find the ELF string in the info output - handle multiline
match = re.search(r'info\[0m: \[1m"(.+?)"\[0m', data, re.DOTALL)
if match:
    elf_str = match.group(1)
    # Convert escape sequences to bytes
    elf_bytes = elf_str.encode('latin1').decode('unicode_escape').encode('latin1')
    sys.stdout.buffer.write(elf_bytes)
else:
    sys.stderr.write("Could not find ELF in output\n")
    sys.exit(1)