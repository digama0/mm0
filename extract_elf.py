#!/usr/bin/env python3
import sys
import re

# Read all input
data = sys.stdin.read()

# Find the ELF string in the info output
match = re.search(r'\[1m\[94minfo\[0m: \[1m"(.+?)"\[0m', data, re.DOTALL)
if match:
    elf_str = match.group(1)
    # Convert escape sequences to bytes
    elf_bytes = bytes(elf_str, 'utf-8').decode('unicode_escape').encode('latin1')
    sys.stdout.buffer.write(elf_bytes)
else:
    sys.stderr.write("Could not find ELF in output\n")
    sys.exit(1)