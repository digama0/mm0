#!/bin/bash
# Extract ARM64 binary from MM0 output

# Run MM0 and capture output in a variable
OUTPUT=$(cargo run --release -- compile test_arm64_write_exe.mm1 2>&1 | tail -1)

# The output is the escaped string, we need to unescape it
# Use printf to interpret escape sequences
echo -n "$OUTPUT" | sed 's/^"//' | sed 's/"$//' | while IFS= read -r -n2 chars; do
    if [[ "$chars" == "\\" ]]; then
        # Read the next character
        IFS= read -r -n1 next
        if [[ "$next" == "x" ]]; then
            # Read two hex digits
            IFS= read -r -n2 hex
            printf "\x$hex"
        elif [[ "$next" == "\\" ]]; then
            printf "\\"
        elif [[ "$next" == "n" ]]; then
            printf "\n"
        elif [[ "$next" == "r" ]]; then
            printf "\r"
        elif [[ "$next" == '"' ]]; then
            printf '"'
        else
            printf "\\$next"
        fi
    else
        printf "%s" "$chars"
    fi
done > test_arm64_exe