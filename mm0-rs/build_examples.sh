#!/bin/bash
# Build script for MM1 examples using improved MMC library

echo "=== Building MM1 Examples ==="
echo

# Set the MM0-RS binary path
MM0_RS="${MM0_RS:-cargo run --}"

# Function to compile an MM1 file
compile_mm1() {
    local input="$1"
    local output="${2:-${input%.mm1}}"
    
    echo "Compiling $input -> $output"
    
    # Run mm0-rs to compile the MM1 file
    # The mmc commands in the file will generate the binary
    $MM0_RS compile "$input" --output "$output" || {
        echo "  ❌ Compilation failed"
        return 1
    }
    
    echo "  ✅ Success"
    
    # If on ARM64 Mac, try to run it
    if [[ "$(uname -m)" == "arm64" && "$(uname)" == "Darwin" ]]; then
        if [[ -x "$output" ]]; then
            echo -n "  Running: "
            ./"$output"
            echo " (exit code: $?)"
        fi
    fi
    
    echo
}

# Build examples
cd examples || exit 1

# Simple examples first
compile_mm1 "calc_simple.mm1" "calculator"

# More complex examples using the library
for example in fibonacci.mm1 array_sum.mm1 echo_args.mm1 prime_checker.mm1; do
    if [[ -f "$example" ]]; then
        compile_mm1 "$example"
    fi
done

echo "=== Testing Generated Binaries ==="
echo

# Test fibonacci
if [[ -x fibonacci ]]; then
    echo "Fibonacci(10):"
    ./fibonacci
    echo "  Result: $? (expect 55)"
    echo
fi

# Test array sum
if [[ -x array_sum ]]; then
    echo "Array sum [10,20,30,40]:"
    ./array_sum
    echo "  Result: $? (expect 100)"
    echo
fi

# Test echo with arguments
if [[ -x echo_args ]]; then
    echo "Echo arguments test:"
    ./echo_args hello world "MM0 compiler"
    echo
fi

# Test prime counter
if [[ -x prime_checker ]]; then
    echo "Primes up to 20:"
    ./prime_checker
    echo "  Result: $? (expect 8)"
    echo
fi

echo "=== Build Complete ==="