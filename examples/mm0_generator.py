#!/usr/bin/env python3
"""
MM0 Code Generator - Makes writing MM0/MMC code easier

This demonstrates how Python can be used to generate MM0 code, 
automatically handling tedious tasks like:
- Calculating string lengths
- Converting numbers to string representations
- Generating repetitive code patterns
"""

class MM0Generator:
    def __init__(self):
        self.indent = "      "
        
    def string_decl(self, var_name, message):
        """Generate a string declaration with automatic length calculation"""
        length = len(message)
        escaped = message.replace('\\', '\\\\').replace('"', '\\"')
        return f'{{{{{var_name} : (array u8 {length})}} := (list . ,(string->list "{escaped}"))}}'
    
    def sys_write(self, var_name, message=None):
        """Generate a sys_write call"""
        if message is None:
            # Assume var_name contains the message and we need to look up its length
            return f'{{_ := (sys_write 1 <length> {var_name} (& {var_name}))}}'
        else:
            length = len(message)
            return f'{{_ := (sys_write 1 {length} {var_name} (& {var_name}))}}'
    
    def write_string(self, var_name, message):
        """Generate both string declaration and write in one go"""
        return f"""{self.indent}{self.string_decl(var_name, message)}
{self.indent}{self.sys_write(var_name, message)}"""

    def number_to_digits(self, number, var_prefix="d"):
        """Generate code to convert a number into individual digit characters"""
        digits = str(number)
        code = []
        
        for i, digit in enumerate(digits):
            ascii_val = ord(digit)  # '0' = 48, '1' = 49, etc.
            code.append(f'{self.indent}{{{{{var_prefix}{i} : u8}} := (cast {ascii_val})}}  -- \'{digit}\'')
        
        return '\n'.join(code)
    
    def number_to_string_array(self, number, var_name, with_newline=True):
        """Generate code to create a string array from a number"""
        digits = str(number)
        digit_vars = [f'd{i}' for i in range(len(digits))]
        
        # Generate digit conversion code
        digit_code = self.number_to_digits(number)
        
        # Build the array
        array_items = ' '.join(digit_vars)
        if with_newline:
            array_items += ' 10'  # ASCII newline
            length = len(digits) + 1
        else:
            length = len(digits)
            
        array_code = f'{self.indent}{{{{{var_name} : (array u8 {length})}} := (list {array_items})}}'
        
        return digit_code + '\n' + array_code

def generate_fibonacci_demo():
    """Generate a demo that calculates and displays Fibonacci numbers"""
    gen = MM0Generator()
    
    code = '''import "compiler.mm1";

do {
  (mmc-add '(
    (intrinsic @ proc (sys_write {fd : u32} {count : u32}
      (ghost @ mut {buf : (ref @ array u8 count)}) {p : (&sn buf)} : u32))

    (proc (main {n : u32})
      -- Fibonacci calculator demo
      -- Calculate first few Fibonacci numbers
      
'''
    
    # Add title
    code += gen.write_string("title", "Fibonacci Numbers\\n\\n") + "\n\n"
    
    # Calculate Fibonacci numbers
    code += f'''{gen.indent}-- Calculate Fibonacci sequence
{gen.indent}{{{{fib0 : u32}} := 0}}
{gen.indent}{{{{fib1 : u32}} := 1}}
{gen.indent}{{{{fib2 : u32}} := (cast {{fib0 + fib1}})}}  -- 1
{gen.indent}{{{{fib3 : u32}} := (cast {{fib1 + fib2}})}}  -- 2
{gen.indent}{{{{fib4 : u32}} := (cast {{fib2 + fib3}})}}  -- 3
{gen.indent}{{{{fib5 : u32}} := (cast {{fib3 + fib4}})}}  -- 5
{gen.indent}{{{{fib6 : u32}} := (cast {{fib4 + fib5}})}}  -- 8
{gen.indent}{{{{fib7 : u32}} := (cast {{fib5 + fib6}})}}  -- 13
{gen.indent}{{{{fib8 : u32}} := (cast {{fib6 + fib7}})}}  -- 21
'''
    
    # Display the numbers
    fib_values = [0, 1, 1, 2, 3, 5, 8, 13, 21]
    
    for i, val in enumerate(fib_values):
        code += f'''
{gen.indent}-- Display Fib({i}) = {val}
'''
        code += gen.write_string(f"fib{i}_msg", f"Fib({i}) = {val}\\n") + "\n"
    
    code += '''
      -- Footer
'''
    code += gen.write_string("footer", "\\nMM0: Verified Fibonacci sequence!\\n")
    
    code += '''
      )
  ))
  
  -- Generate the ELF
  (print (mmc->string))
};
'''
    
    return code

def generate_prime_checker():
    """Generate a simple prime number checker"""
    gen = MM0Generator()
    
    code = '''import "compiler.mm1";

do {
  (mmc-add '(
    (intrinsic @ proc (sys_write {fd : u32} {count : u32}
      (ghost @ mut {buf : (ref @ array u8 count)}) {p : (&sn buf)} : u32))

    (proc (main {n : u32})
      -- Prime number checker for small numbers
      -- Using hardcoded checks for demonstration
      
'''
    
    code += gen.write_string("title", "Prime Number Check\\n\\n") + "\n\n"
    
    # Check some small primes
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    non_primes = [4, 6, 8, 9, 10, 12, 14, 15, 16, 18]
    
    # Generate checks for a few numbers
    for num in [2, 3, 4, 5, 6, 7]:
        is_prime = num in primes
        result = "prime" if is_prime else "not prime"
        code += gen.write_string(f"num{num}_msg", f"{num} is {result}\\n") + "\n"
    
    code += '''
      )
  ))
  
  -- Generate the ELF
  (print (mmc->string))
};
'''
    
    return code

if __name__ == "__main__":
    # Generate Fibonacci demo
    fib_code = generate_fibonacci_demo()
    with open("fibonacci_generated.mm1", "w") as f:
        f.write(fib_code)
    print("Generated fibonacci_generated.mm1")
    
    # Generate prime checker
    prime_code = generate_prime_checker()
    with open("prime_check_generated.mm1", "w") as f:
        f.write(prime_code)
    print("Generated prime_check_generated.mm1")
    
    # Show how to use the generator for custom code
    print("\nExample of using MM0Generator:")
    gen = MM0Generator()
    
    # Example: Generate code to display a calculation result
    calc_msg = "42 * 3 = 126"
    print(f"\nTo display '{calc_msg}':")
    print(gen.write_string("result", calc_msg + "\\n"))
    
    # Example: Convert number to string
    print(f"\nTo convert number 789 to string:")
    print(gen.number_to_string_array(789, "num_str"))
    
    print("\nThis shows how Python can make MM0 programming much easier!")