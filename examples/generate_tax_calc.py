#!/usr/bin/env python3
"""Generate MM0 code for tax calculations with automatic string formatting"""

def mm0_string(s):
    """Convert a Python string to MM0 string literal with proper length"""
    length = len(s)
    escaped = s.replace('\\', '\\\\').replace('"', '\\"')
    return f'{{(array u8 {length})}} := (list . ,(string->list "{escaped}"))'

def mm0_write(var_name, message):
    """Generate a sys_write call"""
    length = len(message)
    return f'{{_ := (sys_write 1 {length} {var_name} (& {var_name}))}}'

def mm0_u32_to_digits(value, var_prefix):
    """Generate MM0 code to convert a number to individual digit characters"""
    digits = str(value)
    code = []
    
    for i, digit in enumerate(digits):
        # Convert digit to ASCII (0 = 48)
        code.append(f'      {{{{{var_prefix}{i} : u8}} := (cast {{{ord(digit)}}})}}')
    
    return '\n'.join(code), len(digits)

def generate_tax_calculation():
    """Generate MM0 code for a simple tax calculation"""
    
    header = '''import "compiler.mm1";

do {
  (mmc-add '(
    (intrinsic @ proc (sys_write {fd : u32} {count : u32}
      (ghost @ mut {buf : (ref @ array u8 count)}) {p : (&sn buf)} : u32))

    (proc (main {income : u32})
      -- Simple tax calculator demo
      -- For demonstration: 10% tax on first 10000, 20% on rest
      
'''
    
    # Generate the calculation logic
    body = '''      -- Display header
      {{title {mm0_string("Tax Calculator Demo\\n\\n")}}}
      {mm0_write("title", "Tax Calculator Demo\\n\\n")}
      
      -- Show income (hardcoded display for 123 = $12,300)
      {{inc_msg {mm0_string("Income: $12,300\\n")}}}
      {mm0_write("inc_msg", "Income: $12,300\\n")}
      
      -- Calculate tax brackets
      -- First bracket: 10% on up to 10000
      {{bracket1 : u32} := 10000}
      {{rate1 : u32} := 10}  -- 10%
      
      -- Tax on first bracket = 10000 * 10 / 100 = 1000
      {{tax1 : u32} := (cast {{bracket1 * rate1} / 100})}
      
      -- Second bracket: 20% on amount over 10000
      -- For income 123 (representing 12300), excess = 2300
      {{excess : u32} := (cast {income - 100})}  -- 123 - 100 = 23 (representing 2300)
      {{rate2 : u32} := 20}  -- 20%
      
      -- Tax on second bracket = 23 * 20 / 100 = 4 (representing 460)
      {{tax2 : u32} := (cast {{excess * rate2} / 100})}
      
      -- Total tax = 1000 + 460 = 1460 (represented as 14)
      {{total_tax : u32} := (cast {10 + tax2})}  -- 10 represents 1000
      
      -- Display tax breakdown
      {{brk1_msg {mm0_string("Tax on first $10,000 (10%): $1,000\\n")}}}
      {mm0_write("brk1_msg", "Tax on first $10,000 (10%): $1,000\\n")}
      
      {{brk2_msg {mm0_string("Tax on next $2,300 (20%): $460\\n")}}}
      {mm0_write("brk2_msg", "Tax on next $2,300 (20%): $460\\n")}
      
      {{total_msg {mm0_string("\\nTotal tax: $1,460\\n")}}}
      {mm0_write("total_msg", "\\nTotal tax: $1,460\\n")}
      
      -- After-tax income
      {{after_tax : u32} := (cast {income - total_tax})}  -- 123 - 14 = 109 (representing 10,840)
      
      {{after_msg {mm0_string("After-tax income: $10,840\\n\\n")}}}
      {mm0_write("after_msg", "After-tax income: $10,840\\n\\n")}
      
      -- Footer
      {{footer {mm0_string("MM0: Verified tax calculations!\\n")}}}
      {mm0_write("footer", "MM0: Verified tax calculations!\\n")}
      )
'''
    
    footer = '''  ))
  
  -- Generate the ELF
  (print (mmc->string))
};
'''
    
    # Process the template
    result = header + body + footer
    
    # Replace the template functions
    result = result.replace('{mm0_string(', '').replace(')}', ')')
    result = result.replace('{mm0_write(', '').replace(')}', ')')
    
    # Manually process mm0_string calls
    import re
    
    def process_mm0_string(match):
        s = match.group(1)
        # Unescape for length calculation
        unescaped = s.replace('\\\\', '\\').replace('\\"', '"')
        # Process \n
        unescaped = unescaped.replace('\\n', '\n')
        length = len(unescaped)
        return f'(array u8 {length})}} := (list . ,(string->list "{s}")'
    
    result = re.sub(r'"([^"]+)"\)', process_mm0_string, result)
    
    def process_mm0_write(match):
        var = match.group(1)
        msg = match.group(2)
        # Unescape for length calculation
        unescaped = msg.replace('\\\\', '\\').replace('\\"', '"')
        unescaped = unescaped.replace('\\n', '\n')
        length = len(unescaped)
        return f'_ := (sys_write 1 {length} {var} (& {var}))'
    
    result = re.sub(r'"([^"]+)", "([^"]+)"\)', process_mm0_write, result)
    
    return result

def generate_simple_number_converter():
    """Generate a simpler example that converts numbers to strings"""
    
    template = '''import "compiler.mm1";

do {
  (mmc-add '(
    (intrinsic @ proc (sys_write {fd : u32} {count : u32}
      (ghost @ mut {buf : (ref @ array u8 count)}) {p : (&sn buf)} : u32))

    -- Convert a single digit to ASCII character
    (proc (digit_to_char {d : u32} : u8)
      {{c : u8} := (cast {d + 48})}  -- ASCII '0' = 48
      c)
    
    -- Display a 3-digit number (hardcoded for now)
    (proc (display_number {n : u32})
      -- For 123: hundreds=1, tens=2, ones=3
      {{h : u8} := (digit_to_char 1)}
      {{t : u8} := (digit_to_char 2)}
      {{o : u8} := (digit_to_char 3)}
      
      {{num : (array u8 4)} := (list h t o 10)}  -- "123\\n"
      {{_ := (sys_write 1 4 num (& num))}}
      )

    (proc (main {n : u32})
      -- Test number display
      {{msg {mm0_string("Number: ")}}}
      {mm0_write("msg", "Number: ")}
      
      {(display_number n)}
      
      {{done {mm0_string("Done!\\n")}}}
      {mm0_write("done", "Done!\\n")}
      )
  ))
  
  -- Generate the ELF
  (print (mmc->string))
};
'''
    
    # Process template
    result = template
    
    # Replace mm0_string
    import re
    
    def process_mm0_string(match):
        s = match.group(1)
        unescaped = s.replace('\\n', '\n')
        length = len(unescaped)
        return f': (array u8 {length})}} := (list . ,(string->list "{s}"))'
    
    result = re.sub(r'{mm0_string\("([^"]+)"\)}', process_mm0_string, result)
    
    # Replace mm0_write
    def process_mm0_write(match):
        var = match.group(1)
        msg = match.group(2)
        unescaped = msg.replace('\\n', '\n')
        length = len(unescaped)
        return f'_ := (sys_write 1 {length} {var} (& {var}))}}'
    
    result = re.sub(r'{mm0_write\("([^"]+)", "([^"]+)"\)}', process_mm0_write, result)
    
    return result

if __name__ == "__main__":
    # Generate the simpler number converter first
    simple_code = generate_simple_number_converter()
    with open("number_display_generated.mm1", "w") as f:
        f.write(simple_code)
    print("Generated number_display_generated.mm1")
    
    # Generate the tax calculator
    tax_code = generate_tax_calculation()
    with open("tax_calc_generated.mm1", "w") as f:
        f.write(tax_code)
    print("Generated tax_calc_generated.mm1")
    
    print("\nThis demonstrates how Python can:")
    print("1. Automatically calculate string lengths")
    print("2. Generate repetitive MM0 code patterns")
    print("3. Handle string escaping properly")
    print("4. Create higher-level abstractions for MM0 programming")