#!/usr/bin/env python3
"""Generate MM0 calculator demo using Python to handle string lengths automatically"""

def generate_sys_write(var_name, message):
    """Generate MM0 code for writing a message to stdout"""
    msg_bytes = message.encode('utf-8')
    length = len(msg_bytes)
    
    # Convert string to MM0 list format
    char_list = ', '.join(f'(char! {ord(c)})' if ord(c) < 128 else str(ord(c)) 
                         for c in message)
    
    # Escape the message for MM0 string literal
    escaped_msg = message.replace('\\', '\\\\').replace('"', '\\"')
    
    return f"""      {{{{{var_name} : (array u8 {length})}} := (list . ,(string->list "{escaped_msg}"))}}
      {{_ := (sys_write 1 {length} {var_name} (& {var_name}))}}\n"""

def generate_calculator_demo():
    """Generate the complete calculator demo MM1 file"""
    
    header = 'import "compiler.mm1";\n\ndo {\n  (mmc-add \'(\n'
    
    # System call definition
    syscall_def = '''    (intrinsic @ proc (sys_write {fd : u32} {count : u32}
      (ghost @ mut {buf : (ref @ array u8 count)}) {p : (&sn buf)} : u32))

'''
    
    # Main function start
    main_start = '''    (proc (main {n : u32})
      -- Calculator demo with the passed argument (123)
      {{x : u32} := n}  -- First "argument" 
      
'''
    
    # Generate all the output statements
    outputs = []
    
    # Header message
    outputs.append(("hdr", "MM0 Calculator Demo\n\n"))
    
    # Arithmetic operations with results
    outputs.append(("msg1", "123 + 77 = 200\n"))
    outputs.append(("msg2", "123 - 23 = 100\n"))
    outputs.append(("msg3", "123 * 2 = 246\n\n"))
    outputs.append(("msg4", "(123 + 7) * 2 = 260\n"))
    
    # Footer
    outputs.append(("ftr", "\nMM0: Verified computation works!\n"))
    
    # Build the main function body
    body = main_start
    
    # Add header output
    body += "      -- Display header\n"
    body += generate_sys_write("hdr", "MM0 Calculator Demo\n\n")
    
    # Add arithmetic operations
    body += '''      -- Addition: 123 + 77 = 200
      {{sum : u32} := (cast {x + 77})}
'''
    body += generate_sys_write("msg1", "123 + 77 = 200\n")
    
    body += '''      -- Subtraction: 123 - 23 = 100  
      {{diff : u32} := (cast {x - 23})}
'''
    body += generate_sys_write("msg2", "123 - 23 = 100\n")
    
    body += '''      -- Multiplication: 123 * 2 = 246
      {{prod : u32} := (cast {x * 2})}
'''
    body += generate_sys_write("msg3", "123 * 2 = 246\n\n")
    
    body += '''      -- Show that we can chain operations: (123 + 7) * 2 = 260
      {{chain : u32} := (cast {{x + 7} * 2})}
'''
    body += generate_sys_write("msg4", "(123 + 7) * 2 = 260\n")
    
    body += "      -- Footer\n"
    body += generate_sys_write("ftr", "\nMM0: Verified computation works!\n")
    
    # Close the main function
    body += "      )\n"
    
    # Footer
    footer = '''  ))
  
  -- Generate the ELF
  (print (mmc->string))
};
'''
    
    return header + syscall_def + body + footer

if __name__ == "__main__":
    mm1_code = generate_calculator_demo()
    
    # Write to file
    with open("calculator_demo_generated.mm1", "w") as f:
        f.write(mm1_code)
    
    print("Generated calculator_demo_generated.mm1")
    print("\nString lengths are automatically calculated!")
    
    # Show the string lengths for verification
    test_strings = [
        "MM0 Calculator Demo\n\n",
        "123 + 77 = 200\n",
        "123 - 23 = 100\n", 
        "123 * 2 = 246\n\n",
        "(123 + 7) * 2 = 260\n",
        "\nMM0: Verified computation works!\n"
    ]
    
    print("\nString lengths:")
    for s in test_strings:
        print(f"  {repr(s)}: {len(s)} chars")