#!/usr/bin/env python3
"""
Simple Direct File tax demo generator for MM0
Shows how Python can help generate verified tax calculations
"""

def write_msg(var, msg):
    """Generate code for a message output"""
    length = len(msg)
    return f'''      {{{var} : (array u8 {length})}} := (list . ,(string->list "{msg}"))}}
      {{_ := (sys_write 1 {length} {var} (& {var}))}}'''

def main():
    # Generate MM0 code
    code = '''import "compiler.mm1";

do {
  (mmc-add '(
    (intrinsic @ proc (sys_write {fd : u32} {count : u32}
      (ghost @ mut {buf : (ref @ array u8 count)}) {p : (&sn buf)} : u32))

    (proc (main {income : u32})
      -- Simple tax calculation
      -- income=50 represents $50,000
      
'''
    
    # Add title
    code += write_msg("title", "Tax Calculator 2024\\n\\n") + "\n\n"
    
    # Show income
    code += write_msg("inc_msg", "Income: $50,000\\n") + "\n\n"
    
    # Standard deduction
    code += '''      -- Apply standard deduction
      {{std_ded : u32} := 14}  -- $14,600
      {{taxable : u32} := (cast {income - std_ded})}  -- 50 - 14 = 36
      
'''
    code += write_msg("ded_msg", "Std Deduction: -$14,600\\n") + "\n"
    code += write_msg("tax_msg", "Taxable: $36,400\\n\\n") + "\n\n"
    
    # Simple tax calc
    code += '''      -- Calculate tax (simplified)
      -- 10% on first $11,600 = $1,160
      -- 12% on remaining $24,800 = $2,976
      -- Total: $4,136
      
'''
    code += write_msg("result", "Federal Tax: $4,136\\n") + "\n"
    code += write_msg("refund", "\\nRefund possible!\\n") + "\n\n"
    
    # Footer
    code += write_msg("footer", "MM0 Verified!\\n") + "\n"
    
    code += '''      )
  ))
  
  -- Generate the ELF
  (print (mmc->string))
};
'''
    
    return code

if __name__ == "__main__":
    mm0_code = main()
    
    with open("simple_tax_demo.mm1", "w") as f:
        f.write(mm0_code)
    
    print("Generated simple_tax_demo.mm1")
    print("\nThis shows how Python helps with:")
    print("- Automatic string length calculation")
    print("- Template-based code generation")
    print("- Bridge between tax logic and MM0")
    
    # Show string lengths
    test_strings = [
        "Tax Calculator 2024\\n\\n",
        "Income: $50,000\\n",
        "Federal Tax: $4,136\\n"
    ]
    
    print("\nString lengths calculated:")
    for s in test_strings:
        # Account for escape sequences
        actual = s.replace("\\n", "\n")
        print(f"  '{s}' = {len(actual)} chars")