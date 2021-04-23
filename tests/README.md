**positive and negative tests for mm0 and mmu**

This folder holds positive (pass folder) and negative (fail folder) tests for mm0 and mmu, inside subfolders

Those subfolders contain mm0 and mmu files that can be used to test :
- mm0 parsers (parsingMM0 and parsingBoth folder)
- mmu parsers (parsingMMU and ParsingBoth folder)
- mm0 vs mmu proofChecker (all folders):
  - parsingMM0, parsingMMU and ParsingBoth handle the parsing stage
  - matching handles match between mm0 statements and mmu directives
  - registering handles the process of recording joined mm0 statements/mmu directives to form a coherent context
  - dynamicParsing handles the behavior of a dynamic parser built on a coherent context 
  - proofchecking handles the proof checking of a (mm0, mmu) pair
