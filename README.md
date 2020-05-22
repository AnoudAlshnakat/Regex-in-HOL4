# Regex-in-HOL4
This project is based on the regular expresion matching programs described in the paper "A Play on Regular Expressions - Functional Pearl" by Fischer et al. Three of the implementations, namely the default matcher, marked regular expressions matcher, and cached marked regular expressions matcher. Each of the previous implementations was formally formalised and its correctness was proved using the theorm prover HOL4.

SML code was later synthesised from HOL4 EmitML, and an SML library was executed and tested from the extracted code.

### Install and build
1. To run this project if you have `Emacs`, `HOL4` and `PolyML` installed. 
2. Clone the project.
3. Change the path in the Holmakefile wherever the directory HOL got installed.
4. build it using `Holmake`, it will take approximatly 5 seconds.
``
real	0m5,850s
user	0m5,094s
sys	 0m0,627s.
``

### Files contents
`RegScript.sml`: Contains regular expressions and their matchers.
`reggenScript.sml`: Contains the code required to extract the code.
`reggenML.sml	`	: Contains the code that got synthesised from HOL4 implementation to SML.
`regLib.sml	`: The library of the generated code.
`test.sml` and `Performance_test.sml` : SML files for testing.


### HOL4 vs SML test.
1. To test the definitions and the theorms or to play with the proofs you can open the file `RegScript.sml` and test it in HOL mode of emacs. 
2. Thesting the generated SML code and library should be in SML REPL mode of Emacs, two optional files are there:
 a. `test.sml` where you can test various regex and strings with your favourite matchers.
 b. `Performance_test.sml` this file contains a function that generates all combinations of the a charachter list and test it against the four matchers.

### For more explaination
Please check the project documentation to gain a better knowledge of what has been done and the steps followed.

## Paper source
[Fischer, S., Huch, F. and Wilke, T., 2010, September. A play on regular expressions: functional pearl. In Proceedings of the 15th ACM SIGPLAN international conference on Functional programming (pp. 357-368).](https://dl.acm.org/doi/abs/10.1145/1863543.1863594).
