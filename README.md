# ANTLR2PNF: ANTLR4 to Perses Normal Form converter

This script accepts an ANTLR4 grammar file and converts the parser rules
within that file into Perses Normal Form (PNF). PNF can be used to assist
in test case reduction as presented in:

> [Perses: Syntax-Guided Program Reduction](https://dl.acm.org/citation.cfm?id=3180236)  
> Chengnian Sun, Yuanbo Li, Qirun Zhang, Tianxiao Gu, Zhendong Su  
> ICSE 2018

The resulting grammars should generally be valid ANTLR4 grammars as well.

## Usage

    ./antlr2pnf.py <path to .g4 file> <name of starting rule>

This will print out the modified grammar (also in ANTLR4 form).
The modified grammar will have the new starting rule `pnf_start`.

## Notes

Minor modifications were made to the process, as the printed algorithm
doesn't quite produce grammars in PNF form. Errors in this implementation
are solely my own. Where possible, variable names match the names in the
paper.

Implementation of quantifying optionals can be slow and a bit dependent
the random ordering of rules. If it seems to be taking a long time on a
grammar, simply killing the process and rerunning it usually does the
trick. This has been tested on a handful of the grammars in the official
ANTLR4 grammar repository.

