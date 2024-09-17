#!/usr/bin/env python3
# invoke as
# cat /path/to/coq/doc/tools/docgram/fullGrammar | ./generate-full-grammar.py > coq_full_grammar.py
import sys, re

print(
    r"""# autogenerated by cat /path/to/coq/doc/tools/docgram/fullGrammar | ./generate-full-grammar.py > coq_full_grammar.py
__all__ = ["COQ_GRAMMAR_TOKENS"]

COQ_GRAMMAR_TOKENS = %s"""
    % repr(sorted(set(i.strip('"') for i in re.findall('"[a-zA-Z_][^"]*"', sys.stdin.read())))).replace(" ", "\n")
)
