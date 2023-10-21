[![Build Status](https://github.com/JasonGross/coq-tools/workflows/CI/badge.svg?branch=master)](https://github.com/JasonGross/coq-tools/actions?query=branch%3Amaster)
[![PyPI version](https://badge.fury.io/py/coq-tools.svg)](https://badge.fury.io/py/coq-tools)

coq-tools
==============

Some scripts to help manipulate Coq developments

coq-bug-minimizer
-----------------

Some scripts to help construct small reproducing examples of bugs.

The script `find-bug.py` is the main program; run `find-bug.py -h` to
see the options.  The script will ask you two questions: whether or
not it successfully determined the error you're seeking to reproduce,
and whether or not it created a regular expression which captures that
error.  After that, it will run without user input until it finishes.

### Usage

Standard usage is to invoke with the buggy file name and the output
(minimized) file name:

```
python find-bug.py BUGGY_FILE.v OUTPUT_FILE.v
```

You can add `-v` for a more verbose output.

If you are using a non-system version of Coq, you can pass `--coqtop
/path/to/coqtop` and `--coqc /path/to/coqc`.  If you pass `-R . Foo`
to, say, `coq_makefile`, you can inform `find-bug.py` of this fact
using `-R . Foo`.

### Examples

There is an example in the examples directory.  You can run
`run-example-01.sh` to see how the program works.  You can pass this
script the arguments `-v`, `-vv`, or `-vvv` for different levels of
verbosity.  Look at the contents of `run-example-01.sh` to see how to
invoke the program.

### Known Bugs

Note that this program can fail in mysterious ways when run using
Windows Python 2.7 under cygwin; it seems that buffering and stdin and
stderr and Popen are screwed up.  To work around this, there is a
coqtop.bat file which is chosen as the default coqtop program.
Somehow running via a .bat file makes things work.  You will probably
have to use a similar wrapper if you use a custom coqtop executable.

Additionally, quirks in module name resolution can result in inlining
failures (see https://github.com/JasonGross/coq-tools/issues/16), and
global side effects of `Require` can also result in failures (see
https://github.com/JasonGross/coq-tools/issues/41).

### Publications

- [Jason Gross, Théo Zimmermann, Miraya Poddar-Agrawal, and Adam Chlipala. Automatic test-case reduction in proof assistants: A case study in Coq. ITP 2022](https://jasongross.github.io/publications/#2022-itp-coq-bug-minimizer)
- [Jason Gross. Coq Bug Minimizer, CoqPL 2015](https://jasongross.github.io/publications/#coqpl-15-coq-bug-minimizer)

minimize-requires
-----------------

The script `minimize-requires.py` can be used to remove unneeded `Require`
statements.  Run `minimize-requires.py -h` to see the options.

### Usage

Standard usage is to run
```
minimize-requires.py some-file1.v some-file2.v ... --in-place .bak
```
or, if you want to minimize an entire project,
```
minimize-requires.py --all -f _CoqProject
```
(you can add `--in-place .bak` if you want to save backup files)

proof-using-helper
------------------

The script `proof-using-helper.py` is the main program; run
`proof-using-helper.py -h` to see the options.

### Usage

Standard usage is to invoke with the any `-R` arguments passed to Coq,
and either pipe the output of `make quick` with `Global Set Suggest Proof Using`
on, to this script, or to give it a file containing said output.

```
make quick -j -k | tee -a proof_using.log
python /path/to/proof-using-helper.py proof_using.log
```

You can add `-v` for a more verbose output.
