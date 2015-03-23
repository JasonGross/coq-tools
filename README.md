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
using `-R . Foo`.  The script should be run from the main directory of
your development; there is an experimental `--directory` argument to
allow you to do otherwise.

### Examples

There is an example in the examples directory.  You can run
`run-example-1.sh` to see how the program works.  You can pass this
script the arguments `-v`, `-vv`, or `-vvv` for different levels of
verbosity.  Look at the contents of `run-example-1.sh` to see how to
invoke the program.

### Known Bugs

Note that this program can fail in mysterious ways when run using
Windows Python 2.7 under cygwin; it seems that buffering and stdin and
stderr and Popen are screwed up.  To work around this, there is a
coqtop.bat file which is chosen as the default coqtop program.
Somehow running via a .bat file makes things work.  You will probably
have to use a similar wrapper if you use a custom coqtop executable.

The `--directory` argument has poor semantics.  It should be improved.

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
