coq-bug-finder
==============

Some scripts to help construct small reproducing examples of bugs.

The script find-bug.py is the main program; run `find-bug.py -h` to
see the options.  The script will ask you two questions: whether or
not it successfully determined the error you're seeking to reproduce,
and whether or not it created a regular expression which captures that
error.  After that, it will run without user input until it finishes.

There is an example in the examples directory.  You can run
`run-example-1.sh` to see how the program works.  You can pass this
script the arguments `-v`, `-vv`, or `-vvv` for different levels of
verbosity.  Look at the contents of `run-example-1.sh` to see how to
invoke the program.

Currently, the program does not work well with non-flat file layouts.
If you want me to add this feature, email me or create an issue on
github with a link to a non-flat repo, and a file in that repo with a
bug, and I will work to make my script work with that file.
Currently, getting this to work well is blocking on [having better
namespacing](https://coq.inria.fr/bugs/show_bug.cgi?id=3171).

Note that this program can fail in mysterious ways when run using
Windows Python 2.7 under cygwin; it seems that buffering and stdin and
stderr and Popen are screwed up.  To work around this, there is a
coqtop.bat file which is chosen as the default coqtop program.
Somehow running via a .bat file makes things work.  You will probably
have to use a similar wrapper if you use a custom coqtop executable.
