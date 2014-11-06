* Use `abstract admit` rather than `admit` for coq-trunk

* Add continuous integration and an actual test suite

* Reduce files before inlining them (or add an option to do so), and
  inline incrementally

* Try using delta-debugging, and being smarter about ordering of
  removals

* Remember timing information for definitions, so we can be smart
  about prioritizing things that take a long time.

* Consider skipping changes that make compilation much slower (e.g.,
  removing a quick-path instance).  Maybe make a tuning parameter for
  how much size needs to be reduced to accept a given reduction in
  speed.

* Deal with `Load` better

* Rename "hint removal" to something more accurate

* Add an option for doing the aggressive thing first

* Interleave "hint" removal and definition removal

* Print out the last few lines of the file around the error in the
  case that the error changes and it causes a catastrophic
  error. (e.g., if splitting the file to definitions changes the error
  message)

* Add a mode where only `Import`s/`Export`s are removed, for
  minimizing the dependencies of a file.  Write a wrapper around this
  mode to check if all dependencies are used.

* Put back support for absolutizing mod and modtype, behind a
  command-line flag.  See also [7d82914e7bc302c19d23f19399f3199c6b9cc3e7](https://github.com/JasonGross/coq-bug-finder/commit/7d82914e7bc302c19d23f19399f3199c6b9cc3e7),
  [Coq Bug 3756](https://coq.inria.fr/bugs/show_bug.cgi?id=3756), and [#3](https://github.com/JasonGross/coq-bug-finder/issues/3).

* Use argparse `action='append'` as per
  [stack overflow](http://stackoverflow.com/questions/26768253/how-can-i-make-pythons-argparse-accept-any-number-of-r-a-bs-and-aggregate-t?noredirect=1#comment42119360_26768253)

* Add a command line flag to use `coqtop -load-vernac-source` and/or
  `coqtop -compile` as coqc.  Workaround: use the following script to
  pass to `--coqc`:

```bash
#!/bin/bash
function strip_v() {
    for i in "$@"
    do
        j="${i%.*}"
        if [ "$j.v" = "$i" ]; then
            echo "-load-vernac-source" # or -compile
            echo "$j"
        else
            echo "$j"
        fi

    done
}

cd "$(dirname "$0")"

exec ./hoqtop $(strip_v "$@")
```
