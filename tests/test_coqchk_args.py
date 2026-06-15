"""Regression tests for coqchk argument handling.

These guard against the bug where shared load-path options (-Q/-R/-I/-coqlib)
were stripped from the coqchk command line because coqchk's --help was queried
the same way as coqc's (`-q --help`), which coqchk rejects, yielding an empty
help string and causing those options to be misclassified as "coqc-only".

See https://github.com/rocq-community/run-coq-bug-minimizer/issues/53 and the
discussion on https://github.com/rocq-prover/rocq/issues/22125.
"""

from coq_tools.coq_version import (
    get_multiple_help_tags,
    get_single_help_tags,
    group_coq_args_split_recognized,
)

# coqchk's actual usage text (see checker/coqchk_main.ml print_usage_channel).
COQCHK_HELP = """Usage: coqchk <options> modules

coqchk options are:

  -Q dir coqdir               map physical dir to logical coqdir
  -R dir coqdir               synonymous for -Q
  -coqlib dir                 set coqchk's standard library location
  -boot                       don't initialize the library paths automatically

  -admit module               load module and dependencies without checking
  -norec module               check module but admit dependencies without checking

  -d (d1,..,dn)               enable specified debug messages
  -debug                      enable all debug messages
  -profile file               output profiling info to file
  -where                      print coqchk's standard library location and exit
  -v, --version               print coqchk version and exit
  -o, --output-context        print the list of assumptions
  -m, --memory                print the maximum heap size
  -silent                     disable trace of constants being checked

  -impredicative-set          set sort Set impredicative
  -indices-matter             levels of indices (and nonuniform parameters)
  -bytecode-compiler (yes|no) enable the vm_compute reduction machine (default is no)

  -h, --help                  print this list of options
"""

# An abbreviated coqc help, enough to recognize the coqc-only options used below.
COQC_HELP = """  -Q dir coqdir          recursively map
  -R dir coqdir          map
  -I dir                 ml include
  -coqlib dir            set coqlib
  -w w                   configure warnings
  -native-compiler arg   native compilation
  -top coqdir            set the toplevel name
"""


def test_coqchk_help_recognizes_load_path_options():
    multiple = get_multiple_help_tags(COQCHK_HELP)
    single = get_single_help_tags(COQCHK_HELP)
    assert multiple.get("-Q") == 3
    assert multiple.get("-R") == 3
    assert multiple.get("-coqlib") == 2
    assert multiple.get("-admit") == 2
    assert "-silent" in single
    assert "-boot" in single


def _filter_like_find_bug(args, coqchk_help, coqc_help):
    """Mirror the two-stage filtering done in find_bug.py for coqchk args."""
    recognized, unrecognized = group_coq_args_split_recognized(args, coqchk_help)
    coqc_only, unrecognized = group_coq_args_split_recognized(unrecognized, coqc_help)
    return [arg for group in recognized for arg in group] + unrecognized, coqc_only


def test_load_path_options_survive_filtering():
    args = [
        "-coqlib", "/lib/coq/",
        "-w", "-foo",
        "-native-compiler", "ondemand",
        "-top", "MyMod",
        "-Q", "/p/Coqprime", "Coqprime",
        "-R", "/p/Bignums", "Bignums",
        "-silent",
    ]
    final, coqc_only = _filter_like_find_bug(args, COQCHK_HELP, COQC_HELP)
    # shared load-path / kernel options must be kept
    assert "-Q" in final and "Coqprime" in final
    assert "-R" in final and "Bignums" in final
    assert final[:2] == ["-coqlib", "/lib/coq/"]
    assert "-silent" in final
    # coqc-only options must still be stripped (coqchk would reject them)
    assert "-w" not in final
    assert "-native-compiler" not in final
    assert "-top" not in final
    assert ("-w", "-foo") in coqc_only
    assert ("-top", "MyMod") in coqc_only


def test_empty_help_would_drop_load_path_regression():
    """With empty coqchk help (the old buggy behavior), -Q/-R get dropped.

    This documents the failure mode the fix avoids: when coqchk's help is
    empty, only the hard-coded -coqlib survives and -Q/-R are misclassified as
    coqc-only.
    """
    args = ["-Q", "/p/Coqprime", "Coqprime", "-R", "/p/Bignums", "Bignums"]
    final, coqc_only = _filter_like_find_bug(args, "", COQC_HELP)
    assert "-Q" not in final
    assert "-R" not in final
    assert ("-Q", "/p/Coqprime", "Coqprime") in coqc_only
