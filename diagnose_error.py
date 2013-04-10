from __future__ import with_statement
import os, sys, tempfile, subprocess, re

__all__ = ["has_error", "get_error_line_number", "make_reg_string", "get_coq_output"]

DEFAULT_ERROR_REG_STRING = 'File "[^"]+", line ([0-9]+), characters [0-9-]+:\n([^\n]+)'
DEFAULT_ERROR_REG_STRING_GENERIC = 'File "[^"]+", line ([0-9]+), characters [0-9-]+:\n(%s)'

def has_error(output, reg_string=DEFAULT_ERROR_REG_STRING):
    """Returns True if the coq output encoded in output has an error
    matching the given regular expression, False otherwise.
    """
    errors = re.search(reg_string, output)
    if errors:
        return True
    else:
        return False

def get_error_line_number(output, reg_string=DEFAULT_ERROR_REG_STRING):
    """Returns the line number that the error matching reg_string
    occured on.

    Precondition: has_error(output, reg_string)
    """
    return int(re.search(reg_string, output).groups()[1])

def get_error_string(output, reg_string=DEFAULT_ERROR_REG_STRING):
    """Returns the error string of the error matching reg_string.

    Precondition: has_error(output, reg_string)
    """
    return re.search(reg_string, output).groups()[0]

def make_reg_string(output):
    """Returns a regular expression for matching the particular error
    in output.

    Precondition: has_error(output)
    """
    return DEFAULT_ERROR_REG_STRING_GENERIC % get_error_string(output)

def get_coq_output(contents):
    """Returns the coqc output of running through the given
    contents."""
    with tempfile.NamedTemporaryFile(suffix='.v', delete=False) as f:
        f.write(contents)
        file_name = f.name
    p = subprocess.Popen(['coqc', '-q', file_name], stderr=subprocess.PIPE)
    (stdout, stderr) = p.communicate()
    return stderr
