from __future__ import with_statement
import os, sys, tempfile, subprocess, re, time
from memoize import memoize

__all__ = ["has_error", "get_error_line_number", "make_reg_string", "get_coq_output", "get_error_string"]

DEFAULT_ERROR_REG_STRING = 'File "[^"]+", line ([0-9]+), characters [0-9-]+:\n((?:.|\n)+)'
DEFAULT_ERROR_REG_STRING_GENERIC = 'File "[^"]+", line ([0-9]+), characters [0-9-]+:\n(%s)'

def clean_output(output):
    return output.replace('\r\n', '\n').replace('\n\r', '\n').replace('\r', '\n')

@memoize
def has_error(output, reg_string=DEFAULT_ERROR_REG_STRING):
    """Returns True if the coq output encoded in output has an error
    matching the given regular expression, False otherwise.
    """
    errors = re.search(reg_string, output)
    if errors:
        return True
    else:
        return False

@memoize
def get_error_line_number(output, reg_string=DEFAULT_ERROR_REG_STRING):
    """Returns the line number that the error matching reg_string
    occured on.

    Precondition: has_error(output, reg_string)
    """
    return int(re.search(reg_string, output).groups()[0])

@memoize
def get_error_string(output, reg_string=DEFAULT_ERROR_REG_STRING):
    """Returns the error string of the error matching reg_string.

    Precondition: has_error(output, reg_string)
    """
    return re.search(reg_string, output).groups()[1]

@memoize
def make_reg_string(output):
    """Returns a regular expression for matching the particular error
    in output.

    Precondition: has_error(output)
    """
    error_string = get_error_string(output)
    if 'Universe inconsistency' in error_string:
        re_string = re.sub(r'(Universe\\ inconsistency.*) because(.|\n)*',
                           r'\1 because.*',
                           re.escape(error_string))
        re_string = re.sub(r'(\s)[^\s]+?\.([0-9]+)',
                           r'\1[^\s]+?\.\2',
                           re_string)
    else:
        re_string = re.escape(error_string)
    re_string = re.sub(r'[0-9]+',
                       r'[0-9]+',
                       re_string)
    return DEFAULT_ERROR_REG_STRING_GENERIC % re_string

LAST_TIMEOUT=None

@memoize
def get_coq_output(coqc, contents, use_timeout):
    """Returns the coqc output of running through the given
    contents."""
    global LAST_TIMEOUT
    with tempfile.NamedTemporaryFile(suffix='.v', delete=False) as f:
        f.write(contents)
        file_name = f.name
    start = time.time()
    if LAST_TIMEOUT is None or not use_timeout:
        p = subprocess.Popen([coqc, '-q', file_name], stderr=subprocess.STDOUT, stdout=subprocess.PIPE)
    else:
        p = subprocess.Popen(['timeout', str(max(5, int(2 * LAST_TIMEOUT))), coqc, '-q', file_name], stderr=subprocess.STDOUT, stdout=subprocess.PIPE)
    (stdout, stderr) = p.communicate()
    end = time.time()
    if LAST_TIMEOUT is None or start - end <= 1.5 * LAST_TIMEOUT:
        LAST_TIMEOUT = start - end
    for names in (file_name[:-2] + '.glob',
                  file_name[:-2] + '.vo',
                  file_name[:-2] + '.d',
                  file_name[:-2] + '.v.d',
                  file_name):
        if os.path.exists(name):
            os.remove(name)
    return clean_output(stdout)
