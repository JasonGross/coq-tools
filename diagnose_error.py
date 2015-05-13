from __future__ import with_statement
import os, sys, tempfile, subprocess, re, time, math, glob, threading
from memoize import memoize
from file_util import clean_v_file

__all__ = ["has_error", "get_error_line_number", "make_reg_string", "get_coq_output", "get_error_string", "get_timeout", "reset_timeout"]

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
    error_string = get_error_string(output).strip()
    if 'Universe inconsistency' in error_string:
        re_string = re.sub(r'(Universe\\ inconsistency.*) because(.|\n)*',
                           r'\1 because.*',
                           re.escape(error_string))
        re_string = re.sub(r'(\s)[^\s]+?\.([0-9]+)',
                           r'\1[^\s]+?\.\2',
                           re_string)
    elif 'Unsatisfied constraints' in error_string:
        re_string = re.sub(r'Error\\:\\ Unsatisfied\\ constraints\\:.*(?:\n.+)*.*\\\(maybe\\ a\\ bugged\\ tactic\\\)',
                           r'Error\:\ Unsatisfied\ constraints\:.*(?:\\n.+)*.*\(maybe\ a\ bugged\ tactic\)',
                           re.escape(error_string),
                           re.DOTALL)
    elif 'Unable to satisfy the following constraints' in error_string:
        re_string = re.sub(r'Error\\:\\ Unable\\ to\\ satisfy\\ the\\ following\\ constraints\\:.*(?:\n.*)*',
                           r'Error\:\ Unable\ to\ satisfy\ the\ following\ constraints\:.*(?:\\n.*)*',
                           re.escape(error_string),
                           re.DOTALL)
    else:
        re_string = re.escape(error_string)
    re_string = re.sub(r'tmp[A-Za-z_\d]+',
                       r'tmp[A-Za-z_\d]+',
                       re_string)
    if r'Universe\ instance\ should\ have\ length\ ' not in re_string:
        re_string = re.sub(r'[\d]+',
                           r'[\d]+',
                           re_string)
    return DEFAULT_ERROR_REG_STRING_GENERIC % re_string

TIMEOUT = None

def get_timeout():
    return TIMEOUT

def reset_timeout():
    global TIMEOUT
    TIMEOUT = None

def timeout_Popen_communicate(*args, **kwargs):
    ret = { 'value' : ('', '') }
    timeout = kwargs.get('timeout')
    del kwargs['timeout']
    p = subprocess.Popen(*args, **kwargs)

    def target():
        ret['value'] = p.communicate()

    thread = threading.Thread(target=target)
    thread.start()

    thread.join(timeout)
    if not thread.is_alive():
        return ret['value']

    p.terminate()
    thread.join()
    return tuple(map((lambda s: (s if s else '') + '\nTimeout!'), ret['value']))


def memory_robust_timeout_Popen_communicate(*args, **kwargs):
    while True:
        try:
            return timeout_Popen_communicate(*args, **kwargs)
        except OSError as e:
            print('Warning: subprocess.Popen%s%s failed with %s\nTrying again in 10s' % (repr(tuple(args)), repr(kwargs), repr(e)))
            time.sleep(10)

@memoize
def get_coq_output(coqc, coqc_args, contents, timeout):
    """Returns the coqc output of running through the given
    contents."""
    global TIMEOUT
    if timeout < 0 and TIMEOUT is not None:
        return get_coq_output(coqc, coqc_args, contents, TIMEOUT)
    with tempfile.NamedTemporaryFile(suffix='.v', delete=False) as f:
        f.write(contents)
        file_name = f.name
    start = time.time()
    cmds = [coqc, '-q'] + list(coqc_args) + [file_name]
    (stdout, stderr) = memory_robust_timeout_Popen_communicate(cmds, stderr=subprocess.STDOUT, stdout=subprocess.PIPE, timeout=(timeout if timeout > 0 else None))
    finish = time.time()
    if TIMEOUT is None:
        TIMEOUT = 2 * max((1, int(math.ceil(finish - start))))
    clean_v_file(file_name)
    ## remove instances of the file name
    #stdout = stdout.replace(os.path.basename(file_name[:-2]), 'Top')
    return (clean_output(stdout), tuple(cmds))
