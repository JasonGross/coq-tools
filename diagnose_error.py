from __future__ import with_statement
import os, sys, tempfile, subprocess, re, time, math, glob
from memoize import memoize

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

# from http://stackoverflow.com/questions/377017/test-if-executable-exists-in-python
@memoize
def which(program):
    def is_exe(fpath):
        return os.path.isfile(fpath) and os.access(fpath, os.X_OK)

    def ext_candidates(fpath):
        yield fpath
        for ext in os.environ.get("PATHEXT", "").split(os.pathsep):
            yield fpath + ext

    fpath, fname = os.path.split(program)
    if fpath:
        if is_exe(program):
            return program
    else:
        for path in os.environ["PATH"].split(os.pathsep):
            exe_file = os.path.join(path, program)
            for candidate in ext_candidates(exe_file):
                if is_exe(candidate):
                    return candidate

    return None

@memoize
def get_timeout_prog():
    TIMEOUT_PROG = 'timeout'
    p = subprocess.Popen([TIMEOUT_PROG, '1', 'true'], stderr=subprocess.STDOUT, stdout=subprocess.PIPE)
    (stdout, stderr) = p.communicate()
    if 'ERROR' in stdout:
        TIMEOUT_PROG = which('timeout')
    return TIMEOUT_PROG if TIMEOUT_PROG is not None else 'timeout'

def memory_robust_Popen(*args, **kwargs):
    while True:
        try:
            return subprocess.Popen(*args, **kwargs)
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
    if timeout > 0:
        # Windows sometimes doesn't like cygwin's timeout, so hack around it
        TIMEOUT_PROG = get_timeout_prog()
        start = time.time()
        p = memory_robust_Popen([TIMEOUT_PROG, str(timeout), coqc, '-q'] + list(coqc_args) + [file_name], stderr=subprocess.STDOUT, stdout=subprocess.PIPE)
    else:
        start = time.time()
        p = memory_robust_Popen([coqc, '-q'] + list(coqc_args) + [file_name], stderr=subprocess.STDOUT, stdout=subprocess.PIPE)
    (stdout, stderr) = p.communicate()
    finish = time.time()
    if TIMEOUT is None:
        TIMEOUT = 2 * max((1, int(math.ceil(finish - start))))
    for pre in ('', '.'):
        for ext in (file_name[-2:], '.glob', '.vo', '.d', '.v.d', '.aux'):
            name = ''.join((os.path.dirname(file_name[:-2]), os.sep, pre, os.path.basename(file_name[:-2]), ext))
            if os.path.exists(name):
                os.remove(name)
    ## remove instances of the file name
    #stdout = stdout.replace(os.path.basename(file_name[:-2]), 'Top')
    return clean_output(stdout)
