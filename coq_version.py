from __future__ import with_statement
import subprocess, tempfile
from file_util import clean_v_file
from memoize import memoize

__all__ = ["get_coqc_version", "get_coqtop_version", "get_coqc_help", "get_coq_accepts_top"]

def get_coqc_version(coqc):
    p = subprocess.Popen([coqc, "-v"], stderr=subprocess.STDOUT, stdout=subprocess.PIPE)
    (stdout, stderr) = p.communicate()
    return stdout.replace('The Coq Proof Assistant, version ', '').replace('\r\n', ' ').replace('\n', ' ').strip()

def get_coqc_help(coqc):
    p = subprocess.Popen([coqc, "-help"], stderr=subprocess.STDOUT, stdout=subprocess.PIPE)
    (stdout, stderr) = p.communicate()
    return stdout.strip()

def get_coqtop_version(coqtop):
    p = subprocess.Popen([coqtop], stderr=subprocess.PIPE, stdout=subprocess.PIPE, stdin=subprocess.PIPE)
    (stdout, stderr) = p.communicate()
    return stdout.replace('Welcome to Coq ', '').replace('\r\n', ' ').replace('\n', ' ').strip()

@memoize
def get_coq_accepts_top(coqc):
    temp_file = tempfile.NamedTemporaryFile(suffix='.v', dir='.', delete=True)
    temp_file_name = temp_file.name
    p = subprocess.Popen([coqc, "-top", "Top", temp_file_name], stderr=subprocess.STDOUT, stdout=subprocess.PIPE)
    (stdout, stderr) = p.communicate()
    temp_file.close()
    clean_v_file(temp_file_name)
    return '-top: no such file or directory' not in stdout
