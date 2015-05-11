from __future__ import with_statement
import subprocess

__all__ = ["get_coqc_version", "get_coqtop_version", "get_coqc_help"]

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
