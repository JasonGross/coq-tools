import os

__all__ = ["clean_v_file", "clean_extra_coq_files"]

def clean_extra_coq_files(v_file_name, extra_exts=tuple()):
    for pre in ('', '.'):
        for ext in tuple(list(extra_exts) + ['.glob', '.vo', '.d', '.v.d', '.aux']):
            name = ''.join((os.path.dirname(v_file_name[:-2]), os.sep, pre, os.path.basename(v_file_name[:-2]), ext))
            if os.path.exists(name):
                os.remove(name)

def clean_v_file(file_name):
    clean_extra_coq_files(file_name, extra_exts=('.v',))
