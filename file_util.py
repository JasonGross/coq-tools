import os, time
from memoize import memoize

__all__ = ["clean_v_file", "clean_extra_coq_files", "write_to_file", "read_from_file", "restore_file"]

def clean_extra_coq_files(v_file_name, extra_exts=tuple()):
    for pre in ('', '.'):
        for ext in tuple(list(extra_exts) + ['.glob', '.vo', '.d', '.v.d', '.aux']):
            name = ''.join((os.path.dirname(v_file_name[:-2]), os.sep, pre, os.path.basename(v_file_name[:-2]), ext))
            if os.path.exists(name):
                os.remove(name)

def clean_v_file(file_name):
    clean_extra_coq_files(file_name, extra_exts=('.v',))

def backup(file_name, ext='.bak'):
    if not ext:
        raise ValueError
    if os.path.exists(file_name):
        backup(file_name + ext)
        os.rename(file_name, file_name + ext)

@memoize
def memobackup(file_name, ext='.bak'):
    return backup(file_name, ext)

FILE_CACHE = {}

def write_to_file(file_name, contents, do_backup=False, backup_ext='.bak', memoize=False):
    backed_up = False
    while not backed_up:
        try:
            if do_backup:
                if memoize:
                    memobackup(file_name, ext=backup_ext)
                else:
                    backup(file_name, ext=backup_ext)
            backed_up = True
        except IOError as e:
            print('Warning: f.write(%s) failed with %s\nTrying again in 10s' % (file_name, repr(e)))
            time.sleep(10)
    written = False
    while not written:
        try:
            try:
                with open(file_name, 'w', encoding='UTF-8') as f:
                    f.write(contents)
            except TypeError:
                with open(file_name, 'w') as f:
                    f.write(contents)
            written = True
            FILE_CACHE[file_name] = (os.stat(file_name).st_mtime, contents)
        except IOError as e:
            print('Warning: f.write(%s) failed with %s\nTrying again in 10s' % (file_name, repr(e)))
            time.sleep(10)

def restore_file(file_name, backup_ext='.bak', backup_backup_ext='.unbak'):
    if not os.path.exists(file_name + backup_ext):
        raise IOError
    if os.path.exists(file_name):
        if backup_backup_ext:
            backup(file_name, backup_backup_ext)
        else:
            os.remove(file_name)
    os.rename(file_name + backup_ext, file_name)

def read_from_file(file_name):
    if file_name in FILE_CACHE.keys() and os.stat(file_name).st_mtime == FILE_CACHE[file_name][0]:
        return FILE_CACHE[file_name][1]
    try:
        with open(file_name, 'r', encoding='UTF-8') as f:
            FILE_CACHE[file_name] = (os.stat(file_name).st_mtime, f.read())
            return FILE_CACHE[file_name][1]
    except TypeError:
        with open(file_name, 'r') as f:
            FILE_CACHE[file_name] = (os.stat(file_name).st_mtime, f.read())
            return FILE_CACHE[file_name][1]
