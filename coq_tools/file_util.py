import os
import tempfile
import time

from . import util
from .memoize import memoize

__all__ = [
    "clean_v_file",
    "clean_extra_coq_files",
    "write_bytes_to_file",
    "read_bytes_from_file",
    "write_to_file",
    "read_from_file",
    "restore_file",
]


def clean_extra_coq_files(v_file_name, extra_exts=tuple()):
    for pre in ("", "."):
        for ext in tuple(list(extra_exts) + [".glob", ".vo", ".d", ".v.d", ".aux", ".vos", ".vok"]):
            name = "".join((os.path.dirname(v_file_name[:-2]), os.sep, pre, os.path.basename(v_file_name[:-2]), ext))
            if os.path.exists(name):
                os.remove(name)


def clean_v_file(file_name):
    clean_extra_coq_files(file_name, extra_exts=(".v",))


def backup(file_name, ext=".bak"):
    if not ext:
        raise ValueError
    if os.path.exists(file_name):
        backup(file_name + ext, ext=ext)
        os.rename(file_name, file_name + ext)


@memoize
def memobackup(file_name, ext=".bak"):
    return backup(file_name, ext)


FILE_CACHE = {}


def write_bytes_to_file(file_name, contents, do_backup=False, backup_ext=".bak", memoize=False):
    assert contents is bytes(contents)
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
            print("Warning: f.write(%s) failed with %s\nTrying again in 10s" % (file_name, repr(e)))
            time.sleep(10)
    written = False
    while not written:
        try:
            with tempfile.NamedTemporaryFile(mode="wb", dir=os.path.dirname(file_name), prefix=os.path.basename(file_name) + ".", delete=False) as f:
                f.write(contents)
                temp_file_name = f.name
            os.rename(temp_file_name, file_name)
            written = True
            FILE_CACHE[file_name] = (os.stat(file_name).st_mtime, contents)
        except IOError as e:
            print("Warning: f.write(%s) failed with %s\nTrying again in 10s" % (file_name, repr(e)))
            time.sleep(10)


def write_to_file(file_name, contents, *args, **kwargs):
    return write_bytes_to_file(file_name, contents.replace("\n", os.linesep).encode("utf-8"), *args, **kwargs)


def restore_file(file_name, backup_ext=".bak", backup_backup_ext=".unbak"):
    if not os.path.exists(file_name + backup_ext):
        raise IOError
    if os.path.exists(file_name):
        if backup_backup_ext:
            backup(file_name, backup_backup_ext)
        else:
            os.remove(file_name)
    os.rename(file_name + backup_ext, file_name)


def read_bytes_from_file(file_name):
    if file_name in FILE_CACHE.keys() and os.stat(file_name).st_mtime == FILE_CACHE[file_name][0]:
        return FILE_CACHE[file_name][1]
    with open(file_name, "rb") as f:
        FILE_CACHE[file_name] = (os.stat(file_name).st_mtime, f.read())
        return FILE_CACHE[file_name][1]


def read_from_file(file_name):
    return util.normalize_newlines(read_bytes_from_file(file_name).decode("utf-8"))
