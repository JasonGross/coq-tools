import os, sys, re
from difflib import SequenceMatcher
from typing import List
from .argparse_compat import argparse

__all__ = [
    "prompt",
    "yes_no_prompt",
    "b",
    "s",
    "cmp_compat",
    "PY3",
    "BooleanOptionalAction",
    "argparse",
    "raw_input",
    "re_escape",
    "slice_string_at_bytes",
    "len_in_bytes",
    "shlex_quote",
    "shlex_join",
    "resource_path",
    "group_by",
]

BooleanOptionalAction = argparse.BooleanOptionalAction

SCRIPT_DIRECTORY = os.path.dirname(os.path.realpath(__file__))

if sys.version_info < (3,):
    PY3 = False

    def b(x):
        return x

    def s(x):
        return x

else:
    PY3 = True

    def b(x) -> bytes:
        if x is not None:
            return x.encode()
        return x

    def s(x) -> str:
        # Sometimes we get str rather than bytes??? cf https://gitlab.com/coq/coq/-/jobs/544269051
        if hasattr(x, "decode"):
            return x.decode("utf-8", "ignore")
        return x

    def cmp(x, y):
        if x < y:
            return -1
        if y < x:
            return 1
        return 0

    raw_input = input

if sys.version_info < (3, 7):
    # see https://bugs.python.org/issue29995
    def re_escape(*args, **kwargs):
        ret = re.escape(*args, **kwargs)
        for ch in ':"':
            ret = ret.replace("\\" + ch, ch)
        return ret

else:
    re_escape = re.escape

cmp_compat = cmp


def prompt(
    options,
    case_sensitive=False,
    strip=True,
    sep="/",
    prefix="Please enter ",
    postfix=": ",
    yes_value=True,
    yes=False,
):
    msg = prefix + sep.join(i["display"] for i in options) + postfix
    if yes:
        print(msg)
        return yes_value
    else:
        response = raw_input(msg)
        while True:
            if not case_sensitive:
                response = response.lower()
            if strip:
                response = response.strip()
            for expected in options:
                if response in expected["values"]:
                    return expected["value"]
            print(
                'Response "%s" is not one of %s'
                % (
                    response,
                    ", ".join(repr(val) for i in options for val in i["values"]),
                )
            )
            response = raw_input(msg)


def yes_no_prompt(**kwargs):
    return prompt(
        (
            {"value": True, "display": "(y)es", "values": ("y", "yes")},
            {"value": False, "display": "(n)o", "values": ("n", "no")},
        ),
        yes_value=True,
        **kwargs,
    )


# Unfortunately, coqtop -emacs -time reports character locations in
# bytes, as does the glob file, so we need to handle unicode.  Here we
# write a generic slicer based on unicode locations that works across
# versions of python
def slice_string_at_bytes(string, start=None, end=None):
    string = b(string)
    if start is None:
        start = 0
    if end is None:
        end = len(string)
    return s(string[start:end])


def len_in_bytes(string):
    return len(b(string))


def normalize_newlines(string: str) -> str:
    return string.replace("\r\n", "\n").replace("\r", "\n")


# Terminal colors (maybe something cleverer needs to be done for other
# platforms).
class colors:
    ESC = "\033"
    # Escape code doesn't render on github so we use the standard escaped escape.
    # ESC = ''

    HEADER = ESC + "[95m"
    OKBLUE = ESC + "[94m"
    OKCYAN = ESC + "[96m"
    OKGREEN = ESC + "[92m"
    WARNING = ESC + "[93m"
    FAIL = ESC + "[91m"
    ENDC = ESC + "[0m"
    BOLD = ESC + "[1m"
    UNDERLINE = ESC + "[4m"


# Colors a string a given color
# Example usage: color("Hello World!", colors.OKBLUE)
def color(str, col, on=True):
    if not on:
        return str
    else:
        return col + str + colors.ENDC


if sys.version_info < (3, 3):
    import pipes

    shlex_quote = pipes.quote
else:
    import shlex

    shlex_quote = shlex.quote

if sys.version_info < (3, 8):
    shlex_join = lambda split_command: " ".join(shlex_quote(arg) for arg in split_command)
else:
    import shlex

    shlex_join = shlex.join


def resource_path(path):
    if os.path.exists(os.path.join(SCRIPT_DIRECTORY, path)):
        return os.path.join(SCRIPT_DIRECTORY, path)
    if sys.version_info < (3, 7):
        import pkg_resources

        return pkg_resources.resource_filename("coq_tools", path)
    else:
        import importlib.resources

        return importlib.resources.path("coq_tools", path)


def group_by_iter(ls, f):
    """
    Groups elements in a list based on a given condition.

    Args:
        ls (iterable): The list of elements to be grouped.
        f (function): The condition function used for grouping.

    Returns:
        iterable: A list of lists, where each inner list represents a group of elements.
    """
    it = iter(ls)
    prev = next(it)
    cur = [prev]
    for token in it:
        if f(prev, token):
            cur.append(token)
        else:
            yield cur
            cur = [token]
        prev = token
    yield cur


def group_by(ls, f):
    """
    Groups elements in a list based on a given condition.

    Args:
        ls (list): The list of elements to be grouped.
        f (function): The condition function used for grouping.

    Returns:
        list: A list of lists, where each inner list represents a group of elements.

    Example:
        >>> group_by([1, 2, 3, 4, 5, 7, 8, 10], lambda x, y: x + 1 == y)
        [[1, 2, 3, 4, 5], [7, 8], [10]]
    """
    return list(group_by_iter(ls, f))


def list_diff(old_strs: List[str], new_strs: List[str], *, autojunk: bool = False) -> str:
    """
    >>> old = ["line1", "line2", "line3", "line4"]
    >>> new = ["line1", "line3", "line4", "line5"]
    >>> print(list_diff(old, new))
      line1
    - line2
      line3
      line4
    + line5
    """
    # Create a SequenceMatcher object
    sm = SequenceMatcher(None, old_strs, new_strs, autojunk=autojunk)
    opcodes = sm.get_opcodes()
    diff_lines = []

    # Threshold for eliding long equal blocks (if more than this many lines, collapse)
    ELIDE_THRESHOLD = 3

    for tag, i1, i2, j1, j2 in opcodes:
        if tag == "equal":
            block_length = i2 - i1
            if block_length > ELIDE_THRESHOLD:
                # Show the first line, an ellipsis, then the last line of the block.
                diff_lines.append("  " + old_strs[i1])
                diff_lines.append("  ...")
                diff_lines.append("  " + old_strs[i2 - 1])
            else:
                for i in range(i1, i2):
                    diff_lines.append("  " + old_strs[i])
        elif tag == "delete":
            # Lines in old_strs that were removed.
            for i in range(i1, i2):
                diff_lines.append("- " + old_strs[i])
        elif tag == "insert":
            # Lines added in new_strs.
            for j in range(j1, j2):
                diff_lines.append("+ " + new_strs[j])
        elif tag == "replace":
            # Show removed lines
            for i in range(i1, i2):
                diff_lines.append("- " + old_strs[i])
            # Then show inserted lines
            for j in range(j1, j2):
                diff_lines.append("+ " + new_strs[j])

    return "\n".join(diff_lines)


if __name__ == "__main__":
    # if we're working in Python 3.3, we can test this file
    try:
        import doctest

        success = True
    except ImportError:
        print(
            "This is not the main file to use.\nOnly run it if you have doctest (Python 3.3+) and are testing things."
        )
        success = False
    if success:
        doctest.testmod()
