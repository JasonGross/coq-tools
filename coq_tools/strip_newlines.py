import re

__all__ = ["strip_newlines"]


def strip_newlines(contents, max_consecutive_newlines):
    """Removes consecutive newlines in excess of max_consecutive_newlines.

    If max_consecutive_newlines < 0, the contents is returned
    unchanged.

    If max_consecutive_newlines == 0, all strings of consecutive
    newlines are replaced by a single space.

    If max_consecutive_newlines > 0, all strings of consecutive
    newlines in excess of max_consecutive_newlines are replaced by
    max_consecutive_newlines newlines.
    """
    if max_consecutive_newlines < 0:
        return contents
    elif max_consecutive_newlines == 0:
        return re.sub(r"\n+", " ", contents)
    else:
        newlines = r"\n" * max_consecutive_newlines
        return re.sub(newlines + "+", newlines, contents)
