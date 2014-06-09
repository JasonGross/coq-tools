from strip_comments import strip_comments
import re

__all__ = ["split_coq_file_contents"]

def merge_quotations(statements):
    """If there are an odd number of "s in a statement, assume that we
    broke the middle of a string.  We recombine that string."""

    cur = None
    for i in statements:
        if i.count('"') % 2 != 0:
            if cur is None:
                cur = i
            else:
                yield (cur + ' ' + i)
                cur = None
        elif cur is None:
            yield i
        else:
            cur += ' ' + i

def split_coq_file_contents(contents):
    """Splits the contents of a coq file into multiple statements.

    This is done by finding one or three periods followed by
    whitespace.  This is a dumb algorithm, but it seems to be (nearly)
    the one that ProofGeneral and CoqIDE use.

    We additionally merge lines inside of quotations."""
    return list(merge_quotations(re.split('(?<=[^\.]\.\.\.)\s|(?<=[^\.]\.)\s', strip_comments(contents))))
