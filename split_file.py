from strip_comments import strip_comments
import re

__all__ = ["split_coq_file_contents"]

def split_coq_file_contents(contents):
    """Splits the contents of a coq file into multiple statements.

    This is done by finding periods followed by whitespace.  This is a
    dumb algorithm, but it seems to be (nearly) the one that
    ProofGeneral and CoqIDE use."""
    return re.split('(?<=\.)\s', strip_comments(contents))
