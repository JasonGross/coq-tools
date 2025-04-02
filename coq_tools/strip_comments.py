from .util import group_by

__all__ = ["strip_comments", "strip_trailing_comments"]


def annotate_with_is_comment(tokens):
    """
    Annotates each token in the given list with a boolean value indicating whether it is a comment or not.

    Args:
        tokens (list[str]): The list of tokens to be annotated.

    Yields:
        Tuple[bool, str]: A tuple containing a boolean value indicating whether
        the token is a comment or not, and the token itself.
    """
    is_string = False
    comment_level = 0
    for token in tokens:
        is_comment = comment_level > 0
        if is_string:
            if token.count('"') % 2 == 1:
                # there are an odd number of '"' characters, indicating that we've ended the string
                is_string = False
        elif token.count('"') % 2 == 1:
            # there are an odd number of '"' characters, so we're starting a string
            is_string = True
        elif token == "(*":
            comment_level += 1
            is_comment = True
        elif comment_level > 0 and token == "*)":
            comment_level -= 1
        yield is_comment, token


def split_comments(contents: str):
    """
    Splits the given string into a list of blocks, each of which is either a comment or is entirely comment-free
    """
    contents = contents.replace("(*", " (* ").replace("*)", " *) ")
    tokens = contents.split(" ")
    token_groups = group_by(annotate_with_is_comment(tokens), lambda x, y: x[0] == y[0])
    rtn = []
    for group in token_groups:
        group = " ".join(token for _, token in group)
        if group.startswith("(*"):
            group = " " + group
        if group.endswith("*)"):
            group = group + " "
        group = group.replace(" (* ", "(*").replace(" *) ", "*)")
        rtn.append(group)
    return rtn


def strip_comments(contents):
    """Strips the comments from coq code in contents.

    The strings in contents are only preserved if there are no
    comment-like tokens inside of strings.  Stripping should be
    successful and correct, regardless of whether or not there are
    comment-like tokens in strings.

    The behavior of this method is undefined if there are any
    notations which change the meaning of '(*', '*)', or '"'.

    Note that we take some extra care to leave *) untouched when it
    does not terminate a comment.
    """
    return "".join(block for block in split_comments(contents) if not (block.startswith("(*") and block.endswith("*)")))


def strip_trailing_comments(contents, strip_chars=None):
    """Strips the trailing comments from coq code in contents.

    The definition of "trailing" is that all non-comment characters after the
    comment must be removed with str.strip(strip_chars).
    """
    blocks = split_comments(contents)
    trailing = []
    for block_i, block in reversed(list(enumerate(blocks))):
        if not block.strip(strip_chars):
            trailing.insert(0, block)
        if block.startswith("(*") and block.endswith("*)"):
            continue
        return "".join(blocks[: block_i + 1] + trailing)
    return "".join(trailing)
