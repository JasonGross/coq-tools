__all__ = ['strip_comments']

def strip_comments(contents):
    """Strips the comments from coq code in contents.

    The strings in contents are only preserved if there are no
    comment-like tokens inside of strings.  Stripping should be
    successful and correct, regardless of whether or not there are
    comment-like tokens in strings.

    The behavior of this method is undefined if there are any
    notations which change the meaning of '(*', '*)', or '"'."""
    contents = contents.replace('(*', ' (* ').replace('*)', ' *) ')
    tokens = contents.split(' ')
    rtn = []
    is_string = False
    comment_level = 0
    for token in tokens:
        if is_string:
            if token.count('"') % 2 == 1: # there are an odd number of '"' characters, indicating that we've ended the string
                is_string = False
            rtn.append(token)
        elif token == '(*':
            comment_level += 1
        elif comment_level > 0:
            if token == '*)':
                comment_level -= 1
        else:
            rtn.append(token)
    return ' '.join(tokens)
