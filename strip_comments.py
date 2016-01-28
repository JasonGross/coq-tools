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
    just_ended_comment = False
    for token in tokens:
        if just_ended_comment and token == '':
            just_ended_comment = False
            continue
        just_ended_comment = (token == '*)')
        do_append = False
        if is_string:
            if token.count('"') % 2 == 1: # there are an odd number of '"' characters, indicating that we've ended the string
                is_string = False
            do_append = True
        elif token == '(*':
            if len(rtn) > 0 and rtn[-1] == '':
                del rtn[-1]
            comment_level += 1
        elif comment_level > 0:
            if token == '*)':
                comment_level -= 1
        elif token.count('"') % 2 == 1: # there are an odd number of '"' characters, so we're starting a string
            is_string = True
            do_append = True
        else:
            do_append = True
        if do_append:
            # handle (*, *)
            if token in ('(*', '*)') and len(rtn) > 0 and rtn[-1] == '':
                del rtn[-1]
            rtn.append(token)
            if len(rtn) > 0 and rtn[-1] in ('(*', '*)') and token == '':
                del rtn[-1]
    return ' '.join(rtn).strip('\n\t ')
