from strip_comments import strip_comments
import re

__all__ = ["split_coq_file_contents", "split_coq_file_contents_with_comments"]

def merge_quotations(statements, sp=' '):
    """If there are an odd number of "s in a statement, assume that we
    broke the middle of a string.  We recombine that string."""

    cur = None
    for i in statements:
        if i.count('"') % 2 != 0:
            if cur is None:
                cur = i
            else:
                yield (cur + sp + i)
                cur = None
        elif cur is None:
            yield i
        else:
            cur += sp + i

BRACES = '{}-*+'

def split_leading_braces(statement):
    while statement.strip() and statement.strip()[0] in BRACES:
        idx = statement.index(statement.strip()[0]) + 1
        first, rest = statement[:idx], statement[idx:]
        #if 'not_reachable_iff' in statement or 'not_reachable_iff' in first:
        #    print((first, rest))
        yield first
        statement = rest
    if statement:
        yield statement

def split_merge_comments(statements):
    """Find open and close comments."""

    def is_genuine_ending(cur):
        return ((cur.strip()[:2] == '(*' and cur.strip()[-2:] == '*)') # cur is just a comment
                or cur.strip()[-1:] in '.}'
                or cur.strip() in BRACES)

    cur = None
    comment_level = 0
    for stmt in statements:
        str_count = 0
        for i in re.split(r'(?<=\*\)) ', stmt.replace('*)', '*) ')):
            if str_count % 2 == 0:
                i2 = re.sub('"[^"]*"|"[^"]*$', '', i)
            else:
                i2 = re.sub('^[^"]*"|"[^"]*"', '', i)
            str_count += i.count('"')
            #print((repr(i), comment_level, repr(i2)))
            if '(*' not in i2 and '*)' not in i2:
                if comment_level < 0:
                    if cur is not None:
                        for ret in split_leading_braces(cur + i):
                            yield ret
                        cur = None
                    else:
                        raw_input('UNEXPECTED COMMENT: %s' % i)
                        yield i
                    comment_level = 0
                elif comment_level == 0:
                    if cur is None:
                        for ret in split_leading_braces(i):
                            yield ret
                    else:
                        cur += i
                elif cur is None:
                    cur = i
                else:
                    cur += i
            else:
                comment_level += i2.count('(*') - i2.count('*)')
                if cur is None:
                    cur = i
                else:
                    cur += i
            if cur is not None:
                curs = list(split_leading_braces(cur))
                while curs and curs[0].strip() in BRACES:
                    yield curs.pop(0)
                cur = ''.join(curs) if curs else None
            if cur is not None and is_genuine_ending(cur) and comment_level == 0: # clear out cur, if we're done with it
                yield cur
                cur = None
    if cur is not None:
        print('Unterminated comment')
        yield cur


def split_coq_file_contents(contents):
    """Splits the contents of a coq file into multiple statements.

    This is done by finding one or three periods followed by
    whitespace.  This is a dumb algorithm, but it seems to be (nearly)
    the one that ProofGeneral and CoqIDE use.

    We additionally merge lines inside of quotations."""
    return list(merge_quotations(re.split('(?<=[^\.]\.\.\.)\s|(?<=[^\.]\.)\s', strip_comments(contents))))

def split_coq_file_contents_with_comments(contents):
    statements = re.split(r'(?<=[^\.]\.\.\.) |(?<=[^\.]\.) ',
                          re.sub(r'((?<=[^\.]\.\.\.)\s|(?<=[^\.]\.)\s)', r' \1', contents))
    #if contents != ''.join(statements):
    #    print('Splitting failed (initial split)!')
    #qstatements = list(merge_quotations(statements, sp=''))
    #if contents != ''.join(qstatements):
    #    print('Splitting failed (quote merge)!')
    #cstatements = list(split_merge_comments(qstatements))
    #if contents != ''.join(cstatements):
    #    print('Splitting failed (comment merge)!')
    return list(split_merge_comments(merge_quotations(statements, sp='')))
