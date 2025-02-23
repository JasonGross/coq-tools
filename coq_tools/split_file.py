import subprocess, re
from .strip_comments import strip_comments
from .custom_arguments import DEFAULT_LOG
from .coq_version import get_coq_accepts_time
from . import util
from .util import PY3

if PY3:
    from .util import raw_input

__all__ = [
    "split_coq_file_contents",
    "split_coq_file_contents_with_comments",
    "get_coq_statement_byte_ranges",
    "UnsupportedCoqVersionError",
    "postprocess_split_proof_term",
    "split_leading_comments_and_whitespace",
]


def fill_kwargs(kwargs):
    ret = {
        "log": DEFAULT_LOG,
        "coqc": "coqc",
        "coqc_args": tuple(),
    }
    ret.update(kwargs)
    return ret


class UnsupportedCoqVersionError(Exception):
    pass


def merge_quotations(statements, sp=" "):
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


BRACES = "{}-*+"


def split_leading_braces(statement):
    while statement.strip() and statement.strip()[0] in BRACES:
        idx = statement.index(statement.strip()[0]) + 1
        first, rest = statement[:idx], statement[idx:]
        # if 'not_reachable_iff' in statement or 'not_reachable_iff' in first:
        #    print((first, rest))
        yield first
        statement = rest
    if statement:
        yield statement


def split_leading_comments_and_whitespace(text):
    comment_level = 0
    in_str = False
    skip = False
    for i, (ch, next_ch) in enumerate(zip(text, text[1:] + "\0")):
        if skip:
            skip = False
        elif in_str:
            if ch in '"':
                in_str = False
        elif ch == "(" and next_ch == "*":
            comment_level += 1
            skip = True
        elif ch == "*" and next_ch == ")":
            comment_level -= 1
            skip = True
        elif comment_level > 0:
            if ch in '"':
                in_str = True
        elif ch.isspace():
            pass
        else:
            return text[:i], text[i:]
    return text, ""


def split_merge_comments(statements):
    """Find open and close comments."""

    def is_genuine_ending(cur):
        return (
            (cur.strip()[:2] == "(*" and cur.strip()[-2:] == "*)")  # cur is just a comment
            or cur.strip()[-1:] in ".}"
            or cur.strip() in BRACES
        )

    cur = None
    comment_level = 0
    for stmt in statements:
        str_count = 0
        for i in re.split(r"(?<=\*\)) ", stmt.replace("*)", "*) ")):
            if str_count % 2 == 0:
                i2 = re.sub('"[^"]*"|"[^"]*$', "", i)
            else:
                i2 = re.sub('^[^"]*"|"[^"]*"', "", i)
            str_count += i.count('"')
            # print((repr(i), comment_level, repr(i2)))
            if "(*" not in i2 and "*)" not in i2:
                if comment_level < 0:
                    if cur is not None:
                        for ret in split_leading_braces(cur + i):
                            yield ret
                        cur = None
                    else:
                        raw_input("UNEXPECTED COMMENT: %s" % i)
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
                comment_level += i2.count("(*") - i2.count("*)")
                if cur is None:
                    cur = i
                else:
                    cur += i
            if cur is not None:
                curs = list(split_leading_braces(cur))
                while curs and curs[0].strip() in BRACES:
                    yield curs.pop(0)
                cur = "".join(curs) if curs else None
            if (
                cur is not None and is_genuine_ending(cur) and comment_level == 0
            ):  # clear out cur, if we're done with it
                yield cur
                cur = None
    if cur is not None:
        print("Unterminated comment")
        yield cur


def split_coq_file_contents(contents):
    """Splits the contents of a coq file into multiple statements.

    This is done by finding one or three periods followed by
    whitespace.  This is a dumb algorithm, but it seems to be (nearly)
    the one that ProofGeneral and CoqIDE use.

    We additionally merge lines inside of quotations."""
    return list(merge_quotations(re.split(r"(?<=[^\.]\.\.\.)\s|(?<=[^\.]\.)\s", strip_comments(contents))))


def split_coq_file_contents_with_comments(contents):
    statements = re.split(
        r"(?<=[^\.]\.\.\.) |(?<=[^\.]\.) ", re.sub(r"((?<=[^\.]\.\.\.)\s|(?<=[^\.]\.)\s)", r" \1", contents)
    )
    # if contents != ''.join(statements):
    #    print('Splitting failed (initial split)!')
    # qstatements = list(merge_quotations(statements, sp=''))
    # if contents != ''.join(qstatements):
    #    print('Splitting failed (quote merge)!')
    # cstatements = list(split_merge_comments(qstatements))
    # if contents != ''.join(cstatements):
    #    print('Splitting failed (comment merge)!')
    return list(split_merge_comments(merge_quotations(statements, sp="")))


PROOF_TERM_REG = re.compile(r"(\s*)Proof(\s+)(.*?)\.(\s*)", flags=re.DOTALL | re.MULTILINE)


def postprocess_split_proof_term_iter(statements, on_first_example=None):
    """Returns an iterator for the statements passed which changes [Proof
    term.] into [Proof. exact (term). Qed.] unless "term" begins with
    "with" or "using"."""
    for statement_num, statement in enumerate(statements):
        match = PROOF_TERM_REG.match(statement)
        if match:
            indent, after_proof_space, proof_term, post_space = match.groups()
            if re.split(r"\s", proof_term)[0] not in (
                "using",
                "with",
            ):  # Proof using ... and Proof with ... are special
                if on_first_example:
                    on_first_example(statement_num, statement, proof_term)
                    on_first_example = None
                yield indent + "Proof."
                yield after_proof_space + "exact (" + proof_term + ")."
                yield " Qed." + post_space
            else:
                yield statement
        else:
            yield statement


def postprocess_split_proof_term(statements, do_warn=True, **kwargs):
    def do_warn_method(statement_num, statement, proof_term):
        kwargs["log"](
            """Warning: Your version of Coq suffers from bug #5349 (https://coq.inria.fr/bugs/show_bug.cgi?id=5349)
and does not support [Proof (term).] with -time.  Falling back to
replacing [Proof (term).] with [Proof. exact (term). Qed.], which may fail."""
        )

    if do_warn and "log" in kwargs.keys():
        do_warn = do_warn_method
    else:
        do_warn = None
    return list(postprocess_split_proof_term_iter(statements, do_warn))


RANGE_REG = re.compile(r"Chars ([0-9]+) - ([0-9]+) [^\s]+", flags=re.DOTALL)


def get_coq_statement_byte_ranges(file_name, coqc, **kwargs):
    kwargs = fill_kwargs(kwargs)
    if not get_coq_accepts_time(coqc, **kwargs):
        raise UnsupportedCoqVersionError

    assert isinstance(coqc, tuple), coqc
    p = subprocess.Popen(
        [*coqc, "-q", "-time"] + list(kwargs["coqc_args"]) + [file_name],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        stdin=subprocess.PIPE,
    )
    (stdout, stderr) = p.communicate()

    ranges = tuple((int(start), int(finish)) for start, finish in RANGE_REG.findall(util.s(stdout)))
    return ranges
