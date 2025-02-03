import re, time
from .Popen_noblock import Popen_async, PIPE, STDOUT, Empty

__all__ = ["join_definitions", "split_statements_to_definitions"]

DEFAULT_VERBOSITY = 1


def DEFAULT_LOG(text, level=DEFAULT_VERBOSITY):
    if level <= DEFAULT_VERBOSITY:
        print(text)


def get_all_nowait_iter(q):
    try:
        while True:
            yield q.get_nowait()
    except Empty:
        pass


def get_all_nowait(q):
    return "".join(get_all_nowait_iter(q))


def get_all_semiwait_iter(q, log=DEFAULT_LOG):
    def log_and_return(val):
        log(val, level=5)
        return val

    try:
        # this is blocking; TODO(jgross): Figure out how to get coqtop
        # to tell us if it's finished computing
        yield log_and_return(q.get(True))
        while True:
            yield log_and_return(q.get(True, 0.1))
    except Empty:
        pass


def get_all_semiwait(q, log=DEFAULT_LOG):
    return "".join(get_all_semiwait_iter(q, log=log))


def get_definitions_diff(previous_definition_string, new_definition_string):
    """Returns a triple of lists (definitions_removed,
    definitions_shared, definitions_added)"""
    old_definitions = [i for i in previous_definition_string.split("|") if i]
    new_definitions = [i for i in new_definition_string.split("|") if i]
    return (
        tuple(i for i in old_definitions if i not in new_definitions),
        tuple(i for i in old_definitions if i in new_definitions),
        tuple(i for i in new_definitions if i not in old_definitions),
    )


# def split_coq_code_to_definitions(code, log=DEFAULT_LOG, coqtop='coqtop'):
#    """Splits coq code into chunks which make up
#    independent definitions/hints/etc, of the form
#
#    {
#     'statements': <list of runnable statements>,
#     'statement':  <entire chunk of code>,
#     'terms_defined': <tuple of terms defined by this chunk of code>,
#     'times': <a list of times for each statement>
#     'output': <a string of the response from coqtop>
#    }"""
#    p = Popen_async([coqtop, '-q', '-emacs', '-time'], stdout=PIPE, stderr=STDOUT, stdin=PIPE)
#    time.sleep(1)


def split_statements_to_definitions(statements, log=DEFAULT_LOG, coqtop="coqtop", coqtop_args=tuple()):
    """Splits a list of statements into chunks which make up
    independent definitions/hints/etc."""
    p = Popen_async([*coqtop, "-q", "-emacs"] + list(coqtop_args), stdout=PIPE, stderr=STDOUT, stdin=PIPE)
    time.sleep(1)
    prompt_reg = re.compile(r"<prompt>([^<]*?) < ([0-9]+) ([^<]*?) ([0-9]+) < ([^<]*?)</prompt>".replace(" ", r"\s*"))
    defined_reg = re.compile(r"^([^\s]+) is (?:defined|assumed)$", re.MULTILINE)
    # aborted_reg = re.compile(r'^Current goal aborted$', re.MULTILINE)
    # goal_reg = re.compile(r'^\s*=+\s*$', re.MULTILINE)
    # goals and definitions are on stdout, prompts are on stderr
    # clear stdout
    get_all_semiwait(p.stdout, log=log)
    # clear stderr
    # get_all_nowait(p.stderr)

    rtn = []
    cur_definition = {}
    last_definitions = "||"
    cur_definition_names = "||"
    for statement in statements:
        if not statement.strip():
            continue
        log("Write: %s\n\nWait to read..." % statement, level=4)
        p.stdin.write(statement + "\n\n")
        p.stdin.flush()
        stdout = get_all_semiwait(p.stdout, log=log)
        stderr = stdout  # ''.join(get_all_semiwait(p.stderr))

        terms_defined = defined_reg.findall(prompt_reg.sub("", stdout))
        # print((statement, stdout, terms_defined))
        prompt_match = prompt_reg.search(stderr)

        if not prompt_match or len(prompt_match.groups()) != 5:
            if not prompt_match:
                log("Likely fatal warning: I did not recognize the output from coqtop:")
                log("stdout: %s\nstderr: %s" % (repr(stdout), repr(stderr)))
                log(
                    "I will append the current statement (%s) to the list of definitions as-is, but I don't expect this to work."
                    % statement
                )
            else:
                log("Crazy things are happening; the number of groups isn't what it should be (should be 5 groups):")
                log(
                    "prompt_match.groups(): %s\nstdout: %s\nstderr: %s\nstatement: %s\n"
                    % (repr(prompt_match.groups()), repr(stdout), repr(stderr), repr(statement))
                )

            log((statement, terms_defined, cur_definition_names, cur_definition.get(cur_definition_names, [])), level=2)
            if cur_definition_names.strip("|"):
                cur_definition[cur_definition_names]["statements"].append(statement)
                cur_definition[cur_definition_names]["terms_defined"] += terms_defined
            else:
                rtn.append({"statements": (statement,), "statement": statement, "terms_defined": tuple(terms_defined)})
        else:
            cur_name, line_num1, cur_definition_names, line_num2, unknown = prompt_reg.search(stderr).groups()
            definitions_removed, definitions_shared, definitions_added = get_definitions_diff(
                last_definitions, cur_definition_names
            )

            # first, to be on the safe side, we add the new
            # definitions key to the dict, if it wasn't already there.
            if cur_definition_names.strip("|") and cur_definition_names not in cur_definition:
                cur_definition[cur_definition_names] = {"statements": [], "terms_defined": []}

            log(
                (
                    statement,
                    terms_defined,
                    last_definitions,
                    cur_definition_names,
                    cur_definition.get(last_definitions, []),
                    cur_definition.get(cur_definition_names, []),
                ),
                level=2,
            )

            # first, we handle the case where we have just finished
            # defining something.  This should correspond to
            # len(definitions_removed) > 0 and len(terms_defined) > 0.
            # If only len(definitions_removed) > 0, then we have
            # aborted something.  If only len(terms_defined) > 0, then
            # we have defined something with a one-liner.
            if definitions_removed:
                cur_definition[last_definitions]["statements"].append(statement)
                cur_definition[last_definitions]["terms_defined"] += terms_defined
                if cur_definition_names.strip("|"):
                    # we are still inside a definition.  For now, we
                    # flatten all definitions.
                    #
                    # TODO(jgross): Come up with a better story for
                    # nested definitions.
                    cur_definition[cur_definition_names]["statements"] += cur_definition[last_definitions]["statements"]
                    cur_definition[cur_definition_names]["terms_defined"] += cur_definition[last_definitions][
                        "terms_defined"
                    ]
                    del cur_definition[last_definitions]
                else:
                    # we're at top-level, so add this as a new
                    # definition
                    rtn.append(
                        {
                            "statements": tuple(cur_definition[last_definitions]["statements"]),
                            "statement": "\n".join(cur_definition[last_definitions]["statements"]),
                            "terms_defined": tuple(cur_definition[last_definitions]["terms_defined"]),
                        }
                    )
                    del cur_definition[last_definitions]
                    # print('Adding:')
                    # print(rtn[-1])
            elif terms_defined:
                if cur_definition_names.strip("|"):
                    # we are still inside a definition.  For now, we
                    # flatten all definitions.
                    #
                    # TODO(jgross): Come up with a better story for
                    # nested definitions.
                    cur_definition[cur_definition_names]["statements"].append(statement)
                    cur_definition[cur_definition_names]["terms_defined"] += terms_defined
                else:
                    # we're at top level, so add this as a new
                    # definition
                    rtn.append(
                        {"statements": (statement,), "statement": statement, "terms_defined": tuple(terms_defined)}
                    )

            # now we handle the case where we have just opened a fresh
            # definition.  We've already added the key to the
            # dictionary.
            elif definitions_added:
                # print(definitions_added)
                cur_definition[cur_definition_names]["statements"].append(statement)
            else:
                # if we're in a definition, append the statement to
                # the queue, otherwise, just add it as it's own
                # statement
                if cur_definition_names.strip("|"):
                    cur_definition[cur_definition_names]["statements"].append(statement)
                else:
                    rtn.append({"statements": (statement,), "statement": statement, "terms_defined": tuple()})
        last_definitions = cur_definition_names

    log((last_definitions, cur_definition_names), level=2)
    if last_definitions.strip("||"):
        rtn.append(
            {
                "statements": tuple(cur_definition[cur_definition_names]["statements"]),
                "statement": "\n".join(cur_definition[cur_definition_names]["statements"]),
                "terms_defined": tuple(cur_definition[cur_definition_names]["terms_defined"]),
            }
        )
        del cur_definition[last_definitions]
    # for i in rtn:
    # print(i)
    p.stdin.close()
    return rtn


def join_definitions(definitions):
    return "\n".join(i["statement"] for i in definitions)
