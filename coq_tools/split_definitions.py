import re
from subprocess import Popen, PIPE, STDOUT
from . import split_definitions_old
from .split_file import postprocess_split_proof_term
from .coq_version import get_coq_accepts_time, get_coq_accepts_emacs
from .coq_running_support import get_proof_term_works_with_time
from .custom_arguments import DEFAULT_LOG, LOG_ALWAYS
from . import util
from .util import shlex_join

__all__ = [
    "join_definitions",
    "split_statements_to_definitions",
    "PREFER_PASSING",
    "PASSING",
    "PREFER_NONPASSING",
    "NONPASSING",
    "get_preferred_passing",
    "get_fallback_passing",
]

PREFER_PASSING, PASSING, PREFER_NONPASSING, NONPASSING = "prefer-passing", "passing", "prefer-nonpassing", "nonpassing"

DEFAULT_PREFERENCE_KEY = "parse_with"
_DEFAULT_PASSING = PREFER_NONPASSING


def get_preferred_fallback_passing(key, preference_key=DEFAULT_PREFERENCE_KEY, **env):
    preference = env.get(preference_key, _DEFAULT_PASSING)
    if preference in (PREFER_PASSING, PASSING, PREFER_NONPASSING, NONPASSING):
        default = env.get("passing_" + key) if preference in (PREFER_PASSING, PASSING) else env.get(key)
        fallback = (
            None
            if preference in (PASSING, NONPASSING)
            else env.get("passing_" + key) if preference == PREFER_NONPASSING else env.get(key)
        )
        return (default, fallback)
    raise ValueError(
        "Invalid value for %s: must be one of %s"
        % (preference_key, ", ".join(map(repr, (PREFER_PASSING, PASSING, PREFER_NONPASSING, NONPASSING))))
    )


def get_preferred_passing(key, **env):
    default, fallback = get_preferred_fallback_passing(key, **env)
    return default if default is not None else fallback


def get_fallback_passing(key, **env):
    default, fallback = get_preferred_fallback_passing(key, **env)
    # no fallback if we use fallback as default
    return fallback if default is not None else None


def get_definitions_diff(previous_definition_string, new_definition_string):
    """Returns a triple of lists (definitions_removed,
    definitions_shared, definitions_added)"""
    old_definitions = [i for i in previous_definition_string.split("|") if i]
    new_definitions = [i for i in new_definition_string.split("|") if i]
    if all(i == "branch" for i in old_definitions + new_definitions):  # work
        # around bug #5577 when all theorem names are "branch", we
        # don't assume that names are unique, and instead go by
        # ordering
        removed = []
        shared = []
        added = []
        for i in range(max((len(old_definitions), len(new_definitions)))):
            if i < len(old_definitions) and i < len(new_definitions):
                if old_definitions[i] == new_definitions[i]:
                    shared.append(old_definitions[i])
                else:
                    removed.append(old_definitions[i])
                    added.append(new_definitions[i])
            elif i < len(old_definitions):
                removed.append(old_definitions[i])
            elif i < len(new_definitions):
                added.append(new_definitions[i])
        return (tuple(removed), tuple(shared), tuple(added))
    else:
        return (
            tuple(i for i in old_definitions if i not in new_definitions),
            tuple(i for i in old_definitions if i in new_definitions),
            tuple(i for i in new_definitions if i not in old_definitions),
        )


def strip_newlines(string):
    if not string:
        return string
    if string[0] == "\n":
        return string[1:]
    if string[-1] == "\n":
        return string[:-1]
    return string


def split_statements_to_definitions(
    statements,
    log=DEFAULT_LOG,
    coqtop=("coqtop",),
    coqtop_args=tuple(),
    fallback_coqtop=None,
    fallback_coqtop_args=None,
    preference_key=DEFAULT_PREFERENCE_KEY,
    **kwargs,
):
    """Splits a list of statements into chunks which make up
    independent definitions/hints/etc."""
    if preference_key is not None:
        env = {"coqtop": coqtop, "coqtop_args": coqtop_args, "log": log}
        env.update(kwargs)
        coqtop, fallback_coqtop = get_preferred_fallback_passing("coqtop", preference_key=preference_key, **env)
        coqtop_args, fallback_coqtop_args = get_preferred_fallback_passing(
            "coqtop_args", preference_key=preference_key, **env
        )
        return split_statements_to_definitions(
            statements,
            log=log,
            coqtop=coqtop,
            coqtop_args=coqtop_args,
            fallback_coqtop=fallback_coqtop,
            fallback_coqtop_args=fallback_coqtop_args,
            preference_key=None,
            **kwargs,
        )
    if coqtop is None and fallback_coqtop is not None:
        return split_statements_to_definitions(
            statements,
            log=log,
            coqtop=fallback_coqtop,
            coqtop_args=fallback_coqtop_args,
            fallback_coqtop=None,
            fallback_coqtop_args=None,
            preference_key=None,
            **kwargs,
        )

    def fallback():
        if fallback_coqtop is not None:
            log(
                "Your preferred version of coqtop (%s) doesn't support -emacs -time.  Falling back to fallback coqtop (%s)."
                % (shlex_join(coqtop), shlex_join(fallback_coqtop))
            )
            return split_statements_to_definitions(
                statements,
                log=log,
                coqtop=fallback_coqtop,
                coqtop_args=fallback_coqtop_args,
                fallback_coqtop=None,
                fallback_coqtop_args=None,
                preference_key=None,
                **kwargs,
            )
        else:
            log("Your version of coqtop doesn't support -emacs -time.  Falling back to more error-prone method.")
            return split_definitions_old.split_statements_to_definitions(
                statements, log=log, coqtop=coqtop, coqtop_args=coqtop_args
            )

    # check for -time
    if not get_coq_accepts_time(coqtop, log=log) or not get_coq_accepts_emacs(coqtop, log=log):
        return fallback()
    if not get_proof_term_works_with_time(coqtop, is_coqtop=True, log=log, **kwargs):
        statements = postprocess_split_proof_term(statements, log=log, **kwargs)
    assert isinstance(coqtop, tuple), coqtop
    p = Popen([*coqtop, "-q", "-emacs", "-time"] + list(coqtop_args), stdout=PIPE, stderr=STDOUT, stdin=PIPE)
    chars_time_reg = re.compile(r"Chars ([0-9]+) - ([0-9]+) [^\s]+".replace(" ", r"\s*"))
    prompt_reg = re.compile(
        r"^(.*)<prompt>([^<]*?) < ([0-9]+) ([^<]*?) ([0-9]+) < ([^<]*)$".replace(" ", r"\s*"), flags=re.DOTALL
    )
    defined_reg = re.compile(
        r"^\s*(?:<infomsg>)?([^\s]+) is (?:defined|assumed|declared)(?:</infomsg>)?$", re.MULTILINE
    )
    proof_using_reg = re.compile(
        r"^\s*<infomsg>\s*The proof of ([^\s]+) should start with(?: one of the following commands)?: ([^<]+)</infomsg>".replace(
            " ", r"\s+"
        ),
        flags=re.MULTILINE | re.DOTALL,
    )
    # goals and definitions are on stdout, prompts are on stderr
    statements_string = "Set Suggest Proof Using.\n" + "\n".join(statements) + "\n\n"
    statements_bytes = statements_string.encode("utf-8")
    log("Sending statements to coqtop...")
    log(statements_string, level=3)
    (stdout, stderr) = p.communicate(input=statements_bytes)
    stdout = util.s(stdout)
    if "know what to do with -time" in stdout.strip().split("\n")[0]:
        # we're using a version of coqtop that doesn't support -time
        return fallback()
    log("Done.  Splitting to definitions...")

    rtn = []
    cur_definition = {}
    last_definitions = "||"
    cur_definition_names = "||"
    last_char_end = 0

    # log('re.findall(' + repr(r'Chars ([0-9]+) - ([0-9]+) [^\s]+ (.*?)<prompt>([^<]*?) < ([0-9]+) ([^<]*?) ([0-9]+) < ([^<]*?)</prompt>'.replace(' ', r'\s*')) + ', ' + repr(stdout) + ', ' + 'flags=re.DOTALL)', level=3)
    for i, prompt in enumerate(stdout.split("</prompt>")):
        log("Processing:\n%s" % prompt, level=4)
        if prompt.strip() == "":
            continue
        times = chars_time_reg.findall(prompt)
        if len(times) == 0:
            if i == 0:
                log("Warning: ignoring %s" % repr(prompt), level=3)
            else:
                log("Warning: Could not find timing info in %s" % repr(prompt), level=1)
            continue
        elif len(times) > 1:
            log("Warning: found multiple timing info in %s: %s" % (repr(prompt), repr(times)), level=1)
        full_response_text = chars_time_reg.sub(" ", prompt)
        proof_using_match = proof_using_reg.findall(full_response_text)
        proof_using_options = []
        proof_using_thm_name = None
        if proof_using_match:
            full_response_text = proof_using_reg.sub(" ", full_response_text)
            if len(proof_using_match) > 1:
                log(
                    "Warning: found multiple proof using info in %s: %s" % (prompt, str(proof_using_match)),
                    level=LOG_ALWAYS,
                )
            proof_using_thm_name, proof_using_cmds = proof_using_match[0]
            proof_using_options = [s.strip() for s in proof_using_cmds.split("Proof using") if s.strip()]
            proof_using_options = [s.split(".")[0].strip() for s in proof_using_options]
            # log("Warning: found proof using info in %s: %s" % (repr(prompt), repr(proof_using_match)), level=1)
            # continue
        proof_using_options_used = False
        for char_start, char_end in times:
            char_start, char_end = int(char_start), int(char_end)
            # if we've travelled backwards in time, as in
            # COQBUG(https://github.com/coq/coq/issues/14475); we just
            # ignore this statement
            if char_end <= last_char_end:
                continue
            match = prompt_reg.match(full_response_text)
            if not match:
                log(
                    "Warning: Could not find statements in %d:%d: %s" % (char_start, char_end, full_response_text),
                    level=LOG_ALWAYS,
                )
                continue
            response_text, cur_name, line_num1, cur_definition_names, line_num2, unknown = match.groups()
            statement = strip_newlines(statements_bytes[last_char_end:char_end].decode("utf-8"))
            last_char_end = char_end

            terms_defined = defined_reg.findall(response_text.strip())

            definitions_removed, definitions_shared, definitions_added = get_definitions_diff(
                last_definitions, cur_definition_names
            )

            # first, to be on the safe side, we add the new
            # definitions key to the dict, if it wasn't already there.
            if cur_definition_names.strip("|") and cur_definition_names not in cur_definition:
                cur_definition[cur_definition_names] = {
                    "statements": [],
                    "terms_defined": [],
                    "proof_using_options_map": [],
                    "proof_using_options": [],
                }

            log(
                (
                    statement,
                    (char_start, char_end),
                    definitions_removed,
                    proof_using_thm_name,
                    proof_using_options,
                    terms_defined,
                    "last_definitions:",
                    last_definitions,
                    "cur_definition_names:",
                    cur_definition_names,
                    cur_definition.get(last_definitions, []),
                    cur_definition.get(cur_definition_names, []),
                    response_text,
                ),
                level=2,
            )

            # first, we handle the case where we have just finished
            # defining something.  This should correspond to
            # len(definitions_removed) > 0 and len(terms_defined) > 0.
            # If only len(definitions_removed) > 0, then we have
            # aborted something (or we're in Coq >= 8.11; see
            # https://github.com/coq/coq/issues/15201).  If only
            # len(terms_defined) > 0, then we have defined something
            # with a one-liner.
            if definitions_removed:
                cur_definition[last_definitions]["statements"].append(statement)
                cur_definition[last_definitions]["terms_defined"] += terms_defined
                if proof_using_options:
                    cur_definition[last_definitions]["proof_using_options_map"].append(
                        (proof_using_thm_name, tuple(proof_using_options))
                    )
                    cur_definition[last_definitions]["proof_using_options"] += proof_using_options
                    proof_using_options = []
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
                    cur_definition[cur_definition_names]["proof_using_options_map"] += cur_definition[last_definitions][
                        "proof_using_options_map"
                    ]
                    cur_definition[cur_definition_names]["proof_using_options"] += cur_definition[last_definitions][
                        "proof_using_options"
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
                            "proof_using_options_map": tuple(
                                cur_definition[last_definitions]["proof_using_options_map"]
                            ),
                            "proof_using_options": tuple(cur_definition[last_definitions]["proof_using_options"]),
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
                        {
                            "statements": (statement,),
                            "statement": statement,
                            "terms_defined": tuple(terms_defined),
                            "proof_using_options_map": (
                                ((proof_using_thm_name, tuple(proof_using_options)),) if proof_using_options else ()
                            ),
                            "proof_using_options": tuple(proof_using_options),
                        }
                    )
                    proof_using_options_used = True

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
                    rtn.append(
                        {
                            "statements": (statement,),
                            "statement": statement,
                            "terms_defined": (),
                            "proof_using_options_map": (
                                ((proof_using_thm_name, tuple(proof_using_options)),) if proof_using_options else ()
                            ),
                            "proof_using_options": tuple(proof_using_options),
                        }
                    )
                    proof_using_options_used = True

            last_definitions = cur_definition_names
        if proof_using_options and not proof_using_options_used:
            log("Warning: Unused proof using options: %s in %s" % (str(proof_using_options), prompt), level=LOG_ALWAYS)
    log((last_definitions, cur_definition_names), level=2)
    if last_definitions.strip("||"):
        rtn.append(
            {
                "statements": tuple(cur_definition[cur_definition_names]["statements"]),
                "statement": "\n".join(cur_definition[cur_definition_names]["statements"]),
                "terms_defined": tuple(cur_definition[cur_definition_names]["terms_defined"]),
                "proof_using_options_map": tuple(cur_definition[cur_definition_names]["proof_using_options_map"]),
                "proof_using_options": tuple(cur_definition[cur_definition_names]["proof_using_options"]),
            }
        )
        del cur_definition[last_definitions]

    if last_char_end + 1 < len(statements_bytes):
        last_statement = statements_bytes[last_char_end:].decode("utf-8")
        log("Appending end of code from %d to %d: %s" % (last_char_end, len(statements_bytes), last_statement), level=2)
        last_statement = strip_newlines(last_statement)
        rtn.append(
            {
                "statements": tuple(
                    last_statement,
                ),
                "statement": last_statement,
                "terms_defined": (),
                "proof_using_options_map": (
                    ((proof_using_thm_name, tuple(proof_using_options)),)
                    if proof_using_options and not proof_using_options_used
                    else ()
                ),
                "proof_using_options": (
                    tuple(proof_using_options) if proof_using_options and not proof_using_options_used else ()
                ),
            }
        )
    if rtn[0]["statement"].strip() == "Set Suggest Proof Using.":
        rtn = rtn[1:]

    return rtn


def join_definitions(definitions):
    return "\n".join(i["statement"] for i in definitions)
