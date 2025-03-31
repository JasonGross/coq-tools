from __future__ import with_statement
import re
from .diagnose_error import get_coq_output
from .coq_version import get_coq_native_compiler_ondemand_fragment, get_boot_noinputstate_args, coqlib_args_of_coq_args
from .coq_full_grammar import COQ_GRAMMAR_TOKENS

# Like coq_version.py, except for things that use get_coq_output (or
# perhaps a bit more generally for things that need to run coqc on a
# file)

__all__ = [
    "get_proof_term_works_with_time",
    "get_ltac_support_snippet",
    "get_reserved_modnames",
    "get_default_options_settings",
]


def get_proof_term_works_with_time(coqc_prog, **kwargs):
    contents = r"""Lemma foo : forall _ : Type, Type.
Proof (fun x => x)."""
    output, cmds, retcode, runtime = get_coq_output(
        coqc_prog,
        ("-time", "-q", *get_boot_noinputstate_args(coqc_prog, **kwargs)),
        contents,
        timeout_val=1,
        verbose_base=3,
        **kwargs,
    )
    return "Error: Attempt to save an incomplete proof" not in output


LTAC_SUPPORT_SNIPPET = {}


def get_ltac_support_snippet(coqc, coqc_args=(), **kwargs):
    if coqc in LTAC_SUPPORT_SNIPPET.keys():
        return LTAC_SUPPORT_SNIPPET[coqc]
    test = r"""Inductive False : Prop := .
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Goal False. admit. Qed."""
    errinfo = {}
    native_ondemand_args = list(get_coq_native_compiler_ondemand_fragment(coqc, coq_args=coqc_args, **kwargs))
    for before, after in (
        ("Require Coq.Init.Ltac.\n", "Import Coq.Init.Ltac.\n"),
        ("Require Coq.Init.Notations.\n", "Import Coq.Init.Notations.\n"),
        ("Require Stdlib.Init.Ltac.\n", "Import Stdlib.Init.Ltac.\n"),
        ("Require Stdlib.Init.Notations.\n", "Import Stdlib.Init.Notations.\n"),
        ('Declare ML Module "coq-core.plugins.ltac".\n', ""),
        ('Declare ML Module "coq-core.plugins.ltac".\n', 'Global Set Default Proof Mode "Classic".\n'),
        ('Declare ML Module "ltac_plugin".\n', ""),
        ('Declare ML Module "ltac_plugin".\n', 'Global Set Default Proof Mode "Classic".\n'),
    ):
        contents = "%s\n%s\n%s" % (before, after, test)
        output, cmds, retcode, runtime = get_coq_output(
            coqc,
            tuple(["-q", "-nois", *coqlib_args_of_coq_args(coqc, coqc_args, **kwargs)] + native_ondemand_args),
            contents,
            timeout_val=None,
            verbose_base=3,
            is_coqtop=kwargs["coqc_is_coqtop"],
            **kwargs,
        )
        if retcode == 0:
            LTAC_SUPPORT_SNIPPET[coqc] = (before, after)
            return (before, after)
        else:
            errinfo[contents] = {"output": output, "cmds": cmds, "retcode": retcode, "runtime": runtime}
    raise Exception("No valid ltac support snipped found.  Debugging info: %s" % repr(errinfo))


def get_is_modname_valid(coqc_prog, modname, **kwargs):
    contents = "Module %s. End %s." % (modname, modname)
    if " " in modname:
        return False
    output, cmds, retcode, runtime = get_coq_output(
        coqc_prog,
        ("-q", *get_boot_noinputstate_args(coqc_prog, **kwargs)),
        contents,
        timeout_val=1,
        verbose_base=3,
        **kwargs,
    )
    return "Syntax error:" not in output


def get_reserved_modnames(coqtop_prog, **kwargs):
    grammars_contents = "Print Grammar tactic. Print Grammar constr. Print Grammar vernac."
    grammars_output, cmds, retcode, runtime = get_coq_output(
        coqtop_prog,
        ("-q", *get_boot_noinputstate_args(coqtop_prog, **kwargs)),
        grammars_contents,
        is_coqtop=True,
        pass_on_stdin=True,
        timeout_val=1,
        verbose_base=3,
        **kwargs,
    )
    tokens = sorted(set([i.strip('"') for i in re.findall(r'"[a-zA-Z_][^"]*"', grammars_output)] + COQ_GRAMMAR_TOKENS))
    contents = "\n".join("Module %s. End %s." % (modname, modname) for modname in tokens)
    output, cmds, retcode, runtime = get_coq_output(
        coqtop_prog,
        ("-q", *get_boot_noinputstate_args(coqtop_prog, **kwargs)),
        contents,
        is_coqtop=True,
        pass_on_stdin=True,
        timeout_val=10,
        verbose_base=3,
        **kwargs,
    )
    success = re.findall(r"Module ([^ ]+) is defined", output)
    return tuple(modname for modname in tokens if modname not in success)


def filter_check_options_after_success(coqc_prog, contents: str, options: list, **kwargs):
    if not options:
        return options
    options_contents = contents + "\n" + "\n".join(options)
    output, cmds, retcode, runtime = get_coq_output(
        coqc_prog,
        ("-q", *kwargs.get("coqc_args", ())),
        options_contents,
        None,
        **kwargs,
    )
    if retcode == 0:
        return options
    elif len(options) == 1:
        return []
    options_1 = options[: len(options) // 2]
    options_2 = options[len(options) // 2 :]
    return filter_check_options_after_success(
        coqc_prog, contents, options_1, **kwargs
    ) + filter_check_options_after_success(coqc_prog, contents, options_2, **kwargs)


def get_default_options_settings(
    coqc_prog, after_contents: str = "", prefix: str = "", coqc_args=(), coqc_is_coqtop=False, **kwargs
):
    options_contents = f"{after_contents}\nPrint Options.\n"
    skip_args = {"-vos", "-vok"}
    coqc_args = tuple([arg for arg in coqc_args if arg not in skip_args])
    output, cmds, retcode, runtime = get_coq_output(
        coqc_prog,
        coqc_args,
        options_contents,
        None,
        is_coqtop=coqc_is_coqtop,
        **kwargs,
    )
    output = f"\n{output}"
    # compat with Coq 8.4, 8.5, 8.6, 8.7
    output = output.replace("\nSynchronous options:", "\nOptions:").replace("\nAsynchronous options:", "")
    assert "\nOptions:" in output, output
    _, options_str = output.split("\nOptions:", maxsplit=1)
    options_str, _tables_str = options_str.split("\nTables:", maxsplit=1)
    options = [
        opt.strip() for opt in options_str.split("\n") if opt.strip() and not opt.strip().startswith("[DEPRECATED")
    ]
    options = [opt[: -len("[DEPRECATED]")].strip() for opt in options if opt.endswith("[DEPRECATED]")]
    options_settings = [opt.split(": ", maxsplit=1) for opt in options]
    commands = []
    for opt_val in options_settings:
        if len(opt_val) == 2:
            opt, val = opt_val
            if val == "undefined" or val == "off":
                commands.append(f"{prefix}Unset {opt}.")
            elif val == "on":
                commands.append(f"{prefix}Set {opt}.")
            else:
                commands.append(f"{prefix}Set {opt} {val}.")

    return "\n".join(filter_check_options_after_success(coqc_prog, after_contents, commands, **kwargs))
