import sys

if sys.version_info < (3,):
    from . import argparse_py2 as argparse
else:
    import argparse

if not hasattr(argparse, "BooleanOptionalAction"):
    # from the stdlib

    class BooleanOptionalAction(argparse.Action):
        def __init__(
            self, option_strings, dest, default=None, type=None, choices=None, required=False, help=None, metavar=None
        ):

            _option_strings = []
            for option_string in option_strings:
                _option_strings.append(option_string)

                if option_string.startswith("--"):
                    option_string = "--no-" + option_string[2:]
                    _option_strings.append(option_string)

            super().__init__(
                option_strings=_option_strings,
                dest=dest,
                nargs=0,
                default=default,
                type=type,
                choices=choices,
                required=required,
                help=help,
                metavar=metavar,
            )

        def __call__(self, parser, namespace, values, option_string=None):
            if option_string in self.option_strings:
                setattr(namespace, self.dest, not option_string.startswith("--no-"))

        def format_usage(self):
            return " | ".join(self.option_strings)

    argparse.BooleanOptionalAction = BooleanOptionalAction
