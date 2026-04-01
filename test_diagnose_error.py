"""Tests for coq_tools.diagnose_error.make_reg_string."""

import re
import pytest
from coq_tools.diagnose_error import make_reg_string


def _make_output(error_body):
    """Wrap an error body in the standard Coq error output format."""
    return 'File "./test.v", line 3, characters 14-15:\n' + error_body + "\n"


class TestMakeRegStringUniverseInconsistency:
    """Tests for universe inconsistency error regex generation."""

    def test_named_universe_matches_original(self):
        output = _make_output(
            'Error:\nThe term "P" has type "SProp" while it is expected to have type \n'
            '"Type" (universe inconsistency: Cannot enforce SProp <= foo.foo.u0).'
        )
        reg = make_reg_string(output)
        assert re.search(reg, output)

    def test_named_universe_matches_different_qualified_name(self):
        output = _make_output(
            'Error:\nThe term "P" has type "SProp" while it is expected to have type \n'
            '"Type" (universe inconsistency: Cannot enforce SProp <= foo.foo.u0).'
        )
        reg = make_reg_string(output)
        output2 = output.replace("foo.foo.u0", "bar.baz.u1")
        assert re.search(reg, output2)

    def test_alphanumeric_components(self):
        """Handles mixed alphanumeric components like fo5a.xy1b1.u5."""
        output = _make_output(
            'Error:\nThe term "P" has type "SProp" while it is expected to have type \n'
            '"Type" (universe inconsistency: Cannot enforce SProp <= fo5a.xy1b1.u5).'
        )
        reg = make_reg_string(output)
        assert re.search(reg, output)
        output2 = output.replace("fo5a.xy1b1.u5", "ab1c.de2f.u9")
        assert re.search(reg, output2)

    def test_long_qualified_name(self):
        """Handles long multi-component qualified universe names."""
        output = _make_output(
            'Error: Illegal application: \n'
            'The term "args.imported_QC" of type\n "Type -> Type"\n'
            'cannot be applied to the term\n "P" : "SProp"\n'
            "This term has type \"SProp\" which should be a subtype of \n"
            '"Type". (universe inconsistency: Cannot enforce SProp <=\n'
            "Checker.Parametricity.playground.Interface.imported_QC.u0)"
        )
        reg = make_reg_string(output)
        assert re.search(reg, output)
        output2 = output.replace(
            "Checker.Parametricity.playground.Interface.imported_QC.u0",
            "Different.Module.Sub.u0",
        )
        assert re.search(reg, output2)

    def test_scoping_preserves_names_before_inconsistency(self):
        """Qualified names before 'universe inconsistency' are not generalized."""
        output = _make_output(
            'Error:\nThe term "Foo.Bar.baz" has type "SProp" while it is expected to have type \n'
            '"Type" (universe inconsistency: Cannot enforce SProp <= Module.Sub.u0).'
        )
        reg = make_reg_string(output)
        # Foo.Bar.baz should appear literally in the regex (escaped)
        assert "Foo" in reg
        # Module.Sub.u0 after 'universe inconsistency' should be generalized
        assert "Module" not in reg
        assert re.search(reg, output)

    def test_numeric_universe_still_works(self):
        """Existing numeric-suffix universe handling is preserved."""
        output = _make_output(
            'Error:\nThe term "A.foo" has type "Type" while it is expected to have type \n'
            '"Set" (universe inconsistency).'
        )
        reg = make_reg_string(output)
        assert re.search(reg, output)

    def test_because_clause_still_works(self):
        """The 'because' clause truncation still works."""
        output = _make_output(
            'Error:\nThe term "A.foo" has type "Type" while it is expected to have type \n'
            '"Set" (universe inconsistency: Type != Set because blah blah).'
        )
        reg = make_reg_string(output)
        assert re.search(reg, output)
        # 'because' clause should be replaced with .*
        assert "blah" not in reg
