import re
import shlex
from .argparse_compat import argparse
from _typeshed import Incomplete
from typing import (
    Any,
    Callable,
    Generic,
    Hashable,
    Iterable,
    Literal,
    Protocol,
    TypeVar,
)

__all__ = [
    "prompt",
    "yes_no_prompt",
    "b",
    "s",
    "cmp_compat",
    "PY3",
    "BooleanOptionalAction",
    "argparse",
    "raw_input",
    "re_escape",
    "slice_string_at_bytes",
    "len_in_bytes",
    "shlex_quote",
    "shlex_join",
    "resource_path",
    "group_by",
    "transitive_closure",
]

BooleanOptionalAction = argparse.BooleanOptionalAction
PY3: bool

def b(x) -> bytes: ...
def s(x) -> str: ...

raw_input = input
re_escape = re.escape
cmp_compat: Callable[[Any, Any], Literal[-1, 1, 0]]
K = TypeVar("K")
V = TypeVar("V")
T = TypeVar("T")
TH = TypeVar("TH", bound=Hashable)

def prompt(
    options,
    case_sensitive: bool = False,
    strip: bool = True,
    sep: str = "/",
    prefix: str = "Please enter ",
    postfix: str = ": ",
    yes_value: bool = True,
    yes: bool = False,
): ...
def yes_no_prompt(**kwargs): ...
def slice_string_at_bytes(string, start=None, end=None): ...
def len_in_bytes(string): ...

class colors:
    ESC: str
    HEADER: str
    OKBLUE: str
    OKCYAN: str
    OKGREEN: str
    WARNING: str
    FAIL: str
    ENDC: str
    BOLD: str
    UNDERLINE: str

shlex_quote = shlex.quote
shlex_join = shlex.join

def resource_path(path): ...
def group_by(ls, f): ...

class TransitiveClosureDict(Protocol, Generic[TH]):
    def __getitem__(self, key: TH, /) -> Iterable[TH]: ...
    def keys(self) -> Iterable[TH]: ...
    def values(self) -> Iterable[Iterable[TH]]: ...

def transitive_closure(graph: TransitiveClosureDict[TH]) -> dict[TH, set[TH]]: ...
