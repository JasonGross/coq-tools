import os
import re
import shlex
import shutil
import sys
import subprocess
from difflib import SequenceMatcher
from typing import Dict, Hashable, Iterable, List, Set, TypeVar, Tuple

try:
    from typing import Protocol
except ImportError:
    Protocol = None

from .argparse_compat import argparse

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
    "get_peak_rss_bytes",
    "parse_memory_bytes",
    "wrap_with_prlimit",
    "wrap_with_ulimit",
    "wrap_with_cgexec",
    "wrap_with_cgexec_and_create",
    "wrap_with_systemd_run",
    "cleanup_cgroup",
    "apply_memory_limit",
    "MEMORY_LIMIT_METHODS",
]

BooleanOptionalAction = argparse.BooleanOptionalAction

SCRIPT_DIRECTORY = os.path.dirname(os.path.realpath(__file__))

if sys.version_info < (3,):
    PY3 = False

    def b(x):
        return x

    def s(x):
        return x

else:
    PY3 = True

    def b(x) -> bytes:
        if x is not None:
            return x.encode()
        return x

    def s(x) -> str:
        # Sometimes we get str rather than bytes??? cf https://gitlab.com/coq/coq/-/jobs/544269051
        if hasattr(x, "decode"):
            return x.decode("utf-8", "ignore")
        return x

    def cmp(x, y):
        if x < y:
            return -1
        if y < x:
            return 1
        return 0

    raw_input = input

if sys.version_info < (3, 7):
    # see https://bugs.python.org/issue29995
    def re_escape(*args, **kwargs):
        ret = re.escape(*args, **kwargs)
        for ch in ':"':
            ret = ret.replace("\\" + ch, ch)
        return ret

else:
    re_escape = re.escape

cmp_compat = cmp

K = TypeVar("K")
V = TypeVar("V")
T = TypeVar("T")
TH = TypeVar("TH", bound=Hashable)


def prompt(
    options,
    case_sensitive=False,
    strip=True,
    sep="/",
    prefix="Please enter ",
    postfix=": ",
    yes_value=True,
    yes=False,
):
    msg = prefix + sep.join(i["display"] for i in options) + postfix
    if yes:
        print(msg)
        return yes_value
    else:
        response = raw_input(msg)
        while True:
            if not case_sensitive:
                response = response.lower()
            if strip:
                response = response.strip()
            for expected in options:
                if response in expected["values"]:
                    return expected["value"]
            print(
                'Response "%s" is not one of %s'
                % (
                    response,
                    ", ".join(repr(val) for i in options for val in i["values"]),
                )
            )
            response = raw_input(msg)


def yes_no_prompt(**kwargs):
    return prompt(
        (
            {"value": True, "display": "(y)es", "values": ("y", "yes")},
            {"value": False, "display": "(n)o", "values": ("n", "no")},
        ),
        yes_value=True,
        **kwargs,
    )


# Unfortunately, coqtop -emacs -time reports character locations in
# bytes, as does the glob file, so we need to handle unicode.  Here we
# write a generic slicer based on unicode locations that works across
# versions of python
def slice_string_at_bytes(string, start=None, end=None):
    string = b(string)
    if start is None:
        start = 0
    if end is None:
        end = len(string)
    return s(string[start:end])


def len_in_bytes(string):
    return len(b(string))


def normalize_newlines(string: str) -> str:
    return string.replace("\r\n", "\n").replace("\r", "\n")


# Terminal colors (maybe something cleverer needs to be done for other
# platforms).
class colors:
    ESC = "\033"
    # Escape code doesn't render on github so we use the standard escaped escape.
    # ESC = ''

    HEADER = ESC + "[95m"
    OKBLUE = ESC + "[94m"
    OKCYAN = ESC + "[96m"
    OKGREEN = ESC + "[92m"
    WARNING = ESC + "[93m"
    FAIL = ESC + "[91m"
    ENDC = ESC + "[0m"
    BOLD = ESC + "[1m"
    UNDERLINE = ESC + "[4m"


# Colors a string a given color
# Example usage: color("Hello World!", colors.OKBLUE)
def color(str, col, on=True):
    if not on:
        return str
    else:
        return col + str + colors.ENDC


if sys.version_info < (3, 3):
    import pipes

    shlex_quote = pipes.quote
else:
    import shlex

    shlex_quote = shlex.quote

if sys.version_info < (3, 8):
    shlex_join = lambda split_command: " ".join(
        shlex_quote(arg) for arg in split_command
    )
else:
    import shlex

    shlex_join = shlex.join


def resource_path(path):
    if os.path.exists(os.path.join(SCRIPT_DIRECTORY, path)):
        return os.path.join(SCRIPT_DIRECTORY, path)
    if sys.version_info < (3, 7):
        import pkg_resources

        return pkg_resources.resource_filename("coq_tools", path)
    else:
        import importlib.resources

        return importlib.resources.path("coq_tools", path)


def group_by_iter(ls, f):
    """
    Groups elements in a list based on a given condition.

    Args:
        ls (iterable): The list of elements to be grouped.
        f (function): The condition function used for grouping.

    Returns:
        iterable: A list of lists, where each inner list represents a group of elements.
    """
    it = iter(ls)
    prev = next(it)
    cur = [prev]
    for token in it:
        if f(prev, token):
            cur.append(token)
        else:
            yield cur
            cur = [token]
        prev = token
    yield cur


def group_by(ls, f):
    """
    Groups elements in a list based on a given condition.

    Args:
        ls (list): The list of elements to be grouped.
        f (function): The condition function used for grouping.

    Returns:
        list: A list of lists, where each inner list represents a group of elements.

    Example:
        >>> group_by([1, 2, 3, 4, 5, 7, 8, 10], lambda x, y: x + 1 == y)
        [[1, 2, 3, 4, 5], [7, 8], [10]]
    """
    return list(group_by_iter(ls, f))


def list_diff(
    old_strs: List[str], new_strs: List[str], *, autojunk: bool = False
) -> str:
    """
    >>> old = ["line1", "line2", "line3", "line4"]
    >>> new = ["line1", "line3", "line4", "line5"]
    >>> print(list_diff(old, new))
      line1
    - line2
      line3
      line4
    + line5
    """
    # Create a SequenceMatcher object
    sm = SequenceMatcher(None, old_strs, new_strs, autojunk=autojunk)
    opcodes = sm.get_opcodes()
    diff_lines = []

    # Threshold for eliding long equal blocks (if more than this many lines, collapse)
    ELIDE_THRESHOLD = 3

    for tag, i1, i2, j1, j2 in opcodes:
        if tag == "equal":
            block_length = i2 - i1
            if block_length > ELIDE_THRESHOLD:
                # Show the first line, an ellipsis, then the last line of the block.
                diff_lines.append("  " + old_strs[i1])
                diff_lines.append("  ...")
                diff_lines.append("  " + old_strs[i2 - 1])
            else:
                for i in range(i1, i2):
                    diff_lines.append("  " + old_strs[i])
        elif tag == "delete":
            # Lines in old_strs that were removed.
            for i in range(i1, i2):
                diff_lines.append("- " + old_strs[i])
        elif tag == "insert":
            # Lines added in new_strs.
            for j in range(j1, j2):
                diff_lines.append("+ " + new_strs[j])
        elif tag == "replace":
            # Show removed lines
            for i in range(i1, i2):
                diff_lines.append("- " + old_strs[i])
            # Then show inserted lines
            for j in range(j1, j2):
                diff_lines.append("+ " + new_strs[j])

    return "\n".join(diff_lines)


# if Protocol is not None:

#     class _TransitiveClosureDict(Generic[TH], Protocol):
#         def __getitem__(self, key: TH) -> Iterable[TH]: ...

#         def keys(self) -> Iterable[TH]: ...

#         def values(self) -> Iterable[Iterable[TH]]: ...

#     TransitiveClosureDict = _TransitiveClosureDict
# else:

#     class _TransitiveClosureDictOld(Generic[TH], Dict[TH, Iterable[TH]]):
#         pass

#     TransitiveClosureDict = _TransitiveClosureDictOld


def transitive_closure(
    graph: Dict[TH, Iterable[TH]],
) -> Dict[TH, Set[TH]]:
    """
    Computes the transitive closure of a directed graph represented as an adjacency list.

    The input is a dictionary where keys are nodes and values are iterables of neighboring nodes.
    The output is a dictionary where each key is a node and the value is the set of all reachable nodes
    from that key, including itself.

    This implementation uses iterative DFS for each starting node to handle large graphs and avoid recursion depth issues.
    """
    # Collect all nodes (keys and those appearing in values)
    all_nodes = set(graph.keys())
    for neighbors in graph.values():
        all_nodes.update(neighbors)

    def adj(node):
        # allow fills from __missing__
        try:
            return graph[node]
        except KeyError:
            return ()

    closure = {}
    for start in all_nodes:
        visited = set()
        stack = [start]
        while stack:
            node = stack.pop()
            if node not in visited:
                visited.add(node)
                for neighbor in adj(node):
                    if neighbor not in visited:
                        stack.append(neighbor)
        closure[start] = visited

    return closure


def get_peak_rss_bytes(rusage):
    """
    Extract peak RSS (Resident Set Size) from rusage in bytes.

    Args:
        rusage: A resource usage object from os.wait4() or similar.

    Returns:
        Peak RSS in bytes. On Linux, ru_maxrss is in kilobytes, so we multiply by 1024.
        On macOS/BSD, ru_maxrss is already in bytes.
    """
    if rusage is None:
        return None
    if sys.platform.startswith("linux"):
        return rusage.ru_maxrss * 1024
    else:
        return rusage.ru_maxrss


def parse_memory_bytes(mem_str: str) -> int:
    """
    Parse a memory string (case-insensitive) to bytes.

    Supports formats like: "5M", "5G", "5GB", "5GiB", "512", "unlimited", "0"

    Args:
        mem_str: Memory string to parse (case-insensitive)

    Returns:
        Number of bytes, or -1 for "unlimited" or "0"

    Examples:
        >>> parse_memory_bytes("5M")
        5242880
        >>> parse_memory_bytes("5G")
        5368709120
        >>> parse_memory_bytes("5GB")
        5368709120
        >>> parse_memory_bytes("5GiB")
        5368709120
        >>> parse_memory_bytes("512")
        512
        >>> parse_memory_bytes("unlimited")
        -1
        >>> parse_memory_bytes("0")
        -1
    """
    if isinstance(mem_str, (int, float)):
        val = float(mem_str)
        return int(val) if val > 0 else -1

    mem_str_normalized = str(mem_str).strip().lower()
    mem_str = mem_str_normalized

    if mem_str in ("unlimited", "0", ""):
        return -1

    # Match number with optional unit suffix
    # Pattern: number followed by optional unit
    # Units: k/m/g/t (with optional 'i' for binary, optional 'b' suffix)
    # Examples: "5", "5k", "5kb", "5kib", "5m", "5mb", "5mib", "5g", "5gb", "5gib"
    match = re.match(r"^(\d+(?:\.\d+)?)\s*([kmgt]i?b?)$", mem_str)
    if not match:
        # Try to parse as plain number
        try:
            val = int(mem_str)
            return val if val > 0 else -1
        except ValueError:
            raise ValueError(f"Invalid memory format: {mem_str}")

    number_str, unit = match.groups()
    number = float(number_str)

    # Parse unit - handle both "b" and "ib" suffixes
    unit = unit.lower()
    if unit == "" or unit == "b":
        multiplier = 1
    elif unit in ("k", "kb"):
        multiplier = 1000
    elif unit == "kib":
        multiplier = 1024
    elif unit in ("m", "mb"):
        multiplier = 1000**2
    elif unit == "mib":
        multiplier = 1024**2
    elif unit in ("g", "gb"):
        multiplier = 1000**3
    elif unit == "gib":
        multiplier = 1024**3
    elif unit in ("t", "tb"):
        multiplier = 1000**4
    elif unit == "tib":
        multiplier = 1024**4
    else:
        raise ValueError(f"Unknown memory unit: {unit}")

    return int(number * multiplier)


def wrap_with_prlimit(
    cmd: List[str], as_bytes: int = None, rss_bytes: int = None
) -> List[str]:
    """
    Wrap command with prlimit to set resource limits.

    Args:
        cmd: Command to run
        as_bytes: RLIMIT_AS (virtual memory) limit in bytes
        rss_bytes: RLIMIT_RSS limit in bytes (advisory on Linux)

    Returns:
        Wrapped command list
    """
    if (as_bytes is None or as_bytes <= 0) and (rss_bytes is None or rss_bytes <= 0):
        return cmd

    wrapper = ["prlimit"]
    if as_bytes is not None and as_bytes > 0:
        wrapper.append(f"--as={as_bytes}")
    if rss_bytes is not None and rss_bytes > 0:
        wrapper.append(f"--rss={rss_bytes}")
    wrapper.append("--")
    return wrapper + cmd


def wrap_with_ulimit(cmd: List[str], as_bytes: int = None) -> List[str]:
    """
    Wrap command with shell ulimit to set RLIMIT_AS.

    Args:
        cmd: Command to run
        as_bytes: RLIMIT_AS (virtual memory) limit in bytes

    Returns:
        Wrapped command list using sh -c
    """
    if as_bytes is None or as_bytes <= 0:
        return cmd

    # ulimit -v takes kilobytes, use ceiling division to avoid exceeding limit
    kb = (as_bytes + 1023) // 1024
    escaped_cmd = " ".join(shlex.quote(arg) for arg in cmd)
    return ["sh", "-c", f"ulimit -v {kb}; exec {escaped_cmd}"]


def wrap_with_cgexec(
    cmd: List[str], cgroup: str, controllers: str = "memory"
) -> List[str]:
    """
    Wrap command with cgexec to run in an existing cgroup.

    Args:
        cmd: Command to run
        cgroup: Name of existing cgroup (e.g., "limited_group")
        controllers: Cgroup controllers to use (default: "memory")

    Returns:
        Wrapped command list

    Note:
        The cgroup must already exist and have limits configured.
        Example setup:
            sudo cgcreate -g memory:/limited_group
            echo 100M | sudo tee /sys/fs/cgroup/memory/limited_group/memory.limit_in_bytes
    """
    if not cgroup:
        return cmd
    return ["cgexec", "-g", f"{controllers}:{cgroup}"] + cmd


def parse_memory_limit_with_multiplier(value, arg_name):
    """returns (absolute_bytes_or_minus_one_or_none, multiplier_or_none)"""
    if value is None:
        return None, None
    value_str = str(value).strip()
    if not value_str:
        return None, None
    lower_val = value_str.lower()
    if lower_val.endswith("x"):
        multiplier_str = lower_val[:-1].strip()
        if not multiplier_str:
            raise ValueError(
                f"{arg_name} multiplier must include a numeric value before 'x'"
            )
        try:
            multiplier = float(multiplier_str)
        except ValueError as exc:
            raise ValueError(
                f"{arg_name} multiplier '{value_str}' is not a valid number"
            ) from exc
        if multiplier <= 0:
            raise ValueError(f"{arg_name} multiplier '{value_str}' must be positive")
        return None, multiplier
    try:
        return parse_memory_bytes(value_str), None
    except ValueError as exc:
        raise ValueError(f"{arg_name} has invalid value '{value_str}': {exc}") from exc


def wrap_with_cgexec_and_create(
    cmd: List[str],
    mem_bytes: int,
    swap_bytes: int = 0,
    cgroup_name: str = None,
) -> Tuple[List[str], str]:
    """
    Create a cgroup v2 with memory limits and wrap command with cgexec.

    Args:
        cmd: Command to run
        mem_bytes: Memory limit in bytes
        swap_bytes: Swap limit in bytes (0 = no swap, -1 = unlimited)
        cgroup_name: Optional cgroup name (auto-generated if None)

    Returns:
        Tuple of (wrapped command list, cgroup path for cleanup)

    Raises:
        RuntimeError: If cgroup creation fails
    """
    if mem_bytes is None or mem_bytes <= 0:
        return cmd, None

    cg_root = "/sys/fs/cgroup"
    cg_name = cgroup_name or f"pyjob-{os.getpid()}"
    cg_path = os.path.join(cg_root, cg_name)

    try:
        os.makedirs(cg_path, exist_ok=True)
        with open(os.path.join(cg_path, "memory.max"), "w") as f:
            f.write(str(mem_bytes))
        with open(os.path.join(cg_path, "memory.swap.max"), "w") as f:
            f.write(str(swap_bytes) if swap_bytes >= 0 else "max")
        with open(os.path.join(cg_path, "memory.oom.group"), "w") as f:
            f.write("1")
    except (OSError, IOError) as e:
        raise RuntimeError(f"Failed to set up cgroup at {cg_path}: {e}")

    wrapped_cmd = ["cgexec", "-g", f"memory:{cg_name}"] + cmd
    return wrapped_cmd, cg_path


def wrap_with_systemd_run(
    cmd: List[str],
    mem_bytes: int = None,
    as_bytes: int = None,
    swap_bytes: int = None,
    scope_name: str = None,
) -> List[str]:
    """
    Wrap command with systemd-run to set memory limits via cgroup.

    Args:
        cmd: Command to run
        mem_bytes: MemoryMax limit in bytes (hard RSS limit)
        as_bytes: LimitAS (virtual memory) limit in bytes
        swap_bytes: MemorySwapMax limit in bytes
        scope_name: Optional name for the transient scope unit

    Returns:
        Wrapped command list

    Note:
        Requires systemd and user session (--user) or root privileges.
    """
    has_limits = any(v is not None and v > 0 for v in [mem_bytes, as_bytes, swap_bytes])
    if not has_limits:
        return cmd

    wrapper = ["systemd-run", "--user", "--scope", "--quiet"]

    if scope_name:
        wrapper.append(f"--unit={scope_name}")

    if mem_bytes is not None and mem_bytes > 0:
        wrapper.append(f"--property=MemoryMax={mem_bytes}")

    if as_bytes is not None and as_bytes > 0:
        wrapper.append(f"--property=LimitAS={as_bytes}")

    if swap_bytes is not None and swap_bytes > 0:
        wrapper.append(f"--property=MemorySwapMax={swap_bytes}")

    wrapper.append("--")
    return wrapper + cmd


def cleanup_cgroup(cg_path: str) -> None:
    """
    Clean up a cgroup directory.

    Args:
        cg_path: Path to cgroup directory to remove
    """
    if cg_path is None:
        return
    try:
        shutil.rmtree(cg_path, ignore_errors=True)
    except Exception:
        pass


# Memory limit method enum for CLI
MEMORY_LIMIT_METHODS = ["prlimit", "ulimit", "cgexec", "systemd-run", "none"]


def apply_memory_limit(
    cmd: List[str],
    method: str,
    as_bytes: int = None,
    rss_bytes: int = None,
    swap_bytes: int = None,
    cgroup: str = None,
) -> Tuple[List[str], str]:
    """
    Apply memory limits to a command using the specified method.

    Args:
        cmd: Command to run
        method: One of "prlimit", "ulimit", "cgexec", "systemd-run", "none"
        as_bytes: Virtual memory (RLIMIT_AS) limit in bytes
        rss_bytes: RSS memory limit in bytes
        swap_bytes: Swap limit in bytes
        cgroup: Existing cgroup name (for cgexec method)

    Returns:
        Tuple of (wrapped command, cgroup_path or None)
        cgroup_path is only set when method creates a new cgroup that needs cleanup

    Raises:
        ValueError: If method is unknown or invalid configuration
    """
    method = method.lower() if method else "none"

    if method == "none":
        return cmd, None

    elif method == "prlimit":
        return wrap_with_prlimit(cmd, as_bytes=as_bytes, rss_bytes=rss_bytes), None

    elif method == "ulimit":
        if rss_bytes is not None and rss_bytes > 0:
            raise ValueError(
                "ulimit method only supports --max-mem-as, not --max-mem-rss"
            )
        return wrap_with_ulimit(cmd, as_bytes=as_bytes), None

    elif method == "cgexec":
        if cgroup:
            # Use existing cgroup
            return wrap_with_cgexec(cmd, cgroup), None
        elif rss_bytes is not None and rss_bytes > 0:
            # Create new cgroup with limits
            return wrap_with_cgexec_and_create(cmd, rss_bytes, swap_bytes or 0)
        else:
            raise ValueError("cgexec method requires --cgroup or --max-mem-rss")

    elif method == "systemd-run":
        return wrap_with_systemd_run(
            cmd, mem_bytes=rss_bytes, as_bytes=as_bytes, swap_bytes=swap_bytes
        ), None

    else:
        raise ValueError(
            f"Unknown memory limit method: {method}. "
            f"Valid options: {', '.join(MEMORY_LIMIT_METHODS)}"
        )


if __name__ == "__main__":
    # if we're working in Python 3.3, we can test this file
    try:
        import doctest

        success = True
    except ImportError:
        print(
            "This is not the main file to use.\nOnly run it if you have doctest (Python 3.3+) and are testing things."
        )
        success = False
    if success:
        doctest.testmod()
