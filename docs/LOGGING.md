# Kind-Based Logging System

## Overview

The logging system now supports kind-based logging in addition to traditional level-based logging. This provides more fine-grained control over what gets logged, while maintaining backwards compatibility.

## Features

### 1. Kind-Based Logging

Instead of (or in addition to) specifying a verbosity level, you can now specify a "kind" for each log message:

```python
log("Processing file", kind="info")
log("Detailed trace info", kind="debug.trace")
```

### 2. Kind Hierarchies

Kinds can be hierarchical using dot notation. For example:
- `debug` includes `debug.trace`, `debug.info`, `debug.detail`, etc.
- `all` includes everything

When you enable a kind like `debug`, all sub-kinds like `debug.trace` are automatically included.

### 3. Default Verbosity Levels for Kinds

Each kind has a default verbosity level defined in `DEFAULT_KIND_VERBOSITY`:

```python
DEFAULT_KIND_VERBOSITY = {
    "error": 0,           # Always log errors
    "warning": 1,         # Log warnings at default verbosity
    "info": 1,            # Log info at default verbosity
    "debug": 2,           # Log debug info at verbosity 2
    "debug.detail": 3,    # Log detailed debug info at verbosity 3
    "debug.trace": 4,     # Log trace-level debug at verbosity 4
    "command": 2,         # Log commands being run at verbosity 2
    "contents": 2,        # Log file contents at verbosity 2
    "cache": 3,           # Log cache operations at verbosity 3
}
```

When a log message has a kind but no explicit level, the default verbosity for that kind is used to determine if it should be logged.

### 4. Kind Suffix

You can build composite kinds using the `kind_suffix` parameter:

```python
log("Debug message", kind="debug", kind_suffix="context")
# This logs with kind "debug.context"
```

This is useful when passing a base kind through function parameters and adding context-specific suffixes.

### 5. Command-Line Control

You can enable or disable specific kinds from the command line:

```bash
# Enable debug logging
./script.py --log-class debug

# Enable debug logging to a specific file
./script.py --log-class debug,debug.log

# Disable error logging
./script.py --disable-log-class error

# Disable debug logging to a specific file
./script.py --disable-log-class debug,debug.log
```

## Usage Examples

### Basic Kind-Based Logging

```python
from coq_tools.custom_arguments import ArgumentParser, add_logging_arguments, process_logging_arguments

parser = ArgumentParser()
add_logging_arguments(parser)
args = parser.parse_args()
process_logging_arguments(args)

# Use kinds for different types of messages
args.log("Starting process", kind="info")
args.log("Processing file X", kind="debug")
args.log("Detailed trace info", kind="debug.trace")
args.log("An error occurred", kind="error")
```

### Enabling Specific Kinds

```python
# Command line: --log-class debug
# This enables all debug.* kinds

args.log("This will be logged", kind="debug")
args.log("This will also be logged", kind="debug.trace")
args.log("This will NOT be logged", kind="info")
```

### Hierarchical Kinds

The system supports prefix-based hierarchies. When you enable a kind like `debug`, it automatically includes:
- `debug` (exact match)
- `debug.trace`
- `debug.info`
- `debug.detail`
- Any other kind starting with `debug.`

The special kind `all` includes everything.

### Migration from Level-Based to Kind-Based Logging

Old style (still supported):
```python
log("Debug message", level=2)
log("Detailed debug", level=3)
```

New style (recommended):
```python
log("Debug message", kind="debug")
log("Detailed debug", kind="debug.detail")
```

The new style provides:
- Better semantic clarity
- More flexible filtering
- Hierarchical grouping
- Command-line control without changing code

## Backwards Compatibility

All existing level-based logging continues to work exactly as before. The kind-based system is additive and doesn't break any existing functionality.

When both `level` and `kind` are specified:
- If the kind is explicitly enabled/disabled, that takes precedence
- Otherwise, the default verbosity level for the kind is used
- If the kind has no default, the explicit level is used

## Implementation Details

The kind-based logging system is implemented in `coq_tools/custom_arguments.py`:

- `DEFAULT_KIND_VERBOSITY`: Dictionary mapping kinds to their default verbosity levels
- `KIND_INCLUDES`: Dictionary mapping kinds to their included sub-kinds
- `check_kind_inclusion(configured_kind, log_kind)`: Function to check if one kind includes another
- `log(..., kind=None, kind_suffix=None)`: Enhanced log function with kind support

## Future Work

As part of ongoing improvements:
1. Migrate existing `verbose_base` parameters to use `kind_suffix`
2. Convert more log calls from level-based to kind-based
3. Add more semantic kinds as needed
4. Potentially deprecate level-based logging in favor of kind-based
