#!/usr/bin/env bash

# This script wraps coqc + coqchk to make coqchk errors appear like coqc errors.
# Usage: coqchk-as-coqc.sh <coqc> <coqchk> [args...]
#
# It runs coqc on the arguments, then runs coqchk -o -silent on the resulting .vo files.
# If coqchk outputs a line starting with "Fatal Error:", it emits a fake Coq error
# location pointing to the end of the .v file before that line.
#
# Arguments are categorized:
# - Both coqc and coqchk: -I, --include, -Q, -R, -coqlib, --coqlib,
#   -impredicative-set, --impredicative-set, -indices-matter, --indices-matter,
#   -bytecode-compiler, --bytecode-compiler, -debug, -d, --debug, -boot, --boot
# - coqchk only: -admit, --admit, -norec, --norec, -o, --output-context,
#   -m, --memory, -silent, --silent
# - .v files: coqc gets .v, coqchk gets .vo
# - Everything else: coqc only

set -o pipefail

coqc="$1"
shift
coqchk="$1"
shift

# Arrays for categorized arguments
coqc_args=()
chk_args=()
v_file=""

# Parse arguments
while [ $# -gt 0 ]; do
    arg="$1"
    case "$arg" in
        # Arguments with one parameter that go to BOTH
        -I|--include|-coqlib|--coqlib|-bytecode-compiler|--bytecode-compiler|-d)
            coqc_args+=("$arg" "$2")
            chk_args+=("$arg" "$2")
            shift 2
            ;;
        # Arguments with two parameters that go to BOTH
        -Q|-R)
            coqc_args+=("$arg" "$2" "$3")
            chk_args+=("$arg" "$2" "$3")
            shift 3
            ;;
        # Flag arguments (no parameter) that go to BOTH
        -impredicative-set|--impredicative-set|-indices-matter|--indices-matter|-debug|--debug|-boot|--boot)
            coqc_args+=("$arg")
            chk_args+=("$arg")
            shift
            ;;
        # Arguments with one parameter that go to coqchk ONLY
        -admit|--admit|-norec|--norec)
            chk_args+=("$arg" "$2")
            shift 2
            ;;
        # Flag arguments (no parameter) that go to coqchk ONLY
        -o|--output-context|-m|--memory|-silent|--silent)
            chk_args+=("$arg")
            shift
            ;;
        # .v files: coqc gets .v, coqchk gets .vo
        *.v)
            v_file="$arg"
            coqc_args+=("$arg")
            chk_args+=("${arg%.v}.vo")
            shift
            ;;
        # Everything else goes to coqc ONLY
        *)
            coqc_args+=("$arg")
            shift
            ;;
    esac
done

# Run coqc first
"$coqc" "${coqc_args[@]}"
coqc_exit=$?

if [ $coqc_exit -ne 0 ]; then
    exit $coqc_exit
fi

# Function to process output and insert error preamble before "Fatal Error:" lines
process_output() {
    local v_file="$1"
    local line_count=0

    # Count lines in v_file if it exists
    if [ -n "$v_file" ] && [ -f "$v_file" ]; then
        line_count=$(wc -l < "$v_file" | tr -d ' ')
    fi

    while IFS= read -r line || [ -n "$line" ]; do
        if [[ "$line" == Fatal\ Error:* ]]; then
            # Emit fake Coq error location before the Fatal Error line
            if [ -n "$v_file" ]; then
                echo "File \"$v_file\", line $line_count, characters 0-0:"
                echo "Error:"
            fi
        fi
        echo "$line"
    done
}

# Export the function and v_file for use in subshells
export -f process_output
export v_file

# Run coqchk with -o -silent, processing stdout and stderr separately
# Use fd 3 to swap stdout and stderr, process each through process_output,
# then swap back so stdout goes to stdout and stderr goes to stderr
{
    {
        "$coqchk" -o -silent "${chk_args[@]}" 2>&1 1>&3 | process_output "$v_file" >&2
    } 3>&1 | process_output "$v_file"
} 3>&-

exit ${PIPESTATUS[0]}
