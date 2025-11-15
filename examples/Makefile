# Options passed on the command line
ERROR_ON_FAILURE=1
V = 0
CAT_ALL_LOGS=0
####

DEFAULT_TESTS = 000 001 002 003 004 005 007 008 008-2 008-3 009 011 012 014 015 016 017 019 021 022 023 024 025 028 029 030 031 035 036 037 038 040 041 043 045 047 050 051 060 062 064 065 066 068 071
CONDITIONAL_TESTS = 006 018

ONLY_IF_COQTOP_COMPILE_TESTS =
ONLY_IF_Q_TESTS = 010 026
ONLY_IF_TYPE_IN_TYPE_WORKS_TESTS =
ONLY_IF_Q_AND_TYPE_IN_TYPE_WORKS_TESTS = 073
ONLY_IF_TOP_TESTS = 063
ONLY_IF_PROOF_USING_TESTS = 067 069
ONLY_IF_W_TESTS = 044
ONLY_IF_W_AND_GE_815_TESTS = 046
ONLY_IF_W_AND_UNSET_TESTS = 057 058
ONLY_IF_FROM_TESTS = 013 027 032 033 034 039 042
ONLY_IF_FROM_AND_IMPORT_CATEGORIES_TESTS = 061
ONLY_IF_FROM_AND_VOS_TESTS = 059
ONLY_IF_GLOB_IMPORT_TESTS = 052 053 054
ONLY_IF_GT_84_TESTS = 020 049
ONLY_IF_GE_812_TESTS = 048
ONLY_IF_SYS_V_FILES_TESTS = 055
ONLY_IF_SYS_GLOB_FILES_GOOD_TESTS =
ONLY_IF_SYS_GLOB_FILES_GOOD_AND_CAN_INLINE_COQ_INIT_LOGIC_TESTS = 056
ONLY_IF_CUSTOM_ENTRY_TESTS = 070
ONLY_IF_LTAC2_TESTS =
ONLY_IF_LTAC2_LIST_MAP_TESTS = 072
ONLY_IF_RESOURCE_MODULE_TESTS =
ONLY_IF_RLIMIT_AS_TESTS = 075
CONDITIONAL_TESTS += \
	$(ONLY_IF_Q_TESTS) \
	$(ONLY_IF_TYPE_IN_TYPE_WORKS_TESTS) \
	$(ONLY_IF_Q_AND_TYPE_IN_TYPE_WORKS_TESTS) \
	$(ONLY_IF_TOP_TESTS) \
	$(ONLY_IF_PROOF_USING_TESTS) \
	$(ONLY_IF_W_TESTS) \
	$(ONLY_IF_W_AND_GE_815_TESTS) \
	$(ONLY_IF_W_AND_UNSET_TESTS) \
	$(ONLY_IF_FROM_TESTS) \
	$(ONLY_IF_FROM_AND_IMPORT_CATEGORIES_TESTS) \
	$(ONLY_IF_FROM_AND_VOS_TESTS) \
	$(ONLY_IF_GLOB_IMPORT_TESTS) \
	$(ONLY_IF_GT_84_TESTS) \
	$(ONLY_IF_GE_812_TESTS) \
	$(ONLY_IF_SYS_V_FILES_TESTS) \
	$(ONLY_IF_SYS_GLOB_FILES_GOOD_TESTS) \
	$(ONLY_IF_SYS_GLOB_FILES_GOOD_AND_CAN_INLINE_COQ_INIT_LOGIC_TESTS) \
	$(ONLY_IF_CUSTOM_ENTRY_TESTS) \
	$(ONLY_IF_LTAC2_TESTS) \
	$(ONLY_IF_LTAC2_LIST_MAP_TESTS) \
	$(ONLY_IF_RESOURCE_MODULE_TESTS) \
	$(ONLY_IF_RLIMIT_AS_TESTS) \
	#

MAIN_RUNS = $(patsubst %,run-example-%.sh,$(DEFAULT_TESTS) $(CONDITIONAL_TESTS) $(BROKEN_TESTS))
OTHER_RUNS = run-example-008.py
IGNORE = prefix-grep.py disable-parallel-make.sh init-settings.sh init-simple-settings.sh memoize.py

DEFAULT_LOGS = $(patsubst %,example_%_result.log,$(DEFAULT_TESTS))
CONDITIONAL_LOGS = $(patsubst %,example_%_result.log,$(CONDITIONAL_TESTS))
BROKEN_LOGS = $(patsubst %,example_%_result.log,$(BROKEN_TESTS))
ALL_LOGS = $(DEFAULT_LOGS) $(CONDITIONAL_LOGS) $(BROKEN_LOGS)
ONLY_IF_COQTOP_COMPILE_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_COQTOP_COMPILE_TESTS))
ONLY_IF_Q_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_Q_TESTS))
ONLY_IF_TYPE_IN_TYPE_WORKS_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_TYPE_IN_TYPE_WORKS_TESTS))
ONLY_IF_Q_AND_TYPE_IN_TYPE_WORKS_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_Q_AND_TYPE_IN_TYPE_WORKS_TESTS))
ONLY_IF_TOP_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_TOP_TESTS))
ONLY_IF_PROOF_USING_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_PROOF_USING_TESTS))
ONLY_IF_W_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_W_TESTS))
ONLY_IF_W_AND_GE_815_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_W_AND_GE_815_TESTS))
ONLY_IF_W_AND_UNSET_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_W_AND_UNSET_TESTS))
ONLY_IF_FROM_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_FROM_TESTS))
ONLY_IF_FROM_AND_IMPORT_CATEGORIES_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_FROM_AND_IMPORT_CATEGORIES_TESTS))
ONLY_IF_FROM_AND_VOS_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_FROM_AND_VOS_TESTS))
ONLY_IF_GLOB_IMPORT_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_GLOB_IMPORT_TESTS))
ONLY_IF_GT_84_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_GT_84_TESTS))
ONLY_IF_GE_812_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_GE_812_TESTS))
ONLY_IF_SYS_V_FILES_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_SYS_V_FILES_TESTS))
ONLY_IF_SYS_GLOB_FILES_GOOD_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_SYS_GLOB_FILES_GOOD_TESTS))
ONLY_IF_SYS_GLOB_FILES_GOOD_AND_CAN_INLINE_COQ_INIT_LOGIC_TESTS_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_SYS_GLOB_FILES_GOOD_AND_CAN_INLINE_COQ_INIT_LOGIC_TESTS))
ONLY_IF_CUSTOM_ENTRY_TESTS_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_CUSTOM_ENTRY_TESTS))
ONLY_IF_LTAC2_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_LTAC2_TESTS))
ONLY_IF_LTAC2_LIST_MAP_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_LTAC2_LIST_MAP_TESTS))
ONLY_IF_RESOURCE_MODULE_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_RESOURCE_MODULE_TESTS))
ONLY_IF_RLIMIT_AS_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_RLIMIT_AS_TESTS))
ENABLED_LOGS = $(DEFAULT_LOGS)
DISABLED_LOGS = $(filter-out $(ENABLED_LOGS),$(ALL_LOGS)) # important for this to be =, not :=, so it gets set late

.DEFAULT_GOAL := test-suite
.SECONDEXPANSION:

# Order the builds for 8 so they don't run in parallel
example_008-2_result.log: | example_008_result.log
example_008-3_result.log: | example_008-2_result.log

# some makefile magic to make things less noisy unless you do `make V=1`
Q_0 := @
Q_1 :=
Q = $(Q_$(V))

VECHO_0 := @echo
VECHO_1 := @true
VECHO = $(VECHO_$(V))

VECHON_0 := @echo -n
VECHON_1 := @true
VECHON = $(VECHON_$(V))

# inner vecho, without the @
VIECHO_0 := echo
VIECHO_1 := true
VIECHO = $(VIECHO_$(V))

RED=\033[0;31m
# No Color
NC=\033[0m
GREEN=\033[0;32m
YELLOW=\033[0;33m
BOLD=$(shell tput bold)
NORMAL=$(shell tput sgr0)

MAKEFILE_DIR:=$(dir $(abspath $(lastword $(MAKEFILE_LIST))))

COQC_VERSION:=$(subst version ,,$(shell $(COQBIN)coqc -q --version 2>&1 | grep -o 'version [^ ]*'))
COQC_SUPPORTS_Q:=$(shell $(COQBIN)coqc -q --help 2>&1 | grep -c -- -Q)
COQC_SUPPORTS_TOP:=$(shell { $(COQBIN)coqc -q -top foo empty.v 2>&1 | grep -q -- "-top: no such file or directory"; } && echo 0 || echo 1)
COQTOP_SUPPORTS_TOP:=$(shell { true | $(COQBIN)coqtop -q -top foo 2>&1 | grep -q -- "-top: no such file or directory"; } && echo 0 || echo 1)
COQTOP_SUPPORTS_COMPILE:=$(shell $(COQBIN)coqtop -q --help 2>&1 | tr '\n' '~' | sed s'/Deprecated options.*//g' | tr '~' '\n' | grep -c -- '\s-compile\s')
COQC_SUPPORTS_FROM:=$(shell echo "From Coq.Init Require Import Notations." | $(COQBIN)coqtop -q 2>&1 | grep -q 'Error'; echo $$?)
COQC_SUPPORTS_CUSTOM_ENTRY:=$(shell echo "Declare Custom Entry foo." | $(COQBIN)coqtop -q 2>&1 | grep -q 'Error\|Syntax error'; echo $$?)
COQC_SUPPORTS_LTAC2:=$(shell echo "Require Import Ltac2.Ltac2." | $(COQBIN)coqtop -q 2>&1 | grep -q 'Error'; echo $$?)
COQC_SUPPORTS_LTAC2_LIST_MAP:=$(shell echo "Require Import Ltac2.Ltac2. Ltac2 Eval List.map." | $(COQBIN)coqtop -q 2>&1 | grep -q 'Error'; echo $$?)
COQC_SUPPORTS_PROOF_USING:=$(shell printf "Section foo.\nVariable x : nat.\nDefinition bar : nat.\nProof using x.\nAdmitted.\nEnd foo.\n" | $(COQBIN)coqtop -q 2>&1 | grep -q 'Error'; echo $$?)
COQC_SUPPORTS_RESOURCE_MODULE:=$(shell . "$(MAKEFILE_DIR)/init-simple-settings.sh"; $${PYTHON} -c "$$(printf 'try:\n    import resource\n    print(1)\nexcept ImportError:\n    print(0)')" 2>&1)
COQC_SUPPORTS_RLIMIT_AS:=$(shell . "$(MAKEFILE_DIR)/init-simple-settings.sh"; $${PYTHON} -c "$$(printf 'try:\n    import resource\n    bytes_=500*1024*1024\n    resource.setrlimit(resource.RLIMIT_AS, (bytes_, bytes_))\n    print(1)\nexcept (RuntimeError, ImportError, OSError, ValueError):\n    print(0)')" 2>&1)
COQC_SUPPORTS_SUGGEST_PROOF_USING:=$(shell printf "Set Suggest Proof Using.\n" | $(COQBIN)coqtop -q 2>&1 | grep -q 'There is no option Suggest Proof Using.'; echo $$?)
COQC_SUPPORTS_IMPORT_CATEGORIES:=$(shell echo "Require Import (hints) Coq.Init.Notations." | $(COQBIN)coqtop -q 2>&1 | grep -q 'Error\|Syntax error'; echo $$?)
COQC_SUPPORTS_W:=$(shell $(COQBIN)coqtop -q --help 2>&1 | grep -c -- '-w ')
COQC_SUPPORTS_VOS:=$(shell $(COQBIN)coqc -q --help 2>&1 | grep -c -- '-vos ')
COQC_SUPPORTS_UNSET:=$(shell $(COQBIN)coqtop -q --help 2>&1 | grep -c -- '-unset ')
COQC_TYPE_IN_TYPE_WORKS:=$(shell printf "Check Set : Set." | $(COQBIN)coqtop -q -type-in-type 2>&1 | grep -q 'Error'; echo $$?)
COQC_COQLIB:=$(shell $(COQBIN)coqc -q -config 2>&1 | grep -o 'COQLIB=.*' | sed s'/^COQLIB=//g')
COQLIB_V_FILES:=$(wildcard $(COQC_COQLIB)/theories/Init/*.v)
COQLIB_GLOB_FILES:=$(wildcard $(COQC_COQLIB)/theories/Init/*.glob)
COQLIB_PRELUDE_V_FILE:=$(wildcard $(COQC_COQLIB)/theories/Init/Prelude.v)
COQLIB_PRELUDE_GLOB_FILE:=$(wildcard $(COQC_COQLIB)/theories/Init/Prelude.glob)

.PHONY: check
check::
	@printf "Running with PYTHON=$(GREEN)"
	@bash -c '. "$(MAKEFILE_DIR)/init-settings.sh"; printf '%s' "$${PYTHON}"'
	@printf "$(NC) ($(GREEN)"
	@bash -c '. "$(MAKEFILE_DIR)/init-settings.sh"; printf '%s' "$$(which "$${PYTHON}")"'
	@printf "$(NC)) (based on $(GREEN)%s$(NC))\n" "$${PYTHON}"
	@printf "Running with FIND_BUG='%s'\n" "$(FIND_BUG)"
	$(MAKE) -B test-suite

.PHONY: print-support
print-support::

ifeq (1,$(CAT_ALL_LOGS))
check::
	$(MAKE) test-suite-verbose-report
else
check::
	$(MAKE) test-suite-report
endif

.PHONY: test-suite
test-suite: $(DEFAULT_LOGS)

ifneq (0,$(strip $(COQTOP_SUPPORTS_COMPILE)))
test-suite: $(ONLY_IF_COQTOP_COMPILE_LOGS)
ENABLED_LOGS += $(ONLY_IF_COQTOP_COMPILE_LOGS)
print-support::
	@printf "coqtop supports -compile:\t\t\tYes\n"
else
print-support::
	@printf "coqtop supports -compile:\t\t\tNo\n"
endif

ifneq (0,$(strip $(COQC_SUPPORTS_Q)))
test-suite: $(ONLY_IF_Q_LOGS)
ENABLED_LOGS += $(ONLY_IF_Q_LOGS)
print-support::
	@printf "coqc supports -Q:\t\t\t\tYes\n"
else
print-support::
	@printf "coqc supports -Q:\t\t\t\tNo\n"
endif

ifneq (0,$(strip $(COQC_TYPE_IN_TYPE_WORKS)))
test-suite: $(ONLY_IF_TYPE_IN_TYPE_WORKS_LOGS)
ENABLED_LOGS += $(ONLY_IF_TYPE_IN_TYPE_WORKS_LOGS)
print-support::
	@printf "coqc supports Set:Set with -type-in-type:\tYes\n"
ifneq (0,$(strip $(COQC_SUPPORTS_Q)))
test-suite: $(ONLY_IF_Q_AND_TYPE_IN_TYPE_WORKS_LOGS)
ENABLED_LOGS += $(ONLY_IF_Q_AND_TYPE_IN_TYPE_WORKS_LOGS)
endif
else
print-support::
	@printf "coqc supports Set:Set with -type-in-type:\tNo\n"
endif

ifneq (0,$(strip $(COQC_SUPPORTS_PROOF_USING)))
print-support::
	@printf "coqc supports Proof using:\t\t\tYes\n"
ifneq (0,$(strip $(COQC_SUPPORTS_SUGGEST_PROOF_USING)))
test-suite: $(ONLY_IF_PROOF_USING_LOGS)
ENABLED_LOGS += $(ONLY_IF_PROOF_USING_LOGS)
print-support::
	@printf "coqc supports Set Suggest Proof using:\t\tYes\n"
else
print-support::
	@printf "coqc supports Set Suggest Proof using:\t\tNo\n"
endif
else
print-support::
	@printf "coqc supports Proof using:\t\t\tNo\n"
endif

ifneq (0,$(strip $(COQTOP_SUPPORTS_TOP)))
print-support::
	@printf "coqtop supports -top:\t\t\t\tYes\n"
else
print-support::
	@printf "coqtop supports -top:\t\t\t\tNo\n"
endif

ifneq (0,$(strip $(COQC_SUPPORTS_TOP)))
print-support::
	@printf "coqc supports -top:\t\t\t\tYes\n"
else
print-support::
	@printf "coqc supports -top:\t\t\t\tNo\n"
endif

ifneq (0,$(strip $(COQC_SUPPORTS_TOP)))
ifneq (0,$(strip $(COQTOP_SUPPORTS_TOP)))
test-suite: $(ONLY_IF_TOP_LOGS)
ENABLED_LOGS += $(ONLY_IF_TOP_LOGS)
endif
endif

ifneq (0,$(strip $(COQC_SUPPORTS_W)))
test-suite: $(ONLY_IF_W_LOGS)
ENABLED_LOGS += $(ONLY_IF_W_LOGS)
print-support::
	@printf "coqc supports -w:\t\t\t\tYes\n"
else
print-support::
	@printf "coqc supports -w:\t\t\t\tNo\n"
endif

ifneq (0,$(strip $(COQC_SUPPORTS_FROM)))
test-suite: $(ONLY_IF_FROM_LOGS)
ENABLED_LOGS += $(ONLY_IF_FROM_LOGS)
print-support::
	@printf "coqc supports From ... Require ...:\t\tYes\n"
else
print-support::
	@printf "coqc supports From ... Require ...:\t\tNo\n"
endif

ifneq (0,$(strip $(COQC_SUPPORTS_IMPORT_CATEGORIES)))
ifneq (0,$(strip $(COQC_SUPPORTS_FROM)))
test-suite: $(ONLY_IF_FROM_AND_IMPORT_CATEGORIES_LOGS)
ENABLED_LOGS += $(ONLY_IF_FROM_AND_IMPORT_CATEGORIES_LOGS)
endif
print-support::
	@printf "coqc supports Import|Export categories:\t\tYes\n"
else
print-support::
	@printf "coqc supports Import|Export categories:\t\tNo\n"
endif


ifneq (0,$(strip $(COQC_SUPPORTS_VOS)))
ifneq (0,$(strip $(COQC_SUPPORTS_FROM)))
test-suite: $(ONLY_IF_FROM_AND_VOS_LOGS)
ENABLED_LOGS += $(ONLY_IF_FROM_AND_VOS_LOGS)
endif
print-support::
	@printf "coqc supports -vos:\t\t\t\tYes\n"
else
print-support::
	@printf "coqc supports -vos:\t\t\t\tNo\n"
endif

ifneq (0,$(strip $(COQC_SUPPORTS_CUSTOM_ENTRY)))
test-suite: $(ONLY_IF_CUSTOM_ENTRY_TESTS_LOGS)
ENABLED_LOGS += $(ONLY_IF_CUSTOM_ENTRY_TESTS_LOGS)
print-support::
	@printf "coqc supports Declare Custom Entry:\t\tYes\n"
else
print-support::
	@printf "coqc supports Declare Custom Entry:\t\tNo\n"
endif

ifneq (0,$(strip $(COQC_SUPPORTS_LTAC2)))
test-suite: $(ONLY_IF_LTAC2_LOGS)
ENABLED_LOGS += $(ONLY_IF_LTAC2_LOGS)
print-support::
	@printf "coqc supports Ltac2:\t\t\t\tYes\n"
else
print-support::
	@printf "coqc supports Ltac2:\t\t\t\tNo\n"
endif

ifneq (0,$(strip $(COQC_SUPPORTS_LTAC2_LIST_MAP)))
test-suite: $(ONLY_IF_LTAC2_LIST_MAP_LOGS)
ENABLED_LOGS += $(ONLY_IF_LTAC2_LIST_MAP_LOGS)
print-support::
	@printf "coqc supports Ltac2 List.map:\t\t\tYes\n"
else
print-support::
	@printf "coqc supports Ltac2 List.map:\t\t\tNo\n"
endif

ifneq (0,$(strip $(COQC_SUPPORTS_RESOURCE_MODULE)))
test-suite: $(ONLY_IF_RESOURCE_MODULE_LOGS)
ENABLED_LOGS += $(ONLY_IF_RESOURCE_MODULE_LOGS)
print-support::
	@printf "Python resource module importable:\t\tYes\n"
else
print-support::
	@printf "Python resource module importable:\t\tNo\n"
endif

ifneq (0,$(strip $(COQC_SUPPORTS_RLIMIT_AS)))
test-suite: $(ONLY_IF_RLIMIT_AS_LOGS)
ENABLED_LOGS += $(ONLY_IF_RLIMIT_AS_LOGS)
print-support::
	@printf "Python supports RLIMIT_AS (500MB):\t\tYes\n"
else
print-support::
	@printf "Python supports RLIMIT_AS (500MB):\t\tNo\n"
endif

ifeq (,$(strip $(COQLIB_PRELUDE_V_FILE)))
print-support::
	@printf "coqc installs stdlib .v files:\t\t\tNo\n"
else
test-suite: $(ONLY_IF_SYS_V_FILES_LOGS)
ENABLED_LOGS += $(ONLY_IF_SYS_V_FILES_LOGS)
print-support::
	@printf "coqc installs stdlib .v files:\t\t\tYes\n"

ifeq (,$(strip $(COQLIB_PRELUDE_GLOB_FILE)))
print-support::
	@printf "coqc installs stdlib .glob files:\t\tNo\n"
else
print-support::
	@printf "coqc installs stdlib .glob files:\t\tYes\n"


COQLIB_PRELUDE_GLOB_FILE_NEWER:=$(shell . "$(MAKEFILE_DIR)/init-simple-settings.sh"; $${PYTHON} -c 'import sys, os; m1, m2 = os.stat(os.sys.argv[1]).st_mtime, os.stat(os.sys.argv[2]).st_mtime; print(m1 < m2 or "%s <= %s" % (m2, m1))' "$(COQLIB_PRELUDE_V_FILE)" "$(COQLIB_PRELUDE_GLOB_FILE)" 2>&1)
ifeq (True,$(strip $(COQLIB_PRELUDE_GLOB_FILE_NEWER)))
test-suite: $(ONLY_IF_SYS_GLOB_FILES_GOOD_LOGS)
ENABLED_LOGS += $(ONLY_IF_SYS_GLOB_FILES_GOOD_LOGS)
print-support::
	@printf "coqlib has correctly timestampped .glob files:\tYes\n"

ifeq (,$(strip $(filter 8.5% 8.6% 8.10%,$(COQC_VERSION))))
test-suite: $(ONLY_IF_SYS_GLOB_FILES_GOOD_AND_CAN_INLINE_COQ_INIT_LOGIC_TESTS_LOGS)
ENABLED_LOGS += $(ONLY_IF_SYS_GLOB_FILES_GOOD_AND_CAN_INLINE_COQ_INIT_LOGIC_TESTS_LOGS)
print-support::
	@printf "can inline Coq.Init.Logic:\t\t\tYes\n"
else
ifneq (,$(strip $(filter 8.5% 8.6%,$(COQC_VERSION))))
print-support::
	@printf "can inline Coq.Init.Logic:\t\t\tNo (Coq 8.5, 8.6 (%s) errors with a message about replace)\n" '$(COQC_VERSION)'
else
print-support::
	@printf "can inline Coq.Init.Logic:\t\t\tNo (Coq 8.10 (%s) errors with missing eq_sind elim)\n" '$(COQC_VERSION)'
endif
endif

else
print-support::
	@printf "coqlib has correctly timestampped .glob files:\tNo (%s)\n" "$(COQLIB_PRELUDE_GLOB_FILE_NEWER)"
endif

endif

endif

ifneq (0,$(strip $(COQC_SUPPORTS_UNSET)))
ifneq (0,$(strip $(COQC_SUPPORTS_W)))
test-suite: $(ONLY_IF_W_AND_UNSET_LOGS)
ENABLED_LOGS += $(ONLY_IF_W_AND_UNSET_LOGS)
endif
print-support::
	@printf "coqc supports -unset:\t\t\t\tYes\n"
else
print-support::
	@printf "coqc supports -unset:\t\t\t\tNo\n"
endif

ifeq (,$(strip $(filter 8.3% 8.4% 8.5% 8.6% 8.7% 8.8% 8.9% 8.10% 8.11% 8.12% 8.13% 8.14%,$(COQC_VERSION))))
ifneq (0,$(strip $(COQC_SUPPORTS_W)))
test-suite: $(ONLY_IF_W_AND_GE_815_LOGS)
ENABLED_LOGS += $(ONLY_IF_W_AND_GE_815_LOGS)
endif
test-suite: $(ONLY_IF_GLOB_IMPORT_LOGS)
ENABLED_LOGS += $(ONLY_IF_GLOB_IMPORT_LOGS)
print-support::
	@printf "coqc emits globalization info for Imports:\tYes\n"
	@printf "coqc is < 8.15:\t\t\t\t\tNo\n"
else
print-support::
	@printf "coqc emits globalization info for Imports:\tNo\n"
	@printf "coqc is < 8.15:\t\t\t\t\tYes\n"
endif

ifeq (,$(strip $(filter 8.3% 8.4% 8.5% 8.6% 8.7% 8.8% 8.9% 8.10% 8.11%,$(COQC_VERSION))))
test-suite: $(ONLY_IF_GE_812_LOGS)
ENABLED_LOGS += $(ONLY_IF_GE_812_LOGS)
print-support::
	@printf "coqc is < 8.12:\t\t\t\t\tNo\n"
else
print-support::
	@printf "coqc is < 8.12:\t\t\t\t\tYes\n"
endif

ifeq (,$(strip $(filter 8.3% 8.4%,$(COQC_VERSION))))
test-suite: $(ONLY_IF_GT_84_LOGS)
ENABLED_LOGS += $(ONLY_IF_GT_84_LOGS)
print-support::
	@printf "coqc is 8.3 or 8.4:\t\t\t\tNo\n"
else
print-support::
	@printf "coqc is 8.3 or 8.4:\t\t\t\tYes\n"
endif

$(DEFAULT_LOGS) $(CONDITIONAL_LOGS) : example_%_result.log : $$(wildcard example_%/example_%.v) run-example-%.sh
	$(VECHO) "TEST run-example-$*.sh..." >&2
	$(Q)yes "y" 2>/dev/null | ./run-example-$*.sh >"example_$*_make.log" 2>&1; RV=$$?; (echo "$$RV" > "$@")
	$(Q)RV="$$(cat "$@")"; if [ "$$RV" -eq 0 ]; then RESULT="$(GREEN)success!$(NC)"; else RESULT="$(RED)failure$(NC)"; fi; \
	echo "TEST run-example-$*.sh... $$RESULT" >&2

test-suite-verbose-report::
	$(Q)$(MAKE) test-suite-report -k
	$(Q)ALL="$(sort $(wildcard $(ENABLED_LOGS)))"; \
	for i in $$ALL; do                             \
	        if [ "$$(cat $$i)" -ne 0 ]; then       \
	                echo "$(RED)$$i$(NC):";        \
	        else                                   \
	                echo "$(GREEN)$$i$(NC):";      \
	        fi;                                    \
	        cat "$${i%%_result.log}_make.log";     \
	done

test-suite-verbose-report test-suite-report::
	$(Q)ALL="$(sort $(ENABLED_LOGS))";                               \
	DISABLED="$(sort $(DISABLED_LOGS))";                             \
	SUCCESS=;                                                        \
	FAILURE=;                                                        \
	UNKNOWN=;                                                        \
	for i in $$ALL; do                                               \
	        if [ -f "$$i" ]; then                                    \
	                if [ "$$(cat $$i)" -ne 0 ]; then                 \
	                        FAILURE="$$FAILURE $$i";                 \
	                else                                             \
	                        SUCCESS="$$SUCCESS $$i";                 \
	                fi;                                              \
	        else                                                     \
	                UNKNOWN="$$UNKNOWN $$i";                         \
	        fi;                                                      \
	done;                                                            \
	if [ ! -z "$$FAILURE" ]; then                                    \
	        echo "$(BOLD)Failing test logs:$(NORMAL)";               \
	        for i in $$FAILURE; do                                   \
	                echo "$(RED)$$i$(NC):";                          \
	                cat "$${i%%_result.log}_make.log";               \
	        done;                                                    \
	fi;                                                              \
	if [ ! -z "$$SUCCESS" ]; then                                    \
	        echo "$(BOLD)Passing tests:$(NORMAL)";                   \
	        for i in $$SUCCESS; do                                   \
	                echo "$(GREEN)$$i$(NC)";                         \
	        done;                                                    \
	fi;                                                              \
	if [ ! -z "$$UNKNOWN" ]; then                                    \
	        echo "$(BOLD)Unknown tests:$(NORMAL)";                   \
	        for i in $$UNKNOWN; do                                   \
	                echo "$(YELLOW)$$i$(NC)";                        \
	        done;                                                    \
	fi;                                                              \
	if [ ! -z "$$DISABLED" ]; then                                   \
	        echo "$(BOLD)Disabled tests:$(NORMAL)";                  \
	        for i in $$DISABLED; do                                  \
	                echo "$(YELLOW)$$i$(NC)";                        \
	        done;                                                    \
	fi;                                                              \
	if [ ! -z "$$FAILURE" ]; then                                    \
	        echo "$(RED)$(BOLD)Failing tests:$(NORMAL)$(NC)";        \
	        for i in $$FAILURE; do                                   \
	                echo "$(RED)$$i$(NC)";                           \
	        done;                                                    \
		exit $(ERROR_ON_FAILURE);                                \
	elif [ -z "$$UNKNOWN" ]; then                                    \
	        echo "$(GREEN)$(BOLD)All tests succeeded$(NORMAL)$(NC)"; \
	fi





MISSING_FILES = $(filter-out $(MAIN_RUNS) $(OTHER_RUNS) $(IGNORE), $(wildcard *.sh *.py))
.PHONY: has-all-tests
ifneq (,$(MISSING_FILES))
has-all-tests::
	@echo "$(RED)Missing files: $(MISSING_FILES)$(NC)"
	@exit 1
else
has-all-tests::

endif

clean::
	rm -f */bug*.v */*.vo */*.v.d */*.glob $(DEFAULT_LOGS) $(CONDITIONAL_LOGS) $(BROKEN_LOGS)
