# Options passed on the command line
ERROR_ON_FAILURE=1
V = 0
CAT_ALL_LOGS=0
####

DEFAULT_TESTS = 000 001 002 003 004 005 007 008 008-2 008-3 009 011 012 014 015 016 017 019 021 022 023 024 025 028 029 030 031 035 036 037 038 039 040 041 042 043 045 047 050 051 060 062
CONDITIONAL_TESTS = 006 018

ONLY_IF_COQTOP_COMPILE_TESTS =
ONLY_IF_Q_TESTS = 010 026
ONLY_IF_TOP_TESTS = 063
ONLY_IF_W_TESTS = 044
ONLY_IF_W_AND_GE_815_TESTS = 046
ONLY_IF_W_AND_UNSET_TESTS = 057 058
ONLY_IF_FROM_TESTS = 013 027 032 033 034
ONLY_IF_FROM_AND_IMPORT_CATEGORIES_TESTS = 061
ONLY_IF_FROM_AND_VOS_TESTS = 059
ONLY_IF_GLOB_IMPORT_TESTS = 052 053 054
ONLY_IF_GT_84_TESTS = 020 049
ONLY_IF_GE_812_TESTS = 048
ONLY_IF_SYS_V_FILES_TESTS = 055
ONLY_IF_SYS_GLOB_FILES_GOOD_TESTS =
ONLY_IF_SYS_GLOB_FILES_GOOD_AND_CAN_INLINE_COQ_INIT_LOGIC_TESTS = 056
CONDITIONAL_TESTS += \
	$(ONLY_IF_Q_TESTS) \
	$(ONLY_IF_TOP_TESTS) \
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
	#

MAIN_RUNS = $(patsubst %,run-example-%.sh,$(DEFAULT_TESTS) $(CONDITIONAL_TESTS) $(BROKEN_TESTS))
OTHER_RUNS = run-example-008.py
IGNORE = prefix-grep.py disable-parallel-make.sh init-settings.sh memoize.py

DEFAULT_LOGS = $(patsubst %,example_%_result.log,$(DEFAULT_TESTS))
CONDITIONAL_LOGS = $(patsubst %,example_%_result.log,$(CONDITIONAL_TESTS))
BROKEN_LOGS = $(patsubst %,example_%_result.log,$(BROKEN_TESTS))
ALL_LOGS = $(DEFAULT_LOGS) $(CONDITIONAL_LOGS) $(BROKEN_LOGS)
ONLY_IF_COQTOP_COMPILE_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_COQTOP_COMPILE_TESTS))
ONLY_IF_Q_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_Q_TESTS))
ONLY_IF_TOP_LOGS = $(patsubst %,example_%_result.log,$(ONLY_IF_TOP_TESTS))
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

COQC_VERSION:=$(subst version ,,$(shell $(COQBIN)coqc --version 2>&1 | grep -o 'version [^ ]*'))
COQC_SUPPORTS_Q:=$(shell $(COQBIN)coqc --help 2>&1 | grep -c -- -Q)
COQC_SUPPORTS_TOP:=$(shell $(COQBIN)coqc --help 2>&1 | grep -c -- '-top ')
COQTOP_SUPPORTS_COMPILE:=$(shell $(COQBIN)coqtop --help 2>&1 | tr '\n' '~' | sed s'/Deprecated options.*//g' | tr '~' '\n' | grep -c -- '\s-compile\s')
COQC_SUPPORTS_FROM:=$(shell echo "From Coq.Init Require Import Notations." | $(COQBIN)coqtop 2>&1 | grep -q 'Error'; echo $$?)
COQC_SUPPORTS_IMPORT_CATEGORIES:=$(shell echo "Require Import (hints) Coq.Init.Notations." | $(COQBIN)coqtop 2>&1 | grep -q 'Error\|Syntax error'; echo $$?)
COQC_SUPPORTS_W:=$(shell $(COQBIN)coqtop --help 2>&1 | grep -c -- '-w ')
COQC_SUPPORTS_VOS:=$(shell $(COQBIN)coqc --help 2>&1 | grep -c -- '-vos ')
COQC_SUPPORTS_UNSET:=$(shell $(COQBIN)coqtop --help 2>&1 | grep -c -- '-unset ')
COQC_COQLIB:=$(shell $(COQBIN)coqc -config 2>&1 | grep -o 'COQLIB=.*' | sed s'/^COQLIB=//g')
COQLIB_V_FILES:=$(wildcard $(COQC_COQLIB)/theories/Init/*.v)
COQLIB_GLOB_FILES:=$(wildcard $(COQC_COQLIB)/theories/Init/*.glob)
COQLIB_PRELUDE_V_FILE:=$(wildcard $(COQC_COQLIB)/theories/Init/Prelude.v)
COQLIB_PRELUDE_GLOB_FILE:=$(wildcard $(COQC_COQLIB)/theories/Init/Prelude.glob)

.PHONY: check
check::
	@echo -n "Running with PYTHON=$(GREEN)"
	@bash -c '. init-settings.sh; echo -n "$${PYTHON}"'
	@echo -n "$(NC) ($(GREEN)"
	@bash -c '. init-settings.sh; echo -n "$$(which "$${PYTHON}")"'
	@echo "$(NC)) (based on $(GREEN)$${PYTHON}$(NC))"
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

ifneq (0,$(strip $(COQC_SUPPORTS_TOP)))
test-suite: $(ONLY_IF_TOP_LOGS)
ENABLED_LOGS += $(ONLY_IF_TOP_LOGS)
print-support::
	@printf "coqc supports -top:\t\t\t\tYes\n"
else
print-support::
	@printf "coqc supports -top:\t\t\t\tNo\n"
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


COQLIB_PRELUDE_GLOB_FILE_NEWER:=$(shell . init-settings.sh; $${PYTHON} -c 'import sys, os; m1, m2 = os.stat(os.sys.argv[1]).st_mtime, os.stat(os.sys.argv[2]).st_mtime; print(m1 < m2 or "%s <= %s" % (m2, m1))' "$(COQLIB_PRELUDE_V_FILE)" "$(COQLIB_PRELUDE_GLOB_FILE)" 2>&1)
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
