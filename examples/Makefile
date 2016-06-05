# Options passed on the command line
ERROR_ON_FAILURE=1
V = 0
CAT_ALL_LOGS=0

####

DEFAULT_TESTS = 00 01 02 03 04 05 07 08 08-2 08-3 09 11 12 14 15 16 17
CONDITIONAL_TESTS = 06 10 13 18

MAIN_RUNS = $(patsubst %,run-example-%.sh,$(DEFAULT_TESTS) $(CONDITIONAL_TESTS) $(BROKEN_TESTS))
OTHER_RUNS = run-example-08.py
IGNORE = prefix-grep.py

DEFAULT_LOGS = $(patsubst %,example_%_result.log,$(DEFAULT_TESTS))
CONDITIONAL_LOGS = $(patsubst %,example_%_result.log,$(CONDITIONAL_TESTS))

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
BOLD=$(shell tput bold)
NORMAL=$(shell tput sgr0)

COQC_SUPPORTS_Q=$(shell coqc --help 2>&1 | grep -c -- -Q)
COQC_SUPPORTS_FROM=$(shell echo "From Coq.Init Require Import Notations." | coqtop 2>&1 | grep -c 'Error')

check::
	$(MAKE) -B test-suite

ifeq (1,$(CAT_ALL_LOGS))
check::
	$(MAKE) test-suite-verbose-report
else
check::
	$(MAKE) test-suite-report
endif

test-suite: $(DEFAULT_LOGS)

ifneq (0,$(strip $(COQC_SUPPORTS_Q)))
test-suite: example_10_result.log
endif

ifeq (0,$(strip $(COQC_SUPPORTS_FROM)))
test-suite: example_13_result.log
endif

$(DEFAULT_LOGS) $(CONDITIONAL_LOGS) : example_%_result.log : $(wildcard example_%/*.v run-example-%.sh) Makefile
	$(VECHO) "TEST run-example-$*.sh..." >&2
	$(Q)yes "y" | ./run-example-$*.sh >"example_$*_make.log" 2>&1; RV=$$?; (echo "$$RV" > "$@")
	$(Q)RV="$$(cat "$@")"; if [ "$$RV" -eq 0 ]; then RESULT="$(GREEN)success!$(NC)"; else RESULT="$(RED)failure$(NC)"; fi; \
	$(VIECHO) "TEST run-example-$*.sh... $$RESULT" >&2

test-suite-verbose-report::
	$(Q)$(MAKE) test-suite-report
	$(Q)for i in $(wildcard example_*_result.log); do                       \
	        if [ "$$(cat $$i)" -ne 0 ]; then                                \
	                echo "$(RED)$$i$(NC):";                                 \
	        else                                                            \
	                echo "$(GREEN)$$i$(NC):";                               \
	        fi;                                                             \
	        cat "$${i%%_result.log}_make.log";                              \
	done

test-suite-verbose-report test-suite-report::
	$(Q)ALL="$(wildcard example_*_result.log)";                             \
	SUCCESS=;                                                               \
	FAILURE=;                                                               \
	for i in $$ALL; do                                                      \
	        if [ "$$(cat $$i)" -ne 0 ]; then                                \
	                FAILURE="$$FAILURE $$i";                                \
	        else                                                            \
	                SUCCESS="$$SUCCESS $$i";                                \
	        fi;                                                             \
	done;                                                                   \
	if [ ! -z "$$FAILURE" ]; then                                           \
	        echo "$(BOLD)Failing test logs:$(NORMAL)";                      \
	        for i in $$FAILURE; do                                          \
	                echo "$(RED)$$i$(NC):";                                 \
	                cat "$${i%%_result.log}_make.log";                      \
	        done;                                                           \
	fi;                                                                     \
	if [ ! -z "$$SUCCESS" ]; then                                           \
	        echo "$(BOLD)Passing tests:$(NORMAL)";                          \
	        for i in $$SUCCESS; do                                          \
	                echo "$(GREEN)$$i$(NC)";                                \
	        done;                                                           \
	fi;                                                                     \
	if [ ! -z "$$FAILURE" ]; then                                           \
	        echo "$(RED)$(BOLD)Failing tests:$(NORMAL)$(NC)";               \
	        for i in $$FAILURE; do                                          \
	                echo "$(RED)$$i$(NC)";                                  \
	        done;                                                           \
		exit $(ERROR_ON_FAILURE);                                       \
	else                                                                    \
	        echo "$(GREEN)$(BOLD)All tests succeeded$(NORMAL)$(NC)";        \
	fi





MISSING_FILES = $(filter-out $(MAIN_RUNS) $(OTHER_RUNS) $(IGNORE), $(wildcard *.sh *.py))
ifneq (,$(MISSING_FILES))
has-all-tests::
	@echo "$(RED)Missing files: $(MISSING_FILES)$(NC)"
	@exit 1
else
has-all-tests::

endif

clean::
	rm -f */bug*.v */*.vo */*.v.d */*.glob $(DEFAULT_LOGS) $(CONDITIONAL_LOGS)
