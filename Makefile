FIND_BUG?=
ifneq (,$(strip $(FIND_BUG)))
FULL_FIND_BUG:=$(abspath $(shell which '$(FIND_BUG)'))
else
FULL_FIND_BUG=$(FIND_BUG)
endif
MINIMIZE_REQUIRES?=
ifneq (,$(strip $(MINIMIZE_REQUIRES)))
FULL_MINIMIZE_REQUIRES:=$(abspath $(shell which '$(MINIMIZE_REQUIRES)'))
else
FULL_MINIMIZE_REQUIRES=$(MINIMIZE_REQUIRES)
endif
INLINE_IMPORTS?=
ifneq (,$(strip $(INLINE_IMPORTS)))
FULL_INLINE_IMPORTS:=$(abspath $(shell which '$(INLINE_IMPORTS)'))
else
FULL_INLINE_IMPORTS=$(INLINE_IMPORTS)
endif

has-all-tests check print-support::
	$(MAKE) -C examples $@ FIND_BUG='$(FULL_FIND_BUG)' MINIMIZE_REQUIRES='$(FULL_MINIMIZE_REQUIRES)' INLINE_IMPORTS='$(FULL_INLINE_IMPORTS)'


.PHONY: has-all-tests check print-support

PYTHON3?=python3
PYTHON?=python

.PHONY: dist
dist:
	$(PYTHON) -m build

DOCTEST_MODULES := \
	import_util \
	#

.PHONY: doctests

define add_target
# $(1) main target
# $(2) intermediate target
# $(3) recipe
$(1): $(1)-$(2)

.PHONY: $(1)-$(2)
$(1)-$(2):
	$(3)
endef

$(foreach m,$(DOCTEST_MODULES),$(eval $(call add_target,doctests,$(m),$(PYTHON3) -m coq_tools.$(m))))

MAIN_FILES_SH = git grep --name-only 'def main' 'coq_tools/*.py'
MAIN_MODULES = $(sort $(patsubst coq_tools/%.py,%,$(shell $(MAIN_FILES_SH))))

.PHONY: update-__init__
update-__init__:
	printf "%s\n" '__all__ = [' > coq_tools/__init__.py
	printf "    '%s',\n" $(MAIN_MODULES) >> coq_tools/__init__.py
	printf "%s\n" "  ]" >> coq_tools/__init__.py

PYINSTALLER_ADD_DATA := \
	--add-data coq_tools/coqtop-as-coqc.sh:coq_tools/ \
	--add-data coq_tools/coqtop.bat:coq_tools/ \
	#

.PHONY: standalone-coq-bug-minimizer
standalone-coq-bug-minimizer:
	pyinstaller find-bug.py -n coq-bug-minimizer $(PYINSTALLER_ADD_DATA)

.PHONY: standalone-coq-require-minimizer
standalone-coq-require-minimizer:
	pyinstaller minimize-requires.py -n coq-require-minimizer $(PYINSTALLER_ADD_DATA)

.PHONY: standalone-coq-import-inliner
standalone-coq-import-inliner:
	pyinstaller inline-imports.py -n coq-import-inliner $(PYINSTALLER_ADD_DATA)

.PHONY: standalone
standalone: standalone-coq-bug-minimizer standalone-coq-require-minimizer standalone-coq-import-inliner
