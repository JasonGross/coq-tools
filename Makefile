has-all-tests check print-support::
	$(MAKE) -C examples $@

.PHONY: has-all-tests check print-support

PYTHON3?=python3
PYTHON?=python

.PHONY: dist
dist:
	$(PYTHON) setup.py sdist bdist_wheel

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
