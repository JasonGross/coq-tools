has-all-tests check print-support::
	$(MAKE) -C examples $@

.PHONY: has-all-tests check print-support

PYTHON3?=python3

DOCTEST_FILES := \
	import_util.py \
	#

.PHONY: doctests
doctests::
	$(PYTHON3) $(DOCTEST_FILES)

PYINSTALLER_ADD_DATA := \
	--add-data coqtop-as-coqc.sh:. \
	--add-data coqtop.bat:. \
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
