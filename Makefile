has-all-tests check::
	$(MAKE) -C examples $@

.PHONY: has-all-tests check

PYTHON3?=python3

DOCTEST_FILES := \
	import_util.py \
	#

.PHONY: doctests
doctests::
	$(PYTHON3) $(DOCTEST_FILES)
