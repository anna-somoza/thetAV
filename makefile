# This Makefile is for convenience as a reminder and shortcut for the most used commands

# Package folder
PACKAGE = thetAV

# change to your sage command if needed
SAGE = sage

all: install test

install:
	$(SAGE) -pip install --upgrade --no-index -v .

uninstall:
	$(SAGE) -pip uninstall $(PACKAGE)

dev:
	$(SAGE) -pip install --upgrade -e .

test:
	$(SAGE) -t $(PACKAGE)/.

coverage:
	$(SAGE) -coverage $(PACKAGE)/*

doc:
	cd docs && $(SAGE) -sh -c "make html"

doc-pdf:
	cd docs && $(SAGE) -sh -c "make latexpdf" && $(SAGE) -sh -c "make latexpdf"

clean: uninstall
	clean-doc

clean-doc:
	cd docs && $(SAGE) -sh -c "make clean"

.PHONY: all install develop test coverage clean clean-doc doc doc-pdf
