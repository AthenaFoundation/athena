OS=$(shell uname -s | tr '[:upper:]' '[:lower:]')
prefix ?= ./build
INSTALLDIR ?= $(prefix)/athena
version=$(shell cat ./version.txt)
ATHENA_POSTFIX=$(OS)-$(version)

.PHONY: test
test:
	python3 ./tests/regression/regressionTest.py


.PHONY: build
build:
	mkdir -p $(INSTALLDIR)
	touch $(INSTALLDIR)/error_logs.txt
	ATHENA_POSTFIX=$(ATHENA_POSTFIX) INSTALLDIR=$(INSTALLDIR) ./make_mlton_binary  2> $(INSTALLDIR)/error_logs.txt

.PHONY: dist
dist:

.PHONY: clean
clean:
	rm -rf $(INSTALLDIR)

