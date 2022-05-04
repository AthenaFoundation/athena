OS=$(shell uname -s | tr '[:upper:]' '[:lower:]')
prefix ?= .
INSTALLDIR ?= $(prefix)
version=$(shell cat ./version.txt)
ATHENA_POSTFIX=$(OS)-$(version)

.PHONY: test
test:
	python3 ./tests/regression/regressionTest.py


.PHONY: build
build:
	mkdir -p $(INSTALLDIR)
	ATHENA_POSTFIX=$(ATHENA_POSTFIX) INSTALLDIR=$(INSTALLDIR) ./make_mlton_binary >> athena-$(OS)

.PHONE: dist
dist:
