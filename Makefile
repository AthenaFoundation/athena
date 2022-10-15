OS=$(shell uname -s | tr '[:upper:]' '[:lower:]')
prefix ?= $(shell pwd)/build
ATHENA_POSTFIX=$(OS)-$(version)
TEST_LOGS_DIR ?= ./logs/tests/
INSTALLDIR ?= $(prefix)/athena-$(ATHENA_POSTFIX)
version=$(shell cat ./version.txt)

ATHENA_HOME ?= $(shell pwd)

.PHONY: install_external_tools
install_external_tools: 
	$(shell ./scripts/install_external_tools.sh)

.PHONY: test
test: smlnj
	mkdir -p $(TEST_LOGS_DIR)
	ATHENA_HOME=${ATHENA_HOME} TEST_LOGS_DIR=$(TEST_LOGS_DIR) python3 ./tests/regression/regressionTest.py 2> $(TEST_LOGS_DIR)test_error.txt 1> $(TEST_LOGS_DIR)test_out.txt

.PHONY: smlnj
smlnj:
	sml scripts/make_smlnj_binary.sml


.PHONY: build
build:
	mkdir -p $(INSTALLDIR)
	cp -r ./lib $(INSTALLDIR)
	cp -r ./util $(INSTALLDIR)
	touch $(INSTALLDIR)/build_logs.txt
	ATHENA_POSTFIX=$(ATHENA_POSTFIX) INSTALLDIR=$(INSTALLDIR) ./scripts/make_mlton_binary

.PHONY: packages
packages: build
	mkdir ./packages
	cd $(prefix) && tar czvf athena-$(ATHENA_POSTFIX).tgz ./athena-$(ATHENA_POSTFIX)
	cd $(prefix) && zip -r athena-$(ATHENA_POSTFIX).zip ./athena-$(ATHENA_POSTFIX)/*
	mv $(prefix)/*.tgz ./packages
	mv $(prefix)/*.zip ./packages

.PHONY: clean
clean:
	rm -rf $(INSTALLDIR)/lib
	rm -rf $(INSTALLDIR)/tmp
	rm -rf $(INSTALLDIR)/build_logs.txt
	rm -rf $(INSTALLDIR)/athena
	rm -rf $(TEST_LOGS_DIR)
	rm -rf ./*.tgz
	rm -rf ./*.zip
	rm -rf ./packages
