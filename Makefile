OS=$(shell uname -s | tr '[:upper:]' '[:lower:]')
prefix ?= $(pwd)/build
TEST_LOGS_DIR ?= ./logs/tests/
INSTALLDIR ?= $(prefix)/athena
version=$(shell cat ./version.txt)
ATHENA_POSTFIX=$(OS)-$(version)


.PHONY: test
test: smlnj
	mkdir -p $(TEST_LOGS_DIR)
	ATHENA_HOME=${ATHENA_HOME} TEST_LOGS_DIR=$(TEST_LOGS_DIR) python3 ./tests/regression/regressionTest.py 2> $(TEST_LOGS_DIR)/test_error.txt 1> $(TEST_LOGS_DIR)/test_out.txt

.PHONY: smlnj
smlnj:
	sml scripts/make_smlnj_binary.sml


.PHONY: build
build:
	mkdir -p $(INSTALLDIR)
	touch $(INSTALLDIR)/error_logs.txt
	ATHENA_POSTFIX=$(ATHENA_POSTFIX) INSTALLDIR=$(INSTALLDIR) ./scripts/make_mlton_binary  2> $(INSTALLDIR)/error_logs.txt

.PHONY: dist
dist:

.PHONY: clean
clean:
	rm -rf $(INSTALLDIR)
	rm -rf $(TEST_LOGS_DIR)

