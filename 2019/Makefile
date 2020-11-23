
DAYS := $(dir $(wildcard solutions/day*/Makefile))

build:
	$(foreach dir,$(DAYS),echo "$(dir)" && make -C "$(dir)" &&) true
