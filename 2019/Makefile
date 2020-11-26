
DAYS := $(dir $(wildcard solutions/day*/Makefile))
DAYS := $(shell ruby -e "days = ARGV[0].strip.split(' ').map { |d| d.chomp '/' }; puts days.sort_by { |d1| [d1.size, d1] }" "$(DAYS)")

build:
	$(foreach dir,$(DAYS),make -C "$(dir)" &&) true

.PHONY: clean run

run:
	make build
	@echo
	@$(foreach dir,$(DAYS),make -s -C "$(dir)" run && echo &&) true

clean:
	$(foreach dir,$(DAYS),make -C "$(dir)" clean &&) true
