ifeq "$(COQBIN)" ""
  COQBIN=$(dir $(shell which coqtop))/
endif

all: $(patsubst %.v,%.v.log,$(wildcard *.v))

%.v.log: %.v
	$(COQBIN)coqtop -batch -I ../src -Q ../theories Effects -lv $< > $@
	if [ $$? = 0 ]; then \
		echo "    $<... OK"; \
	else \
		echo "    $<... FAIL!"; \
	fi; \

clean:
	rm -f *.log
