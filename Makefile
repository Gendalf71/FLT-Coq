COQC ?= coqc
COQFLAGS ?= -Q . ""

# Two-track build (adjust file names if needed)
VFILES := FLT-new.v FLT-old.v
VOFILES := $(VFILES:.v=.vo)

all: $(VOFILES)

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

test:
	@if grep -R -n --include="*.v" "Admitted\." . ; then \
	  echo "ERROR: Admitted found"; exit 1; \
	else \
	  echo "OK: no Admitted"; \
	fi

clean:
	rm -f *.vo *.glob

.PHONY: all clean test
