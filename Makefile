VOFILES := Basic.vo Induction.vo Lists.vo

.PHONY: all clean

all: $(VOFILES)

clean:
	rm -f *.vo *.glob

%.vo: %.v
	coqc $*
