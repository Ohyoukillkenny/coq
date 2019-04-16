VOFILES := Basic.vo Induction.vo

.PHONY: all clean

all: $(VOFILES)

clean:
	rm -f *.vo *.glob

%.vo: %.v
	coqc $*
