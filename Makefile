src = $(wildcard *.v)
obj = $(src:.v=.vo)

all : $(obj)

%.vo: %.v
	coqc $<

.depend depend:
	coqdep *.v > .depend

clean:
	rm -f *.vo *.glob .*.aux .depend

include .depend
