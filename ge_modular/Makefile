# OPAM switch: 4.04.0+BER

UTIL=prelude.cmo
TIMPL=floatImpl.cmo integerImpl.cmo rationalImpl.cmo

all: check-compiler $(UTIL) domains.cmo staged.cmo $(TIMPL)

check-compiler:
	@test $$(opam switch  show) = "4.03.0+effects-ber" \
	|| (echo 1>&2 "Please use OPAM switch 4.03.0+effects-ber"; exit 1)

staged.cmo: staged.ml
	metaocamlc -g -c -short-paths \
           staged.ml

prelude.cmo: prelude.ml
	metaocamlc -g -c -short-paths \
	  prelude.mli prelude.ml

floatImpl.cmo: prelude.cmo staged.cmo floatImpl.mli floatImpl.ml
	metaocamlc -g -c -short-paths \
           floatImpl.mli floatImpl.ml

integerImpl.cmo: prelude.cmo staged.cmo integerImpl.mli integerImpl.ml
	metaocamlc -g -c -short-paths \
           integerImpl.mli integerImpl.ml

rationalImpl.cmo: prelude.cmo staged.cmo rationalImpl.mli rationalImpl.ml
	metaocamlc -g -c -short-paths \
           rationalImpl.mli rationalImpl.ml

domains.cmo: $(wildcard *.ml *.mli)
	metaocamlc -g -c -short-paths \
           gausselim_types.ml \
           prelude.mli prelude.ml \
	   floatImpl.mli floatImpl.ml \
	   integerImpl.mli integerImpl.ml \
	   rationalImpl.mli rationalImpl.ml \
           domains.mli domains.ml

clean:
	rm -f mytop *.cmi *.cmo test.out

.PHONY: all clean check-compiler test
