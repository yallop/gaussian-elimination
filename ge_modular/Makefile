# OPAM switch: 4.04.0+BER

TIMPL=floatImpl.cmo integerImpl.cmo rationalImpl.cmo

all: check-compiler domains.cmo staged.cmo $(TIMPL)

check-compiler:
	@test $$(opam switch  show) = "4.03.0+effects-ber" \
	|| (echo 1>&2 "Please use OPAM switch 4.03.0+effects-ber"; exit 1)

staged.cmo: staged.ml
	metaocamlc -g -c -short-paths \
           staged.ml

floatImpl.cmo: staged.cmo
	metaocamlc -g -c -short-paths \
           floatImpl.mli floatImpl.ml

integerImpl.cmo: staged.cmo
	metaocamlc -g -c -short-paths \
           integerImpl.mli integerImpl.ml

rationalImpl.cmo: staged.cmo
	metaocamlc -g -c -short-paths \
           rationalImpl.mli rationalImpl.ml

domains.cmo: $(wildcard *.ml *.mli)
	metaocamlc -g -c -short-paths \
           gausselim_types.ml \
           domains.mli domains.ml

clean:
	rm -f mytop *.cmi *.cmo test.out

.PHONY: all clean check-compiler test
