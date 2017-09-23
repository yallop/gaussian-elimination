# OPAM switch: 4.04.0+BER

UTIL=prelude.cmo codePrelude.cmo
INFRA=domains.cmo staged.cmo simplify.cmo
TIMPL=floatImpl.cmo integerImpl.cmo rationalImpl.cmo zpImpl.cmo
CIMPL=genericArray.cmo

all: check-compiler $(UTIL) $(INFRA) $(TIMPL) $(CIMPL)

check-compiler:
	@test $$(opam switch  show) = "4.03.0+effects-ber" \
	|| (echo 1>&2 "Please use OPAM switch 4.03.0+effects-ber"; exit 1)

staged.cmo: staged.ml
	metaocamlc -g -c -short-paths \
           staged.ml

simplify.cmo: simplify.ml staged.cmo
	metaocamlc -g -c -short-paths \
           simplify.ml

prelude.cmo: prelude.ml prelude.mli
	metaocamlc -g -c -short-paths \
	  prelude.mli prelude.ml

codePrelude.cmo: codePrelude.ml codePrelude.mli
	metaocamlc -g -c -short-paths \
	  codePrelude.mli codePrelude.ml

floatImpl.cmo: prelude.cmo codePrelude.cmo staged.cmo domains.cmo simplify.cmo floatImpl.mli floatImpl.ml
	metaocamlc -g -c -short-paths \
	  floatImpl.mli floatImpl.ml

integerImpl.cmo: prelude.cmo staged.cmo domains.cmo integerImpl.mli integerImpl.ml
	metaocamlc -g -c -short-paths \
           integerImpl.mli integerImpl.ml

rationalImpl.cmo: prelude.cmo staged.cmo domains.cmo rationalImpl.mli rationalImpl.ml
	metaocamlc -g -c -short-paths \
           rationalImpl.mli rationalImpl.ml

zpImpl.cmo: prelude.cmo staged.cmo domains.cmo zpImpl.mli zpImpl.ml
	metaocamlc -g -c -short-paths \
           zpImpl.mli zpImpl.ml

container.cmi: container.mli
	metaocamlc -g -c -short-paths \
           container.mli

genericArray.cmo: domains.cmo genericArray.ml container.cmi
	metaocamlc -g -c -short-paths \
           genericArray.ml

domains.cmo: domains.mli domains.ml
	metaocamlc -g -c -short-paths \
           domains.mli domains.ml

clean:
	rm -f mytop *.cmi *.cmo test.out

.PHONY: all clean check-compiler test
