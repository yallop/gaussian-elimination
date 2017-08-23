# OPAM switch: 4.04.0+BER

all: check-compiler mytop gausselim.cmo

check-compiler:
	@test $$(opam switch  show) = "4.03.0+effects-ber" \
	|| (echo 1>&2 "Please use OPAM switch 4.03.0+effects-ber"; exit 1)

gausselim.cmo: $(wildcard *.ml *.mli)
	metaocamlc -g -c -short-paths \
           gausselim_types.ml \
           gausselim.ml

mytop:
	metaocamlmktop -o mytop -g nums.cma

test: all
	OCAMLRUNPARAM=b ./mytop ./gausselim_types.cmo ./gausselim.cmo < test.ml > test.out
	@(diff test.ml.reference test.out && echo 'test passed') \
         || (echo 'test failed'; exit 1)

clean:
	rm -f mytop *.cmi *.cmo test.out

.PHONY: all clean check-compiler test
