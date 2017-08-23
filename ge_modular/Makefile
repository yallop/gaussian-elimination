# OPAM switch: 4.04.0+BER

all: check-compiler domains.cmo

check-compiler:
	@test $$(opam switch  show) = "4.03.0+effects-ber" \
	|| (echo 1>&2 "Please use OPAM switch 4.03.0+effects-ber"; exit 1)

domains.cmo: $(wildcard *.ml *.mli)
	metaocamlc -g -c -short-paths \
           gausselim_types.ml \
           domains.mli domains.ml

clean:
	rm -f mytop *.cmi *.cmo test.out

.PHONY: all clean check-compiler test
