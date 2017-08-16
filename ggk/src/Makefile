.PHONY: all depend

CC = metaocamlc
INC = -I .

CMO = staged.cmo \
      simplify.cmo \
      repr.cmo sstring.cmo \
      sign.cmo \
      logic.cmo \
      algebra.cmo \
      float.cmo rational.cmo integer.cmo  \
      tuple.cmo foldable.cmo matrix.cmo \
      vector.cmo vectoren.cmo point.cmo pointen.cmo \
      affine.cmo \
      hplane.cmo sphere.cmo \
      simplex.cmo \
      instances.cmo

ML = $(CMO:.cmo=.ml)
MLI = staged.mli

all: $(CMO) $(CMI)

.depend: $(ML) $(MLI)
	ocamldep *.ml > .depend

depend: .depend

# %.mli : %.ml
#	$(CC) $(INC) -i $< > $@

%.cmi: %.mli
	$(CC) $(INC) -c $<

%.cmo: %.ml
	$(CC) $(INC) -c $(LIB) $<

clean: 
	rm -f *.cm?
include .depend
