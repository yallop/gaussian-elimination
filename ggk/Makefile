.PHONY: all clean codetest

INC = -I src/

CMO = src/staged.cmo src/repr.cmo \
      src/sign.cmo src/simplify.cmo \
      src/sstring.cmo src/logic.cmo \
      src/algebra.cmo src/float.cmo src/rational.cmo src/integer.cmo  \
      src/tuple.cmo src/foldable.cmo src/matrix.cmo \
      src/vector.cmo src/vectoren.cmo src/point.cmo src/pointen.cmo \
      src/affine.cmo \
      src/hplane.cmo src/sphere.cmo \
      src/simplex.cmo \
      src/instances.cmo

ML = $(CMO:.cmo=.ml)

# unittest:
#	cd utest && make && cd .. && touch utest.out

all: $(ML) ggk.top ohunit codetest

ohunit:
	cd ounit && make all && cd .. 

codetest: ggk.top
	cd ctest && make && cd .. && touch ctest.out

ggk.top: $(ML)
	cd src && make all && cd ..
	metaocamlmktop -o ggk.top nums.cma $(CMO)

clean:
	rm -f src/*.cm[iox] src/*~ *.out ggk.top #src/*.mli removed from rm command
	cd ctest && make clean && cd ..
	cd ounit && make clean && cd ..
