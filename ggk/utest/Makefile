
CC = metaocamlc

SOBJ = staged.cmo basetypes.cmo code.cmo util.cmo \
       algebra.cmo float.cmo \
       tuple.cmo matrix.cmo determinant.cmo \
       vector.cmo vectoren.cmo \
       point.cmo pointen.cmo \
       affine.cmo \
       hplane.cmo sphere.cmo \
       orient.cmo insphere.cmo \
       vertex.cmo simplex.cmo \
       inside.cmo
TEST = staged_test.ml basetypes_test.ml float_test.ml \
       matrix_test.ml determinant_test.ml \
       pointen_test.ml affine_test.ml \
       hplane_test.ml sphere_test.ml \
       orient_test.ml insphere_test.ml \
       inside_test.ml
TOBJ = $(TEST:.ml=.cmo)
LIB = unix.cma ../ounit/oUnit.cma
OUT = test.out
CFLAGS = -I ../src/ -I ../ounit/

%.cmo: %.ml
	$(CC) $(CFLAGS) -c $(LIB) $<

test: $(TOBJ) main.ml
	$(CC) $(CFLAGS) -o $(OUT) $(LIB) $(SOBJ) $?

top: $(TOBJ)
	ocamlmktop $(CFLAGS) $(LIB) $(SOBJ) $?

clean:
	rm -f *.cm[iox] *~ *.o
	rm -f test.out

