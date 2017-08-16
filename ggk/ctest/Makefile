# The diff tests (DTST) compare generated code (*_out.ml) to expected generate 
# 	code (*_res.ml).
# The unit tests (UTST) run the generated code and check assertions that
# 	the calculated results match the expected results using ounit.

TOP = ../ggk.top -I ../src/
SED = sed '1,/CUT MARKER/d' 
DTST = d_vector d_point d_affine d_hplane d_inside d_power
UTST = u_vector u_point u_affine u_hplane u_inside u_sphere u_power u_vector_int

LIBOU = unix.cma ../ounit/oUnit.cma #library for ounit
INCOU = -I ../ounit/ #include for ounit

all:	$(DTST) $(UTST)
	@echo "DONE"

clean:
	rm *out*

d_%:
	$(TOP) < $*_test.ml > $*_out_all.ml
	$(SED) $*_out_all.ml > $*_out.ml
	- diff $*_out.ml $*_res.ml
	@echo

u_%:
	- $(TOP) $(INCOU) $(LIBOU) $*_results_test.ml
	@echo


