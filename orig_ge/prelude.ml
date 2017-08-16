(* Common operations used throughout the code *)
(* $Id$ *)

(* Direction, for loops *)
type dir = UP | DOWN

type ('a, 'b) either = Left of 'a | Right of 'b

(* Matrix layed out row after row, in a C fashion, using a record
   as intermediary *)
type 'a container2dfromvector = {arr:('a array); n:int; m:int}

(* Matrix layed out column after column, in a Fortran fashion, using an
   algebraic type as intermediary *)
type 'a container2dfromFvector = FortranVector of ('a array * int * int)

(* This type is needed for the output, and is tracked during pivoting. 
   It's hard to find the right place for this lifting. If this
   is moved to domans_*.ml modules, this code should be placed
   into CONTAINER2D.
*)
type perm = RowSwap of (int * int) | ColSwap of (int*int)
