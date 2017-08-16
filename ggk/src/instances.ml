(* used to be Float.Float_Real_Exact, but that's wrong.  Instead use
   Inexact version, with a fixed epsilon
module F = Float.Float_Real_Exact *)

module Eps = struct let eps = 10. ** (-5.) end
module F = Float.Float_Real_Inexact(Eps)

module V1 = Vectoren.NormedVector(Repr.CGen)(F)(Tuple.Tuple1D)
(* Vector 2D with record representation *)
module V2R = Vectoren.NormedVector (Repr.CGen) (F) (Tuple.Record2D)
(* Vector 2D with pair representation *)
module V2P = Vectoren.NormedVector (Repr.CGen) (F) (Tuple.Pair2D)
(* Vector 3D with record representation *)
module V3R = Vectoren.NormedVector (Repr.CGen) (F) (Tuple.Record3D)
(* Vector nD with array representation *)
(* module VnA = Vector (F) (ArrayTuple) *)

module P2R = Pointen.Iso_Axis_Ordered_En_Point (Repr.CGen) (F) (Tuple.Record2D) 
module P3R = Pointen.Iso_Axis_Ordered_En_Point (Repr.CGen) (F) (Tuple.Record3D) 

module P1   = Pointen.En_Point (Repr.CGen) (F) (Tuple.Tuple1D)
module EP2R = Pointen.En_Point (Repr.CGen) (F)(Tuple.Record2D)
module EP3R = Pointen.En_Point (Repr.CGen) (F)(Tuple.Record3D)

module AT2R = Affine.AffineTransformations (EP2R)
module AT3R = Affine.AffineTransformations (EP3R)

(* Line is a 2D codimensional hypleplane *)
module L = Hplane.Line (Repr.CGen) (P2R)

module H0 = Hplane.N_plane (Repr.CGen) (P1)
module H1 = Hplane.N_plane (Repr.CGen) (P2R)
module H2 = Hplane.N_plane (Repr.CGen) (P3R)

module S1 = Sphere.CRSphere(P1) ;;
module S2 = Sphere.CRSphere(EP2R) ;;
module S3 = Sphere.CRSphere(EP3R) ;;

(* instances not based on Float *)
(* exact rationals *)
module Rat = Rational.Field

module V1Rat = Vectoren.Vector(Repr.CGen)(Rat)(Tuple.Tuple1D)
module V3Rat = Vectoren.Vector(Repr.CGen)(Rat)(Tuple.Record3D)

(* integers *)
module I = Integer.Ring
module V1Int = Vectoren.RModule(Repr.CGen)(I)(Tuple.Tuple1D)
module V3Int = Vectoren.RModule(Repr.CGen)(I)(Tuple.Record3D)

(* all of the above are for CGen, let's try others too! *)
(* we can keep the same names too... *)
module Immediate = struct
  module F = Float.FloatNI(Eps)
  module V1 = Vectoren.NormedVector(Repr.Imm)(F)(Tuple.R1DImm)
  (* Vector 2D with record representation *)
  module V2R = Vectoren.NormedVector (Repr.Imm) (F) (Tuple.R2DImm)
  (* Vector 2D with pair representation *)
  module V2P = Vectoren.NormedVector (Repr.Imm) (F) (Tuple.P2DImm)
  (* Vector 3D with record representation *)
  module V3R = Vectoren.NormedVector (Repr.Imm) (F) (Tuple.R3DImm)
  (* Vector nD with array representation *)
  (* module VnA = Vector (F) (ArrayTuple) *)

  module P2R = Pointen.Iso_Axis_Ordered_En_Point (Repr.Imm) (F) (Tuple.R2DImm) 
  module P3R = Pointen.Iso_Axis_Ordered_En_Point (Repr.Imm) (F) (Tuple.R3DImm) 

  module P1   = Pointen.En_Point (Repr.Imm) (F) (Tuple.R1DImm)
  module EP2R = Pointen.En_Point (Repr.Imm) (F)(Tuple.R2DImm)
  module EP3R = Pointen.En_Point (Repr.Imm) (F)(Tuple.R3DImm)

  module AT2R = Affine.AffineTransformations (EP2R)
  module AT3R = Affine.AffineTransformations (EP3R)

  (* Line is a 2D codimensional hypleplane *)
  module L = Hplane.Line (Repr.Imm) (P2R)

  module H0 = Hplane.N_plane (Repr.Imm) (P1)
  module H1 = Hplane.N_plane (Repr.Imm) (P2R)
  module H2 = Hplane.N_plane (Repr.Imm) (P3R)

  module S1 = Sphere.CRSphere(P1) ;;
  module S2 = Sphere.CRSphere(EP2R) ;;
  module S3 = Sphere.CRSphere(EP3R) ;;

  (* instances not based on Float *)
  (* exact rationals *)
  module Rat = Rational.RationalN

  module V1Rat = Vectoren.Vector(Repr.Imm)(Rat)(Tuple.R1DImm)
  module V3Rat = Vectoren.Vector(Repr.Imm)(Rat)(Tuple.R3DImm)

  (* integers *)
  module I = Integer.IntegerN
  module V1Int = Vectoren.RModule(Repr.Imm)(I)(Tuple.R1DImm)
  module V3Int = Vectoren.RModule(Repr.Imm)(I)(Tuple.R3DImm)
end

(* and now for the Code version *)
module Code = struct
  module F = Float.FloatCI(Eps)
  module V1 = Vectoren.NormedVector(Repr.Code)(F)(Tuple.R1DCode)
  (* Vector 2D with record representation *)
  module V2R = Vectoren.NormedVector (Repr.Code) (F) (Tuple.R2DCode)
  (* Vector 2D with pair representation *)
  module V2P = Vectoren.NormedVector (Repr.Code) (F) (Tuple.P2DCode)
  (* Vector 3D with record representation *)
  module V3R = Vectoren.NormedVector (Repr.Code) (F) (Tuple.R3DCode)
  (* Vector nD with array representation *)
  (* module VnA = Vector (F) (ArrayTuple) *)

  module P2R = Pointen.Iso_Axis_Ordered_En_Point (Repr.Code) (F) (Tuple.R2DCode) 
  module P3R = Pointen.Iso_Axis_Ordered_En_Point (Repr.Code) (F) (Tuple.R3DCode) 

  module P1   = Pointen.En_Point (Repr.Code) (F) (Tuple.R1DCode)
  module EP2R = Pointen.En_Point (Repr.Code) (F)(Tuple.R2DCode)
  module EP3R = Pointen.En_Point (Repr.Code) (F)(Tuple.R3DCode)

  module AT2R = Affine.AffineTransformations (EP2R)
  module AT3R = Affine.AffineTransformations (EP3R)

  (* Line is a 2D codimensional hypleplane *)
  module L = Hplane.Line (Repr.Code) (P2R)

  module H0 = Hplane.N_plane (Repr.Code) (P1)
  module H1 = Hplane.N_plane (Repr.Code) (P2R)
  module H2 = Hplane.N_plane (Repr.Code) (P3R)

  module S1 = Sphere.CRSphere(P1) ;;
  module S2 = Sphere.CRSphere(EP2R) ;;
  module S3 = Sphere.CRSphere(EP3R) ;;

  (* instances not based on Float *)
  (* exact rationals *)
  module Rat = Rational.RationalC

  module V1Rat = Vectoren.Vector(Repr.Code)(Rat)(Tuple.R1DCode)
  module V3Rat = Vectoren.Vector(Repr.Code)(Rat)(Tuple.R3DCode)

  (* integers *)
  module I = Integer.IntegerC
  module V1Int = Vectoren.RModule(Repr.Code)(I)(Tuple.R1DCode)
  module V3Int = Vectoren.RModule(Repr.Code)(I)(Tuple.R3DCode)
end
