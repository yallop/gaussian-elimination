module type LOGIC = sig
  include Repr.REP
  val not_ : ('a,bool,bool) unary_fun
  val and_ : ('a,bool) rel
  val or_  : ('a,bool) rel
  val true_ : ('a,bool) rep
  val false_ : ('a,bool) rep
end

module LogicN = struct
  let false_ = false
  let true_ = true
  let or_ = ( || )
  let and_ = ( && )
  let not_ = ( not )
end

module LogicC = struct
  let false_ = .<false>.
  let true_ = .<true>.
  let or_ = fun x y -> .< .~x || .~y >.
  let and_ = fun x y -> .< .~x && .~y >.
  let not_ = fun x -> .< not .~x >.
end

module LogicStaged = struct
  let false_ = Staged.lift_const false
  let true_ = Staged.lift_const true
  let or_ x y = Simplify.semiring true false LogicN.or_ LogicC.or_ x y
  let and_ x y = Simplify.semiring false true LogicN.and_ LogicC.and_ x y
  let not_ x = Staged.unary LogicN.not_ LogicC.not_ x
end

