type t = Pos | Zero | Neg | PosOrZero | NegOrZero
let eq = (=)
let pos = eq Pos
let zero = eq Zero
let neg = eq Neg
let pos_or_zero = eq PosOrZero
let neg_or_zero = eq NegOrZero
let bind a b c d e = 
  function Pos -> a | Zero -> b | Neg -> c | PosOrZero -> d | NegOrZero -> e
