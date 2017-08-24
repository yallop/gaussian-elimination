let run0 c = Runcode.run c
let run1 f = Runcode.run .< fun x -> .~(f .<x>.) >.
let run2 f = Runcode.run .< fun x y -> .~(f .<x>. .<y>.) >.
