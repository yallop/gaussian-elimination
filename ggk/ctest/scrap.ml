let addi x y =
  mk_binary { bnow = ( + );
	      blater = (fun x y -> lift_comp .<.~(x.c) + .~(y.c)>.) } x y

let ctor x y = x,y

let to_c (x,y) = .< let x = .~(Staged.to_code x)
                    and y = .~(Staged.to_code y) in x, y >.

let add (a,b) (c,d) = ctor (addi a c) (addi b d)

let add2 x =
  let x = x in add x x

let gen () =
  .< fun a b -> .~(
     let x = ctor (of_atom .<a>.) (of_atom .<b>.) in
     let r = add2 x in
     to_c r) >. ;;

gen () ;;

