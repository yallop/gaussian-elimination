
- : unit = ()
# 

 ==== POWER TEST ==== 

- : unit = ()
#   

 ==== PowerFloat power () ==== 

- : unit = ()
#     - : ('a, Float1.R.n -> Float1.R.n) code = .<fun x_1 -> x_1>.
# - : ('a, Float2.R.n -> Float2.R.n) code = .<fun x_2 -> (x_2 *. x_2)>.
# - : ('a, Float8.R.n -> Float8.R.n) code =
.<fun x_3 ->
   (x_3 *. (x_3 *. (x_3 *. (x_3 *. (x_3 *. (x_3 *. (x_3 *. x_3)))))))>.
#   - : ('a, Integer1.R.n -> Integer1.R.n) code = .<fun x_4 -> x_4>.
# - : ('a, Integer2.R.n -> Integer2.R.n) code = .<fun x_5 -> (x_5 * x_5)>.
# - : ('a, Integer8.R.n -> Integer8.R.n) code =
.<fun x_6 -> (x_6 * (x_6 * (x_6 * (x_6 * (x_6 * (x_6 * (x_6 * x_6)))))))>.
#     * *     * * * * * * * * * * * *   
