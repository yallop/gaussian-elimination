let maybe f c = function
  | Some x -> f x
  | None   -> c

let maybe_apply2 f a b = match (a,b) with
  | Some aa , Some bb -> Some (fun x y -> f aa bb x y)
  | _ , _ -> None
