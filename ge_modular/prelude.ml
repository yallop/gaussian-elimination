let maybe f c = function
  | Some x -> f x
  | None   -> c
