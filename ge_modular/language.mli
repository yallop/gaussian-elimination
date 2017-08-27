(* Define a number of types which amount to
   **Virtualizing the language**
   that we will use.  \cite{Scala Virtualized}

  Try to organize these into logical groupings.
*)
type 'a abstract

module type Control = sig
  val ret : 'a abstract -> unit -> 'b abstract
end

module type Ref = sig
  val ref : 'a abstract -> 'a ref abstract
  val get : 'a ref abstract -> 'a abstract
end
