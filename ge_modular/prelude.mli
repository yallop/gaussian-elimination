val maybe : ('a -> 'b) -> 'b -> 'a option -> 'b
val maybe_apply2 : ('a -> 'b -> 'c -> 'd -> 'e) -> 'a option -> 'b option -> ('c -> 'd -> 'e) option
