
signature SORT =
   sig
      val sort : ('a * 'a -> order) -> 'a list -> 'a list
   end