
(* Terminating, not structurally decreasing *)
(* Hard argument... *)
fun permutations l = case l 
  of [] => []
  | [x] => [x]
  | _ => List.foldl (fn (acc, x) => let
      val l_no_x = List.filter (fn e => e <> x) l
      val ps = permutations l_no_x
    in
      acc @ List.map (fn p => x :: p) ps
    end
    ) [] l
