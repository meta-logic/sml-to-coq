(* Generates the heap image for sml-to-coq
for standalone execution *)

structure Main =
struct
    open Generator

    fun main (prog_name, args) = 
        let
        val _ = print("Converting " ^ List.nth (args,1)  ^ " to " ^ List.nth (args, 2))
        val _ = Generator.generate(List.nth (args,1), List.nth (args,2))
        in
            0
        end
end
