signature KEY =
sig
    type t
    val compare : t * t -> order
end

signature DICT = 
sig
    type key
    type 'a entry = key * 'a
    type 'a dict

    val empty: 'a dict
    val lookup: key * 'a dict -> 'a option
    val insert: 'a entry * 'a dict -> 'a dict
end

structure IntKey :> KEY where type t=int  =
struct
    type t = int
    val compare = Int.compare
end

structure StringKey : KEY =
struct
    type t = string
    val compare = String.compare
end

functor Dict (Key : KEY) :> DICT where type key=Key.t =
struct
    structure K = Key;

    type key = K.t;
    type 'a entry = key * 'a;
    type 'a dict = key -> 'a option;

    fun empty (k : key) = NONE;

    fun lookup (k: key, f: key -> 'a option): 'a option = f k;

    fun insert ((k, v): 'a entry, f: key -> 'a option): key -> 'a option =
      (fn k' => case K.compare (k, k')
    		 of EQUAL => SOME v
		  | _ => f k');

end

structure IntDict = Dict (IntKey) 
val id1 = IntDict.insert ((42,"answer"), IntDict.empty)
val SOME a = IntDict.lookup (42, id1)
;
