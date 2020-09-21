datatype treeS = emptyS
               | leafS of string
               | nodeS of treeS * treeS

fun inorder (emptyS: treeS): string list = nil
  | inorder (leafS x) = [x]
  | inorder (nodeS (tL, tR)) = (inorder tL) @ (inorder tR)

fun canonical' (emptyS: treeS): bool = false
  | canonical' (leafS _) = true
  | canonical' (nodeS (tL, tR)) =
    canonical' tL andalso canonical' tR

fun canonical (emptyS: treeS): bool = true
  | canonical t = canonical' t

(* normalize t --> t'
   Satifies:
   - inorder t == inorder (normalize t)
   - canonical t' == true
 *)
fun normalize (emptyS: treeS): treeS = emptyS
  | normalize (leafS x) = leafS x
  | normalize (nodeS (tL, tR)) =
    (case (normalize tL, normalize tR)
       of (emptyS, tR') => tR'
        | (tL', emptyS) => tL'
        | (tL', tR')    => nodeS (tL', tR'))
;
