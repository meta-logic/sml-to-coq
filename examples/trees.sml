datatype treeS = emptyS
               | leafS of string
               | nodeS of treeS * treeS

fun inorder (emptyS: treeS): string list = nil
  | inorder (leafS x) = [x]
  | inorder (nodeS (tL, tR)) = (inorder tL) @ (inorder tR)

fun normal' (emptyS: treeS): bool = false
  | normal' (leafS _) = true
  | normal' (nodeS (tL, tR)) =
    normal' tL andalso normal' tR

fun normal (emptyS: treeS): bool = true
  | normal t = normal' t

(* normalize t --> t'
   Satifies:
   - inorder t == inorder (normalize t)
   - normal t' == true
 *)
fun normalize (emptyS: treeS): treeS = emptyS
  | normalize (leafS x) = leafS x
  | normalize (nodeS (tL, tR)) =
    (case (normalize tL, normalize tR)
       of (emptyS, tR') => tR'
        | (tL', emptyS) => tL'
        | (tL', tR')    => nodeS (tL', tR'))
;
