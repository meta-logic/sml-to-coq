Require Import Bool.
Require Import List.
Import ListNotations.




Module List.

  (* How to use it? *)
  Variables (A : Type) (B : Type).

  Definition null (l:list A)   :=
    match l with
    | [] => true
    | _  => false
    end.

  Definition length (l:list A) := List.length l.

  Definition append (l1:list A) (l2:list A) := List.app l1 l2.
  Infix "@" := append (right associativity, at level 60).

  Definition hd (l:list A)     := List.hd l.

  Definition tl (l:list A)     := List.tl l.

  Fixpoint  last (l:list A)    := List.last l. 
  
  Definition getItem (l:list A):=
    match l with
    | [] => None
    | _  => Some (List.hd l, List.tl l)
    end.

  (* un-curry *)
  Definition nth (n:nat) (l:list A)  := List.nth n l. 

  (* un-curry *)
  Definition take (n:nat) (l:list A) := List.firstn n l.

  (* un-curry *)
  Definition drop (n:nat) (l:list A) := List.skipn n l.

  Definition rev (l:list A)          := List.rev l. 

  Definition concat (l:list(list A)) := List.concat l.

  (* un-curry *)
  Definition revAppend (l l': list A):= List.rev_append l l'.

  (* What is equivelant to unit in Coq? *)
  (*Definition app (f:A->unit) (l:list A): unit:= 
    match l with
    | [] => ()
    | a :: t => (f a); app f t
    end.*)

  Definition map (f: A->B) (l:list A) := List.map f l.

  Fixpoint mapPartial (f: A-> option B) (l:list A) :=
    match l with
    | [] => []
    | x::l' => match f x with 
               | None   => mapPartial f l'
               | Some y => y::mapPartial f l'
               end
    end.
 
  Definition find (f:A->bool) (l:list A)         := List.find f l.

  Definition filter (f:A->bool) (l:list A)       := List.filter f l.

  Definition partition (f:A->bool) (l:list A)    := List.partition f l.

  Fixpoint foldl (f:A * B ->B) (b0:B) (l:list A) :=
    match l with
    | nil => b0
    | cons a t => foldl f (f(a,b0)) t
    end.

  Fixpoint foldr (f:A * B ->B) (b0:B) (l:list A) :=
    match l with
    | nil => b0
    | cons a t => f(a, foldr f b0 t)
    end.

  (*You can't have a function named exists*)
  Definition existsb (f:A->bool) (l:list A) := List.existsb f l.

  Definition all (f:A->bool) (l:list A)     := List.forallb f l.

  Fixpoint tabulate' (time n:nat)(f:nat->A) (l:list A) :=
    match time with  
    | 0 => l
    | S time' => 
      match n with
      | 0  => f 0::l
      | n' =>(tabulate' time' (n'-1) f ((f n)::l)) 
      end
    end.

  (* un-curry *)
  Definition tabulate (n :nat) (f:nat->A) :=
    tabulate' n n f [].

  (* un-curry / collate f (l1, l2) *) 
  Fixpoint collate (f:A * A -> comparison) (l1 l2:list A): comparison:=
    match l1, l2 with
    | [],[] => Eq
    | [],_  => Lt
    | _ ,[] => Gt
    | x1::l1',x2::l2' => match f(x1,x2) with
                         | Eq     => collate f l1' l2'
                         | other  => other
                         end
   end.

End List.