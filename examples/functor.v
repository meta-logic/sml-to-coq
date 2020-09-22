Require Import intSml.
Require Import listSml.
Require Import realSml.
Require Import stringSml.
Require Import charSml.
Require Import boolSml.
Require Import optionSml.
Require Import listPairSml.
Require Import notationsSml.
From Equations Require Import Equations.

Module Type KEY.

Parameter t : Type.

Parameter compare : (t * t) % type -> comparison.
End KEY.

Module Type DICT.

Parameter key : Type.

Definition entry {_a : Type} := (key * _a) % type.

Parameter dict : Type -> Type.

(*Parameter empty : @ dict _a.

Parameter lookup : (key * @ dict _a) % type -> @ option _a.

Parameter insert : (@ entry _a * @ dict _a) % type -> @ dict _a.*)
End DICT.

Module IntKey : KEY with 
Definition t := Z.

Definition t := Z.

Definition compare := Int.compare.
End IntKey.

Module StringKey <: KEY.

Definition t := string.

Definition compare := String.compare.
End StringKey.

Module Dict ( Key : KEY ) : DICT with 
Definition key := Key.t.

Module K.
Key
End K.

Definition key := K.t.

Definition entry {_a : Type} := (key * _a) % type.

Definition dict {_a : Type} := key -> @ option _a.

Definition empty {_'13421 : Type} := fun  _ => (None : @ option _'13421).

Equations empty {_'13431: Type} (x1: _'13430): @ option _'13431 :=
  empty (_) := (None : @ option _'13431).

Equations lookup (x1: (t * t -> @ option 'a) % type): @ option _a :=
  lookup ((k, f)) := (f k).

Equations insert {'a: Type} (x1: ((t * 'a) % type * t -> @ option 'a) % type): key -> @ option _a :=
  insert (((k, v), f)) := (fun  k' => 
  match (K.compare (k, k')) with
  | Eq => (Some (v : 'a))  
  | _ => (f k')
  end).

Equations insert (x1: ((t * 'a) % type * t -> @ option 'a) % type) (x2: t): @ option _a :=
  insert (((k, v), f) k') := 
  match (K.compare (k, k')) with
  | Eq => (Some v)  
  | _ => (f k')
  end.
End Dict.

Module IntDict.
!Dict IntKey
End IntDict.

Definition id {_'13509 : Type} := (IntDict.empty : @ dict _'13509).

Definition id1 := (IntDict.insert ((42, "answer"), id)).

