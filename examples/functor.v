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

Parameter empty : (forall  {_a : Type} , (@ dict _a)).

Parameter lookup : (forall  {_a : Type} , (key * (@ dict _a)) % type -> (@ option _a)).

Parameter insert : (forall  {_a : Type} , ((@ entry _a) * (@ dict _a)) % type -> (@ dict _a)).
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

Module K := Key.

Definition key := K.t.

Definition entry {_a : Type} := (key * _a) % type.

Definition dict {_a : Type} := key -> (@ option _a).

Definition empty {_'13510 : Type} := fun  _id13608 => 
  match _id13608 with
  | _ => (None : (@ option _'13510))
  end.

Equations empty {_'13519: Type} {_'13520: Type} (x1: _'13519): (@ option _'13520) :=
  empty _ := None.

Equations lookup {_a: Type} {_a: Type} (x1: (t * t -> (@ option _a)) % type): (@ option _a) :=
  lookup (k, f) := ((f : t -> (@ option _a)) k).

Equations insert {_a: Type} {_a: Type} (x1: ((t * _a) % type * t -> (@ option _a)) % type): key -> (@ option _a) :=
  insert ((k, v), f) := (fun  _id13609 => 
  match _id13609 with
  | k' => 
  match (K.compare (k, k')) with
  | Eq => ((Some : _a -> (@ option _a)) v)  
  | _ => (f k')
  end
  end).

Equations insert {_a: Type} {_a: Type} (x1: ((t * _a) % type * t -> (@ option _a)) % type) (x2: t): (@ option _a) :=
  insert ((k, v), f) k' := 
  match (K.compare (k, k')) with
  | Eq => ((Some : _a -> (@ option _a)) v)  
  | _ => (f k')
  end.
End Dict.

Module IntDict := !Dict IntKey.

Definition id {_'13598 : Type} := (IntDict.empty : (@ dict _'13598)).

Definition id1 := (IntDict.insert ((42, "answer"), id)).
