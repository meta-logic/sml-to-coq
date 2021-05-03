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

Generalizable All Variables.

Module Type KEY.

Parameter t : Type.

Parameter compare : (t * t)%type -> comparison.
End KEY.

Module Type DICT.

Parameter key : Type.

Definition entry {_a : Type} := (key * _a)%type.

Parameter dict : Type -> Type.

Parameter empty : forall  {_a : Type}, @dict _a.

Parameter lookup : forall  {_a : Type}, (key * @dict _a)%type -> @option _a.

Parameter insert : forall  {_a : Type}, (@entry _a * @dict _a)%type -> @dict _a.
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

Definition entry {_a : Type} := (key * _a)%type.

Definition dict {_a : Type} := key -> @option _a.

Equations empty (x1: key): @option _'13533 :=
  empty k := None.

Equations lookup `(x1: (key * key -> @option _a)%type): @option _a :=
  lookup (k, f) := (f k).

Equations insert `(x1: (@entry _a * key -> @option _a)%type): key -> @option _a :=
  insert ((k, v), f) := (fun _id13607 => 
  match _id13607 with
  | k' => 
  match (K.compare (k, k')) with
  | Eq => (Some v)  
  | _ => (f k')
  end
  end).
End Dict.

Module IntDict := !Dict IntKey.

Definition id1 := (IntDict.insert ((42, "answer"), IntDict.empty)).

Definition a := 
  match (IntDict.lookup (42, id1)) with
  (Some a) => a
  | _ => patternFailure
  end.
