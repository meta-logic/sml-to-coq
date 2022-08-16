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


Record rid_1  `(_a : Type) := 
{
  rid_1_f : _a
}.

Definition t  := rid_1.

Equations foo `(x1: (t _a)): Z :=
  foo r := 0.

Definition bar := 
{|
  rid_1_f  := 1
|}.

Definition res := ((foo bar)).

Record rid_3  := 
{
  rid_3_f : _a
}.

Definition t {_a : Type} := rid_3.

Equations foo (x1: (@ t _a)): Z :=
  foo r := 0.

Definition bar := 
{|
  rid_3_f  := 1
|}.
(* Inductive treeS  : Type :=  *)
(*   | emptyS   *)
(*   | leafS : (string -> (@ treeS ))   *)
(*   | nodeS : ((treeS * treeS) % type -> (@ treeS )). *)

(* Equations inorder (x1: treeS): (@ list string) := *)
(*   inorder emptyS := nil; *)
(*   inorder (leafS x) := [x]; *)
(*   inorder (nodeS (tL, tR)) := (((inorder tL))) @ (((inorder tR))). *)

(* Equations normal' (x1: treeS): bool := *)
(*   normal' emptyS := false; *)
(*   normal' (leafS _) := true; *)
(*   normal' (nodeS (tL, tR)) := ((normal' tL)) && ((normal' tR)). *)

(* Equations normal (x1: treeS): bool := *)
(*   normal emptyS := true; *)
(*   normal t := ((normal' t)). *)

(* Equations normalize (x1: treeS): treeS := *)
(*   normalize emptyS := emptyS; *)
(*   normalize (leafS x) := ((leafS x)); *)
(*   normalize (nodeS (tL, tR)) := ( *)
(*   match (((normalize tL)), ((normalize tR))) with *)
(*   | (emptyS, tR') => tR'   *)
(*   | (tL', emptyS) => tL'   *)
(*   | (tL', tR') => ((nodeS (tL', tR'))) *)
(*   end). *)

(* Theorem preserve_order : forall T, inorder T = inorder (normalize T). *)
(* Proof. *)
(*   intros. funelim (inorder T). *)
(*   + auto. *)
(*   + auto. *)
(*   + rewrite normalize_equation_3. destruct (normalize t) eqn:E. *)
(*     - rewrite H. rewrite H0. auto. *)
(*     - destruct (normalize t0) eqn:E'; rewrite H; rewrite H0; auto. *)
(*     - destruct (normalize t0) eqn:E'. *)
(*       * rewrite <- H. rewrite <- app_nil_r. rewrite <- inorder_equation_1.  *)
(*         rewrite <- H0. auto. *)
(*       * rewrite inorder_equation_3. rewrite H0. rewrite H. auto. *)
(*       * rewrite inorder_equation_3. rewrite H0. rewrite H. auto. *)
(* Qed. *)

(* (* This lemma is supposed to help in the proof below, at least on paper *) *)
(* Lemma non_empty_normal : forall T t x, (eq (normalize T) (nodeS t)) \/ (eq (normalize T) (leafS x)) *)
(*   -> normal' (normalize T) = true. *)
(* Proof. *)
(*   intros. funelim (normalize T). *)
(*   - destruct H; discriminate H. *)
(*   - auto. *)
(*   - rewrite normalize_equation_3 in H1. destruct (normalize t). *)
(*     + apply (H0 t1 x). apply H1.  *)
(*     + destruct (normalize t0). *)
(*       * auto.  *)
(*       * auto.  *)
(*       * rewrite normal'_equation_3. rewrite (H0 p x); auto.  *)
(*     +  destruct (normalize t0). *)
(*       * apply (H t1 x); auto.  *)
(*       * rewrite normal'_equation_3. rewrite (H0 t1 s); auto. rewrite (H p x); auto.  *)
(*       * rewrite normal'_equation_3. rewrite (H0 p0 x); auto. rewrite (H p x); auto. *)
(* Qed. *)

(* Theorem normalize_correctness : forall T, normal (normalize T) = true. *)
(* Proof. *)
(*   intros. destruct (normalize T) eqn:E. *)
(*   + auto. *)
(*   + auto.  *)
(*   + destruct T eqn:E'. *)
(*     * rewrite normalize_equation_1 in E. discriminate E.  *)
(*     * rewrite normalize_equation_2 in E. discriminate E. *)
(*     * rewrite normal_equation_3. rewrite <- E. eapply (non_empty_normal _ p ""). left; auto. *)
(* Qed. *)
