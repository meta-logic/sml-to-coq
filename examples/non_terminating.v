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

Fail Equations div_two (n : nat) : nat :=
div_two 0 := 0;
div_two 1 := 0;
div_two n := 1 + div_two (n / 2) .

Equations div_two (n : nat) : nat by wf n lt :=
div_two 0 := 0;
div_two 1 := 0;
div_two n := 1 + div_two (n / 2) .
Obligation 1.
  assert (fst (Nat.divmod n0 1 1 1) = Nat.div (S (S n0)) 2); auto.
  rewrite H. apply  Nat.div_lt.
  + apply Nat.lt_0_succ.
  + auto.
Qed.

Equations collatz ( n : nat ): @list nat by wf n lt :=
collatz 1 := [1%nat];
collatz n := ( n :: (
match (modulo n 2%nat) with
| 0%nat => ( collatz (( n / 2)))
| _ => ( collatz (((3 * n ) + 1)))
end )).

Fail Equations loop1 (x1: Z): _'13722 :=
  loop1 x := (loop1 ((x + 1))).

Fail Equations loop2 (x1: Z): _'13732 :=
  loop2 x := (loop2 ((x - 1))).

Fail Equations loop3 `(x1: @list _'13748) {H: exists y1 y2 , eq (x1) (y1 :: y2)}: _'13749 :=
  loop3 (x :: l) := (@loop3 ((l @ [x])) _);
  loop3 _ := _.
Admit Obligations.

Fail Equations fact (x1: Z): Z :=
  fact 0 := 1;
  fact n := (n * (fact ((n - 1)))).

Fail Equations collatz (x1: Z): @list Z :=
  collatz 1 := [1];
  collatz n := (n :: (
  match (n mod 2) with
  | 0 => (collatz ((n div 2)))  
  | _ => (collatz (((3 * n) + 1)))
  end)).
