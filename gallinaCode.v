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

Record rid_1  := 
{
  rid_1_f : _a
}.

Equations foo {_a: Type} (x1: rid_1): Z :=
  foo r := 0.

Definition bar := 
{|
  rid_1_f  := 1
|}.
