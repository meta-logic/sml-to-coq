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
  rid_1_name : string;
  rid_1_age : Z;
  rid_1_height : float
}.

Definition r := rid_1.

Equations isBob (x1: rid_1): bool :=
  isBob 
{|
  rid_1_age  := _;
  rid_1_height  := _;
  rid_1_name  := "Bob"
|} := true;
  isBob 
{|
  rid_1_age  := _;
  rid_1_height  := _;
  rid_1_name  := _
|} := false.
