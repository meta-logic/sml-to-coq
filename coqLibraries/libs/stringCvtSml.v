Require Import ZArith.

Module StringCvt.

 (*  Variable (A:Type) (B:Type). *)

  Inductive radix :=
    | BIN
    | OCT
    | DEC
    | HEX.

  Inductive realfmt :=
    | SCI (i : option Z)
    | FIX (i : option Z)
    | GEN (i : option Z)
    | EXACT.





End StringCvt.