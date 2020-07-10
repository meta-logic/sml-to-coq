Require Import stringSml.
Require Import listSml.

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

  Definition reader A B := B -> option (A * B).

  Definition clamp (i: Z):Z := if Z.ltb i 0 then 0 else i.

  Definition padding (c:ascii) (i:Z): string := 
    String.implode(List.tabulate(clamp i, (fun _ => c) )).

  Definition padLeft (c:ascii) (i:Z) (s:string): string := 
    (padding c (i - String.size s)) ++ s.

  Definition padRight (c:ascii) (i:Z) (s:string): string := 
    s ++ (padding c (i - String.size s)).

  Fixpoint splitl' {A} (p: ascii->bool) (f: reader ascii A) (src: A) cs := 
    match f src with
    | None => (String.implode(List.rev cs), src)
    | Some(c, src') => if p c then splitl' p f src' (c::cs)
                       else (String.implode(List.rev cs), src)
    end.

  Fixpoint splitl {A} (p: ascii->bool) (f: reader ascii A) (src: A): string * A  :=
    splitl' p f src nil.

End StringCvt.