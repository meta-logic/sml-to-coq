Require Import stringSml.
Require Import listSml.
Require Import charSml.
Require Import optionSml.
Require Import ZArith.
Require Import Bool.

Module StringCvt.

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

  Local Definition padding (c:ascii) (i:Z): string := 
    String.implode(List.tabulate(clamp i, (fun _ => c) )).

  (*
    Sml: char -> int -> string -> string
    Coq: ascii -> Z -> string -> string
  *)
  Definition padLeft (c:ascii) (i:Z) (s:string): string := 
    (padding c (i - String.size s)) ++ s.

  (*
    Sml: char -> int -> string -> string
    Coq: ascii -> Z -> string -> string
  *)
  Definition padRight (c:ascii) (i:Z) (s:string): string := 
    s ++ (padding c (i - String.size s)).

  Local Fixpoint splitl' {A} (f: ascii->bool) (rdr: reader ascii A) (src: A) 
           (cs: list ascii) (time: nat):= 
           match time with
           | 0 => (String.implode(List.rev cs), src)
           | S time' =>
             match rdr src with
             | None => (String.implode(List.rev cs), src)
             | Some(c, src') => if f c then splitl' f rdr src' (c::cs) time'
                                else (String.implode(List.rev cs), src)
             end
           end.

  (*
    Sml: (char -> bool) -> (char, 'a) reader -> 'a -> string * 'a
    Coq: (ascii -> bool) -> reader ascii A -> A -> nat -> string * A
  *)
  Definition splitl {A} (f: ascii->bool) (rdr: reader ascii A) (src: A) 
           (time: nat): string * A  := splitl' f rdr src nil time.

  (*
    Sml: (char -> bool) -> (char, 'a) reader -> 'a -> string * 'a
    Coq: (ascii -> bool) -> reader ascii A -> A -> nat -> string
  *)
  Definition takel {A} (f: ascii->bool) (rdr: reader ascii A) (src: A) 
           (time: nat): string := let (a,b) := splitl f rdr src time in a.

  (*
    Sml: (char -> bool) -> (char, 'a) reader -> 'a -> string * 'a
    Coq: (ascii -> bool) -> reader ascii A -> A -> nat -> A
  *)
  Definition dropl {A} (f: ascii->bool) (rdr: reader ascii A) (src: A) 
           (time: nat): A := let (a,b) := splitl f rdr src time in b.

  (*
    Sml: (char, 'a) reader -> 'a -> 'a
    Coq: reader ascii A -> A -> nat -> A
  *)
  Definition skipWS {A} (rdr: reader ascii A) (src: A) (time: nat): A :=
    dropl (Char.isSpace) rdr src time.

  Definition cs:= Z.

  Local Definition rdr (s: string) (i: Z): option (ascii * Z) := 
    match (Z.leb (String.size(s)) i) || (Z.ltb 0 i) with
    | false => Some(String.sub(s, i), Z.add i 1)
    | true  => None
    end.

  (*
    Sml: ((char, cs) reader -> ('a, cs) reader) -> string -> 'a option
    Coq: (reader ascii cs -> reader A cs) -> string -> option A
  *)
  Definition scanString {A} (f: (reader ascii cs) -> (reader A cs)) 
             (s: string): option A := 
             Option.map (fun '(a, b) => a) ((f (rdr s) 0%Z): @ option(A * cs)).

End StringCvt.