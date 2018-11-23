Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.
Open Scope Z_scope.

Inductive interval : Type :=
  | IInterval : forall (lo hi : option Z), interval.

Definition include (i : interval) (x : Z) : Prop :=
  match i with
  | IInterval lo hi =>
    match lo with
    | Some y => y <= x
    | None => True
    end /\
    match hi with
    | Some z => x <= z
    | None => True
    end
  end.

Definition inb (i : interval) (x : Z) : bool :=
  match i with
  | IInterval lo hi =>
    let lob := match lo with
              | Some y => Z.leb y x
              | None => true
              end
    in
    let hib := match hi with
              | Some z => Z.leb x z
              | None => true
              end
    in
    andb lob hib
  end.

(* Lemma include_inb : forall i x,
  include i x -> inb i x = true. *)