Require Import Maps.
Require Import Program.
Require Import Interval.

Axiom int_aeval: (total_map interval) -> aexp -> interval.

(* Fixpoint int_aeval (st : Id -> interval) (a : aexp) : interval :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end. *)

Lemma int_aeval_sound: forall (st : state) (m : total_map interval) (a : aexp),
  (forall (x : id), include (m x) (st x)) ->
  include (int_aeval m a) (aeval st a).
Admitted.