Require Import Maps.
Require Import Program.
Require Import Interval.

Fixpoint int_aeval (st : id -> interval) (a : aexp) : interval :=
  match a with
  | ANum n => IInterval (Some n) (Some n)
  | AId x => st x
  | APlus a1 a2 => Interval.add (int_aeval st a1) (int_aeval st a2)
  | AMinus a1 a2  => Interval.add (int_aeval st a1) (Interval.neg (int_aeval st a2))
  | AMult a1 a2 => Interval.mul (int_aeval st a1) (int_aeval st a2)
  end.

Lemma int_aeval_sound: forall (st : state) (m : total_map interval) (a : aexp),
  (forall (x : id), include (m x) (st x)) ->
  include (int_aeval m a) (aeval st a).
Admitted.