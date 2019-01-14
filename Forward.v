Require Import Interval.
Require Import Assertion.
Require Import Annotation.


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
Proof.
  intros. induction a.
  - unfold int_aeval, aeval, include; split; apply BinInt.Z.le_refl.
  - unfold int_aeval, aeval; auto.
  - simpl; apply add_sound; auto.
  - simpl; apply minus_sound; auto.
  - simpl; apply mul_sound; auto.
Qed.

Definition forward_skip (s s' : assertion) : assertion :=
  join s s'.

Lemma forward_skip_valid (s s' res : assertion) :
  res = forward_skip s s' ->
  step_valid' s (ASkip res).
Proof.
  intros. subst.
  apply SVSkip. apply le_assertion_in_assertion.
  eapply proj1. apply join_sound.
Qed.

Definition forward_ass (s : assertion) (x : id) (a1 : aexp) (s' : assertion) : assertion :=
  join (assign s x (int_aeval (assertion_to_map s) a1)) s'.

Lemma forward_ass_valid (s : assertion) (x : id) (a1 : aexp) (s' res : assertion) :
  res = forward_ass s x a1 s' ->
  step_valid' s (AAss x a1 res).
Proof.
  intros. subst.
  apply SVAss. intros.
  eapply le_assertion_in_assertion.
  - eapply proj1. apply join_sound.
  - apply assign_sound.
    + auto.
    + apply int_aeval_sound. auto.
Qed.

Definition get_id (a : aexp) : option id :=
  match a with
  | AId x => Some x
  | _ => None
  end.

Definition forward_eq (s : assertion) (a1 a2 : aexp) (ans : bool) : assertion :=
  let r1 := int_aeval (assertion_to_map s) a1 in
  let r2 := int_aeval (assertion_to_map s) a2 in
  eq_cond s (get_id a1) (get_id a2) r1 r2 ans.

Definition forward_le (s : assertion) (a1 a2 : aexp) (ans : bool) : assertion :=
  let r1 := int_aeval (assertion_to_map s) a1 in
  let r2 := int_aeval (assertion_to_map s) a2 in
  le_cond s (get_id a1) (get_id a2) r1 r2 ans.

Fixpoint forward_cond (s : assertion) (b : bexp) (ans : bool) : assertion :=
  match b with
  | BTrue => if ans then s else None
  | BFalse => if ans then None else s
  | BEq a1 a2 => forward_eq s a1 a2 ans
  | BLe a1 a2 => forward_le s a1 a2 ans
  | BNot b' => forward_cond s b' (negb ans)
  | BAnd b1 b2 =>
    if ans
    then meet (forward_cond s b1 true) (forward_cond s b2 true)
    else join (forward_cond s b1 false) (forward_cond s b2 false)
  | BOr b1 b2 =>
    if ans
    then join (forward_cond s b1 true) (forward_cond s b2 true)
    else meet (forward_cond s b1 false) (forward_cond s b2 false)
  end.

Lemma join_sound1 : forall (s1 s2 : assertion),
  s1 |== join s1 s2.
Proof.
  intros. apply le_assertion_in_assertion. eapply proj1, join_sound.
Qed.

Lemma join_sound2 : forall (s1 s2 : assertion),
  s2 |== join s1 s2.
Proof.
  intros. apply le_assertion_in_assertion. eapply proj2, join_sound.
Qed.

Lemma forward_cond_valid (s : assertion) (b : bexp) (ans : bool) (res : assertion) :
  res = forward_cond s b ans ->
  (forall st : state, st |= s -> beval st b = ans -> st |= res).
Proof.
  intros. generalize dependent res. generalize dependent ans. induction b; intros; subst ans; simpl in *.
  1, 2 : rewrite H; apply H0.
  (* 3, 4 *)
  1, 2 : unfold forward_eq, forward_le in *; subst res;
    first [eapply eq_cond_sound | eapply le_cond_sound]; auto;
    try (apply int_aeval_sound; auto);
    try destruct a; try destruct a0; simpl; auto.
  (* 5 *)
  rewrite Bool.negb_involutive in *; eauto.
  (* 6, 7 *)
  all: specialize (IHb1 _ ltac:(reflexivity)); specialize (IHb2 _ ltac:(reflexivity)).
  all : destruct (beval st b1) eqn:?; destruct (beval st b2) eqn:?; simpl in *;
    subst res;
    simple apply meet_sound + simple apply join_sound1 + simple apply join_sound2;
    simple apply IHb1 + simple apply IHb2; match goal with |- ?A = ?B => constr_eq A B; reflexivity; fail 100 end.
Qed.

Definition forward_cond_true (s : assertion) (b : bexp) : assertion :=
  forward_cond s b true.

Lemma forward_cond_true_valid (s : assertion) (b : bexp) (res : assertion) :
  res = forward_cond_true s b ->
  (forall st : state, st |= s -> beval st b = true -> st |= res).
Proof.
  apply forward_cond_valid.
Qed.

Definition forward_cond_false (s : assertion) (b : bexp) : assertion :=
  forward_cond s b false.

Lemma forward_cond_false_valid (s : assertion) (b : bexp) (res : assertion) :
  res = forward_cond_false s b ->
  (forall st : state, st |= s -> beval st b = false -> st |= res).
Proof.
  apply forward_cond_valid.
Qed.

Lemma forward_if (s : assertion) (b : bexp) (A1 A2 : annotation) (s' : assertion) :
  step_valid A1 ->
  step_valid A2 ->
  (forall st : state, st |= s -> beval st b = true -> st |= precondition A1) ->
  (forall st : state, st |= s -> beval st b = false -> st |= precondition A2) ->
  forall (res : assertion),
  res = join s' (join (postcondition A1) (postcondition A2)) ->
  step_valid' s (AIf b A1 A2 res).
Proof.
  intros. apply SVIf; auto.
  all : subst; eapply assertion_in_assertion_trans; apply le_assertion_in_assertion;
  [ | eapply proj2; eapply join_sound].
  - eapply proj1; eapply join_sound.
  - eapply proj2; eapply join_sound.
Qed.

