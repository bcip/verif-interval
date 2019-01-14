Require Import Assertion.
Require Import Annotation.
Require Import IntervalEval.

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

(* TODO placeholder *)
Definition forward_cond (s : assertion) (b : bexp) : assertion.
Admitted.

Lemma forward_cond_valid (s : assertion) (b : bexp) (res : assertion) :
  res = forward_cond s b ->
  (forall st : state, st |= s -> beval st b = true -> st |= res).
Admitted.

Definition forward_cond_true (s : assertion) (b : bexp) : assertion :=
  forward_cond s b.

Lemma forward_cond_true_valid (s : assertion) (b : bexp) (res : assertion) :
  res = forward_cond_true s b ->
  (forall st : state, st |= s -> beval st b = true -> st |= res).
Proof.
  apply forward_cond_valid.
Qed.

Definition forward_cond_false (s : assertion) (b : bexp) : assertion :=
  forward_cond s (BNot b).

Lemma forward_cond_false_valid (s : assertion) (b : bexp) (res : assertion) :
  res = forward_cond_false s b ->
  (forall st : state, st |= s -> beval st b = false -> st |= res).
Proof.
  intros. assert (beval st (BNot b) = true). {
    simpl. rewrite H1.  auto.
  }
  eapply forward_cond_valid with (b := (BNot b)); eauto.
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

