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
