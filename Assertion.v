Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Require Import Maps.
Require Import Program.
Require Import Interval.

Section List_map.

Variable A : Type.

Variable default : A.

Definition list_map := list (id * A).

Fixpoint list_to_map (ls : list_map) :=
  match ls with
  | nil => t_empty default
  | cons (hd1, hd2) tl => t_update (list_to_map tl) hd1 hd2
  end.

End List_map.

Definition assertion : Type := list_map interval.

Definition default_interval : interval := IInterval (Some 0) (Some 0).

Definition empty : assertion := nil.

Definition assertion_to_map : assertion -> total_map interval :=
  list_to_map interval default_interval.

Definition state_in_range (st : state) (m : total_map interval) : Prop :=
  forall (x : id), include (m x) (st x).

Definition state_in_assertion (st : state) (s : assertion) :=
  state_in_range st (assertion_to_map s).

Notation "st |= s" := (state_in_assertion st s) (at level 18).

Definition assertion_in_assertion (s1 : assertion) (s2 : assertion) :=
  forall st : state, state_in_assertion st s1 -> state_in_assertion st s2.

Notation "s1 |== s2" := (assertion_in_assertion s1 s2) (at level 18).


(* Operations on assertions *)

Fixpoint list_leb (s1 s2 : assertion) : bool :=
  match s1 with
  | nil => true
  | cons (hd1, hd2) tl =>
    Interval.leb hd2 (assertion_to_map s2 hd1) && list_leb tl s2
  end.

Fixpoint list_geb (s1 s2 : assertion) : bool :=
  match s1 with
  | nil => true
  | cons (hd1, hd2) tl =>
    Interval.geb hd2 (assertion_to_map s2 hd1) && list_geb tl s2
  end.

Fixpoint list_eqb (s1 s2 : assertion) : bool :=
  match s1 with
  | nil => true
  | cons (hd1, hd2) tl =>
    Interval.eqb hd2 (assertion_to_map s2 hd1) && list_eqb tl s2
  end.

Definition leb (s1 s2 : assertion) : bool :=
  list_leb s1 s2 && list_geb s2 s1.

Definition geb (s1 s2 : assertion) : bool :=
  leb s2 s1.

Definition eqb (s1 s2 : assertion) : bool :=
  list_eqb s1 s2 && list_eqb s2 s1.


(* Props on assertions *)

Definition le (s1 s2 : assertion) : Prop :=
  forall x, Interval.le (assertion_to_map s1 x) (assertion_to_map s2 x).

Definition feq (s1 s2 : assertion) : Prop :=
  forall x, Interval.feq (assertion_to_map s1 x) (assertion_to_map s2 x).

Lemma list_leb_prop : forall x s1 s2,
  list_leb s1 s2 = true ->
  assertion_to_map s1 x <> default_interval ->
  Interval.le (assertion_to_map s1 x) (assertion_to_map s2 x).
Proof.
  intros.
  induction s1.
  - (* s1 = nil *)
    exfalso. apply H0. auto.
  - (* s1 = cons *)
    destruct a as [y r].
    simpl in *. unfold t_update in *.
    destruct (beq_id y x) eqn:Heq.
    + rewrite beq_id_true_iff in Heq.
      subst. apply Interval.leb_le.
      apply andb_prop in H. tauto.
    + apply IHs1.
      * apply andb_prop in H. tauto.
      * auto.
Qed.

Lemma list_geb_prop : forall x s1 s2,
  list_geb s1 s2 = true ->
  assertion_to_map s1 x <> default_interval ->
  Interval.ge (assertion_to_map s1 x) (assertion_to_map s2 x).
Proof.
  intros.
  induction s1.
  - (* s1 = nil *)
    exfalso. apply H0. auto.
  - (* s1 = cons *)
    destruct a as [y r].
    simpl in *. unfold t_update in *.
    destruct (beq_id y x) eqn:Heq.
    + rewrite beq_id_true_iff in Heq.
      subst. apply Interval.leb_le.
      apply andb_prop in H. tauto.
    + apply IHs1.
      * apply andb_prop in H. tauto.
      * auto.
Qed.

Ltac specialize_ H :=
  match type of H with
  | ?A -> ?B =>
    let HA := fresh "H" in
    assert A as HA; [ | specialize (H HA); clear HA]
  end.

Lemma leb_le : forall x s1 s2,
  leb s1 s2 = true ->
  Interval.le (assertion_to_map s1 x) (assertion_to_map s2 x).
Proof.
  intros. apply andb_prop in H. destruct H.
  pose (list_leb_prop x _ _ H) as Hleb.
  pose (list_geb_prop x _ _ H0) as Hgeb.
  destruct (Interval.eq_dec (assertion_to_map s1 x) (default_interval));
  destruct (Interval.eq_dec (assertion_to_map s2 x) (default_interval));
  try solve [apply Hleb; auto];
  try solve [apply Hgeb; auto].
  (* assertion_to_map s1 x = default_interval
     and
     assertion_to_map s2 x = default_interval
  *)
  rewrite e, e0.
  apply Interval.leb_le.
  (* TODO *)
  (* leb not implemented *)
Admitted.

Lemma list_eqb_prop : forall x s1 s2,
  list_eqb s1 s2 = true ->
  assertion_to_map s1 x <> default_interval ->
  Interval.feq (assertion_to_map s1 x) (assertion_to_map s2 x).
Proof.
  intros.
  induction s1.
  - (* s1 = nil *)
    exfalso. apply H0. auto.
  - (* s1 = cons *)
    destruct a as [y r].
    simpl in *. unfold t_update in *.
    destruct (beq_id y x) eqn:Heq.
    + rewrite beq_id_true_iff in Heq.
      subst. apply Interval.eqb_feq.
      apply andb_prop in H. tauto.
    + apply IHs1.
      * apply andb_prop in H. tauto.
      * auto.
Qed.

Lemma eqb_feq : forall x s1 s2,
  eqb s1 s2 = true ->
  Interval.feq (assertion_to_map s1 x) (assertion_to_map s2 x).
Proof.
  intros. apply andb_prop in H. destruct H.
  pose (list_eqb_prop x _ _ H) as Heqb1.
  pose (list_eqb_prop x _ _ H0) as Heqb2.
  destruct (Interval.eq_dec (assertion_to_map s1 x) (default_interval));
  destruct (Interval.eq_dec (assertion_to_map s2 x) (default_interval));
  try solve [apply Heqb1; auto];
  try solve [apply Interval.feq_sym; apply Heqb2; auto].
  (* assertion_to_map s1 x = default_interval
     and
     assertion_to_map s2 x = default_interval
  *)
  rewrite e, e0.
  apply Interval.eqb_feq.
  (* TODO *)
  (* eqb not implemented *)
Admitted.

Lemma le_assertion_in_assertion : forall s1 s2,
  le s1 s2 -> s1 |== s2.
Proof.
  unfold le, assertion_in_assertion.
  intros. intro x.
  apply H. apply H0.
Qed.


