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

Fixpoint update (ls : list_map) (x : id) (v : A) :=
  match ls with
  | nil => [(x, v)]
  | (hd1, hd2) :: tl =>
    if beq_id x hd1 then
      (x, v) :: tl
    else
      (hd1, hd2) :: update tl x v
  end.

Lemma update_spec : forall (ls : list_map) (x : id) (v : A) (x' : id),
  list_to_map (update ls x v) x' = t_update (list_to_map ls) x v x'.
Proof.
  intros. induction ls; auto.
  simpl; destruct a as [hd1 hd2]; destruct (beq_id x hd1) eqn:?.
  - rewrite beq_id_true_iff in *.
    subst hd1. rewrite t_update_shadow. auto.
  - rewrite beq_id_false_iff in *.
    rewrite t_update_permute by auto.
    simpl. unfold t_update at 1 2. rewrite IHls. auto.
Qed.

Fixpoint has_key (ls : list_map) (x : id) : bool :=
  match ls with
  | nil => false
  | (hd1, hd2) :: tl =>
    if beq_id hd1 x then true else has_key tl x
  end.

Lemma not_has_key_default : forall (ls : list_map) (x : id),
  has_key ls x = false ->
  list_to_map ls x = default.
Proof.
  intros; induction ls.
  - auto.
  - simpl. destruct a as [hd1 hd2]. unfold t_update.
    simpl in H. destruct (beq_id hd1 x); try discriminate.
    auto.
Qed.

Fixpoint merge_aux_l (l s : list_map) (f : A -> A -> A) : list_map :=
  match l with
    | nil => nil
    | (hd1, hd2) :: tl =>
      (hd1, f hd2 (list_to_map s hd1)) :: merge_aux_l tl s f
    end.

Fixpoint merge_aux_s (l s : list_map) (f : A -> A -> A) (new_l : list_map): list_map :=
    match s with
    | nil => new_l
    | (hd1, hd2) :: tl =>
      if has_key l hd1
      then merge_aux_s l tl f new_l
      else (hd1, f default hd2) :: merge_aux_s l tl f new_l
    end.

Definition merge (l s : list_map) (f : A -> A -> A) : list_map :=
  merge_aux_s l s f (merge_aux_l l s f).

Theorem merge_spec : forall (l s : list_map) (f : A -> A -> A) (x : id),
  f default default = default ->
  list_to_map (merge l s f) x = f (list_to_map l x) (list_to_map s x).
Proof.
  intros.
  destruct (has_key l x) eqn:?.
  - (* has_key l x = true *)
    replace (list_to_map (merge l s f) x) with (list_to_map (merge_aux_l l s f) x). 2: {
      unfold merge. set (new_l := merge_aux_l l s f). clearbody new_l.
      induction s.
      + auto.
      + simpl. destruct a as [hd1 hd2].
        destruct (has_key l hd1) eqn:?; auto.
        simpl. unfold t_update.
        destruct (beq_id hd1 x) eqn:?; auto.
        rewrite beq_id_true_iff in *. congruence.
    }
    induction l.
    + inversion Heqb.
    + simpl. destruct a as [hd1 hd2]. simpl.
      unfold t_update.
      simpl in Heqb.
      destruct (beq_id hd1 x) eqn:?.
      * rewrite beq_id_true_iff in *. congruence.
      * auto.
  - (* has_key l x = false *)
    unfold merge. set (new_l := merge_aux_l l s f).
    assert (list_to_map l x = default). {
      induction l.
      + auto.
      + simpl. destruct a as [hd1 hd2]. unfold t_update.
        simpl in Heqb. destruct (beq_id hd1 x) eqn:?.
        * discriminate.
        * auto.
    }
    assert (list_to_map new_l x = default). {
      subst new_l. clear H0. induction l.
      + auto.
      + simpl. destruct a as [hd1 hd2]. simpl. unfold t_update.
        simpl in Heqb. destruct (beq_id hd1 x) eqn:?.
        * discriminate.
        * auto.
    }
    clearbody new_l.
    induction s.
    + simpl. unfold t_empty. congruence.
    + simpl. destruct a as [hd1 hd2].
      destruct (has_key l hd1) eqn:?.
      * unfold t_update.
        destruct (beq_id hd1 x) eqn:?.
        -- rewrite beq_id_true_iff in *. congruence.
        -- auto.
      * simpl. unfold t_update.
        destruct (beq_id hd1 x) eqn:?.
        -- rewrite beq_id_true_iff in *. congruence.
        -- auto.
Qed.

End List_map.

Definition assertion : Type := option (list_map interval).

Definition bottom : assertion := None.

Definition default : assertion := Some nil.

Definition list_assertion_to_map : list_map interval -> total_map interval :=
  list_to_map interval default_interval.

Definition assertion_to_map (s : assertion) : total_map interval :=
  match s with
  | Some l => list_assertion_to_map l
  | None => list_to_map interval empty_interval nil
  end.

Definition state_in_range (st : state) (m : total_map interval) : Prop :=
  forall (x : id), include (m x) (st x).

Definition state_in_assertion (st : state) (s : assertion) :=
  state_in_range st (assertion_to_map s).

Notation "st |= s" := (state_in_assertion st s) (at level 18).

Definition assertion_in_assertion (s1 : assertion) (s2 : assertion) :=
  forall st : state, state_in_assertion st s1 -> state_in_assertion st s2.

Notation "s1 |== s2" := (assertion_in_assertion s1 s2) (at level 18).

(* Operations on assertions *)

Fixpoint list_leb (l1 l2 : list_map interval) : bool :=
  match l1 with
  | nil => true
  | cons (hd1, hd2) tl =>
    Interval.leb hd2 (list_assertion_to_map l2 hd1) && list_leb tl l2
  end.

Fixpoint list_geb (l1 l2 : list_map interval) : bool :=
  match l1 with
  | nil => true
  | cons (hd1, hd2) tl =>
    Interval.geb hd2 (list_assertion_to_map l2 hd1) && list_geb tl l2
  end.

Fixpoint list_eqb (l1 l2 : list_map interval) : bool :=
  match l1 with
  | nil => true
  | cons (hd1, hd2) tl =>
    Interval.eqb hd2 (list_assertion_to_map l2 hd1) && list_eqb tl l2
  end.

Definition leb (s1 s2 : assertion) : bool :=
  match s1, s2 with
  | None, _ => true
  | _, None => false
  | Some l1, Some l2 =>
    list_leb l1 l2 && list_geb l2 l1
  end.

Definition geb (s1 s2 : assertion) : bool :=
  leb s2 s1.

Definition eqb (s1 s2 : assertion) : bool :=
  match s1, s2 with
  | None, None => true
  | Some l1, Some l2 =>
    list_eqb l1 l2 && list_eqb l2 l1
  | _, _ => false
  end.

(* Props on assertions *)

Definition le (s1 s2 : assertion) : Prop :=
  forall x, Interval.le (assertion_to_map s1 x) (assertion_to_map s2 x).

Definition feq (s1 s2 : assertion) : Prop :=
  forall x, Interval.feq (assertion_to_map s1 x) (assertion_to_map s2 x).

Lemma list_leb_prop : forall x l1 l2,
  list_leb l1 l2 = true ->
  list_assertion_to_map l1 x <> default_interval ->
  Interval.le (list_assertion_to_map l1 x) (list_assertion_to_map l2 x).
Proof.
  intros.
  induction l1.
  - (* l1 = nil *)
    exfalso. apply H0. auto.
  - (* l1 = cons *)
    destruct a as [y r].
    simpl in *. unfold t_update in *.
    destruct (beq_id y x) eqn:Heq.
    + rewrite beq_id_true_iff in Heq.
      subst. apply Interval.leb_le.
      apply andb_prop in H. tauto.
    + apply IHl1.
      * apply andb_prop in H. tauto.
      * auto.
Qed.

Lemma list_geb_prop : forall x l1 l2,
  list_geb l1 l2 = true ->
  list_assertion_to_map l1 x <> default_interval ->
  Interval.ge (list_assertion_to_map l1 x) (list_assertion_to_map l2 x).
Proof.
  intros.
  induction l1.
  - (* l1 = nil *)
    exfalso. apply H0. auto.
  - (* l1 = cons *)
    destruct a as [y r].
    simpl in *. unfold t_update in *.
    destruct (beq_id y x) eqn:Heq.
    + rewrite beq_id_true_iff in Heq.
      subst. apply Interval.leb_le.
      apply andb_prop in H. tauto.
    + apply IHl1.
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
  intros.
  destruct s1 as [l1 | ]; destruct s2 as [l2 | ]; simpl; try discriminate.
  apply andb_prop in H. destruct H.
  pose (list_leb_prop x _ _ H) as Hleb.
  pose (list_geb_prop x _ _ H0) as Hgeb.
  destruct (Interval.eq_dec (list_assertion_to_map l1 x) (default_interval));
  destruct (Interval.eq_dec (list_assertion_to_map l2 x) (default_interval));
  try solve [apply Hleb; auto];
  try solve [apply Hgeb; auto].
  rewrite e, e0.
  all : apply Interval.leb_le; compute; auto.
Qed.

Lemma list_eqb_prop : forall x l1 l2,
  list_eqb l1 l2 = true ->
  list_assertion_to_map l1 x <> default_interval ->
  Interval.feq (list_assertion_to_map l1 x) (list_assertion_to_map l2 x).
Proof.
  intros.
  induction l1.
  - (* l1 = nil *)
    exfalso. apply H0. auto.
  - (* l1 = cons *)
    destruct a as [y r].
    simpl in *. unfold t_update in *.
    destruct (beq_id y x) eqn:Heq.
    + rewrite beq_id_true_iff in Heq.
      subst. apply Interval.eqb_feq.
      apply andb_prop in H. tauto.
    + apply IHl1.
      * apply andb_prop in H. tauto.
      * auto.
Qed.

Lemma eqb_feq : forall x s1 s2,
  eqb s1 s2 = true ->
  Interval.feq (assertion_to_map s1 x) (assertion_to_map s2 x).
Proof.
  intros.
  destruct s1 as [l1 | ]; destruct s2 as [l2 | ]; simpl; try discriminate.
  apply andb_prop in H. destruct H.
  pose (list_eqb_prop x _ _ H) as Heqb1.
  pose (list_eqb_prop x _ _ H0) as Heqb2.
  destruct (Interval.eq_dec (list_assertion_to_map l1 x) (default_interval));
  destruct (Interval.eq_dec (list_assertion_to_map l2 x) (default_interval));
  try solve [apply Heqb1; auto];
  try solve [apply Interval.feq_sym; apply Heqb2; auto].
  rewrite e, e0.
  all : apply Interval.eqb_feq; compute; auto.
Qed.

Lemma le_assertion_in_assertion : forall s1 s2,
  le s1 s2 -> s1 |== s2.
Proof.
  unfold le, assertion_in_assertion.
  intros. intro x.
  apply H. apply H0.
Qed.

Definition join_base (s1 s2 : assertion) (f : interval -> interval -> interval) : assertion :=
  match s1, s2 with
  | None, _ => s2
  | _, None => s1
  | Some l1, Some l2 =>
    Some (merge _ default_interval l1 l2 f)
  end.

Theorem join_base_sound : forall (s1 s2 : assertion) (f : interval -> interval -> interval),
  f default_interval default_interval = default_interval ->
  (forall x y, Interval.le x (f x y)) ->
  (forall x y, Interval.le y (f x y)) ->
  le s1 (join_base s1 s2 f) /\ le s2 (join_base s1 s2 f).
Proof.
  intros.
  unfold le, join.
  destruct s1 as [l1 | ]; destruct s2 as [l2 | ];
  split; intros; simpl; unfold t_empty;
  try apply empty_interval_le_all;
  try apply interval_le_refl;
  unfold list_assertion_to_map;
  rewrite merge_spec; auto.
Qed.

Definition join (s1 s2 : assertion) :=
  join_base s1 s2 Interval.join.

Theorem join_sound : forall (s1 s2 : assertion),
  le s1 (join s1 s2) /\ le s2 (join s1 s2).
Proof.
  intros. apply join_base_sound; auto.
  all: intros; pose (Interval.join_sound x y); tauto.
Qed.

Definition join_widen (s1 s2 : assertion) :=
  join_base s1 s2 Interval.widen.

Theorem join_widen_sound : forall (s1 s2 : assertion),
  le s1 (join_widen s1 s2) /\ le s2 (join_widen s1 s2).
Proof.
  intros. apply join_base_sound; auto.
  admit.
  all: intros; pose (Interval.widen_sound x y); tauto.
Admitted.





