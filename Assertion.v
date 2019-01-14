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

(*
Fixpoint merge_option_aux_l (l s : list_map) (f : A -> A -> option A) : option list_map :=
  match l with
    | nil => Some nil
    | (hd1, hd2) :: tl =>
      match f hd2 (list_to_map s hd1) with
      | None => None
      | Some new_hd2 =>
        match merge_option_aux_l tl s f with
        | None => None
        | Some res =>
          Some ((hd1, new_hd2) :: res)
        end
      end
    end.

Fixpoint merge_option_aux_s (l s : list_map) (f : A -> A -> option A) (new_l : option list_map): option list_map :=
    match s with
    | nil => new_l
    | (hd1, hd2) :: tl =>
      if has_key l hd1
      then merge_option_aux_s l tl f new_l
      else
        match f default hd2 with
        | None => None
        | Some new_hd2 =>
          match merge_option_aux_s l tl f new_l with
          | None => None
          | Some res =>
            Some ((hd1, new_hd2) :: res)
          end
        end
    end.

Definition merge_option (l s : list_map) (f : A -> A -> option A) : option list_map :=
  merge_option_aux_s l s f (merge_option_aux_l l s f).

Theorem merge_option_spec : forall (l s : list_map) (f : A -> A -> option A),
  f default default = Some default ->
  (exists (x : id), f (list_to_map l x) (list_to_map s x) = None) /\ list_to_map (merge l s f) = None
  \/
  forall (x : id), f (list_to_map l x) (list_to_map s x) <> None) /\ list_to_map (merge l s f) = None
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
Qed. *)

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

Lemma assertion_in_assertion_trans : forall (s s' s'' : assertion),
  s |== s' ->
  s' |== s'' ->
  s |== s''.
Proof.
  unfold assertion_in_assertion. intros. auto.
Qed.

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

Lemma leb_le : forall s1 s2,
  leb s1 s2 = true ->
  forall x,
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
  intros. unfold le.
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
  all: intros; pose (Interval.widen_sound x y); tauto.
Qed.

Fixpoint has_empty (l s : list_map interval) : bool :=
  match l with
  | nil => false
  | (hd1, hd2) :: tl => emptyb hd2 && negb (has_key _ s hd1) || has_empty tl ((hd1, hd2) :: s)
  end.

Definition rectify_empty (s : assertion) : assertion :=
  match s with
  | None => None
  | Some l => if has_empty l nil then None else s
  end.

Lemma has_empty_exists_empty : forall (l s : list_map interval),
  has_empty l s = true ->
  exists (x : id),
  (forall (n : Z), ~include (assertion_to_map (Some l) x) n) /\
  has_key _ s x = false.
Proof.
  intros l. induction l; intros.
  - inversion H.
  - destruct a as [hd1 hd2]. simpl in H.
    destruct (emptyb hd2 && negb (has_key interval s hd1)) eqn:?.
    + destruct (emptyb hd2) eqn:?;
      destruct (has_key interval s hd1) eqn:?; simpl in *; try congruence.
      exists hd1. split; auto.
      intros. unfold t_update; rewrite <- beq_id_refl. intro.
      assert (emptyb hd2 = false) by (eapply include_non_empty; eauto).
      congruence.
    + apply orb_prop in H. destruct H; try discriminate.
      specialize (IHl _ H).
      destruct IHl as [x IHl]. exists x.
      simpl in IHl. destruct IHl. destruct (beq_id hd1 x) eqn:?; try congruence.
      split; auto.
      intros. simpl. unfold t_update. rewrite Heqb0. auto.
Qed.

Lemma rectify_empty_sound : forall (s : assertion),
  s |== (rectify_empty s).
Proof.
  intro;
  destruct s as [l | ]; simpl; try destruct (has_empty l []) eqn:H;
  try solve [apply le_assertion_in_assertion;
    unfold le;
    simpl; intros; unfold t_empty;
    try rewrite H;
    try apply interval_le_refl;
    try apply empty_interval_le_all].
  pose (has_empty_exists_empty _ _ H) as H0.
  destruct H0 as [x []].
  intros st Hst.
  specialize (Hst x). exfalso. eapply H0. eauto.
Qed.

Definition meet (s1 s2 : assertion) : assertion :=
  match s1, s2 with
  | Some l1, Some l2 =>
    rectify_empty (Some (merge _ default_interval l1 l2 Interval.meet))
  | _, _ => None (* at least a None *)
  end.

Lemma bottom_implies_all : forall (s : assertion),
  None |== s.
Proof.
  intros. apply le_assertion_in_assertion. unfold le.
  intros. simpl. unfold t_empty. eapply empty_interval_le_all.
Qed.

Lemma merge_meet_sound : forall (l1 l2 : list_map interval),
  forall (st : state),
  st |= (Some l1) ->
  st |= (Some l2) ->
  st |= (Some (merge _ default_interval l1 l2 Interval.meet)).
Proof.
  intros. unfold state_in_assertion. simpl.
  unfold list_assertion_to_map. intro x. rewrite merge_spec by auto.
  apply meet_sound.
  - apply H.
  - apply H0.
Qed.

Theorem meet_sound : forall (s1 s2 : assertion),
  forall (st : state),
  st |= s1 ->
  st |= s2 ->
  st |= (meet s1 s2).
Proof.
  intros.
  destruct s1 as [l1 | ]; destruct s2 as [l2 | ];
  try (intro; specialize (H x); specialize (H0 x); simpl in *; omega).
  unfold meet.
  apply rectify_empty_sound, merge_meet_sound; auto.
Qed.

Definition assign (s : assertion) (x : id) (r : interval) : assertion :=
  if emptyb r
  then None
  else
    match s with
    | None => None
    | Some l => Some (update _ l x r)
    end.

Theorem assign_sound : forall (s : assertion) (x : id) (r : interval) (st : state) (n : Z),
  st |= s ->
  include r n ->
  t_update st x n |= assign s x r.
Proof.
  intros. intro y.
  unfold assign.
  destruct (emptyb r) eqn:?.
  - (* emptyb r = true *)
    pose (include_non_empty r n ltac:(auto)). congruence.
  - (* emptyb r = false *)
    destruct s; simpl.
    + (* s = Some l *)
      unfold list_assertion_to_map. rewrite update_spec.
      unfold t_update. destruct (beq_id x y).
      * auto.
      * apply H.
    + (* s = None *)
      specialize (H x). simpl in H. omega.
Qed.

Lemma assign_sound2 : forall (s : assertion) (x : id) (r : interval) (st : state) (n : Z),
  st |= s ->
  include r n ->
  st x = n ->
  st |= assign s x r.
Proof.
  intros. intro y.
  unfold assign.
  destruct (emptyb r) eqn:?.
  - (* emptyb r = true *)
    pose (include_non_empty r n ltac:(auto)). congruence.
  - (* emptyb r = false *)
    destruct s; simpl.
    + (* s = Some l *)
      unfold list_assertion_to_map. rewrite update_spec.
      unfold t_update. destruct (beq_id x y) eqn:?.
      * rewrite beq_id_true_iff in *. subst y. congruence.
      * apply H.
    + (* s = None *)
      specialize (H x). simpl in H. omega.
Qed.

Definition assign_option (s : assertion) (x : option id) (r : interval) : assertion :=
  if emptyb r then None else
  match x with
  | None => s
  | Some x => assign s x r
  end.

Definition mapsto_option (st : state) (x : option id) (n : Z) : Prop :=
  match x with
  | None => True
  | Some x => st x = n
  end.

Lemma assign_option_sound : forall (s : assertion) (x : option id) (r : interval) (st : state) (n : Z),
  st |= s ->
  mapsto_option st x n ->
  include r n ->
  st |= assign_option s x r.
Proof.
  intros. assert (emptyb r = false). {
    eapply include_non_empty; eauto.
  }
  destruct x; simpl in *; unfold assign_option; rewrite H2; auto.
  eapply assign_sound2; eauto.
Qed.

Definition eq_cond (s : assertion) (x y : option id) (r1 r2 : interval) (ans : bool) : assertion :=
  let new_r1 := Interval.eq_cond1 r1 r2 ans in
  let new_r2 := Interval.eq_cond2 r1 r2 ans in
  assign_option (assign_option s y new_r2) x new_r1.

Lemma eq_cond_sound : forall (s : assertion) (x y : option id) (r1 r2 : interval) (ans : bool) (st : state) (n m : Z),
  st |= s ->
  mapsto_option st x n ->
  mapsto_option st y m ->
  include r1 n ->
  include r2 m ->
  n =? m = ans ->
  st |= eq_cond s x y r1 r2 ans.
Proof.
  intros.
  eapply assign_option_sound; eauto.
  - eapply assign_option_sound; eauto.
    eapply eq_cond2_sound; eauto.
  - eapply eq_cond1_sound; eauto.
Qed.

Definition le_cond (s : assertion) (x y : option id) (r1 r2 : interval) (ans : bool) : assertion :=
  let new_r1 := Interval.le_cond1 r1 r2 ans in
  let new_r2 := Interval.le_cond2 r1 r2 ans in
  assign_option (assign_option s y new_r2) x new_r1.

Lemma le_cond_sound : forall (s : assertion) (x y : option id) (r1 r2 : interval) (ans : bool) (st : state) (n m : Z),
  st |= s ->
  mapsto_option st x n ->
  mapsto_option st y m ->
  include r1 n ->
  include r2 m ->
  n <=? m = ans ->
  st |= le_cond s x y r1 r2 ans.
Proof.
  intros.
  eapply assign_option_sound; eauto.
  - eapply assign_option_sound; eauto.
    eapply le_cond2_sound; eauto.
  - eapply le_cond1_sound; eauto.
Qed.

(*
Definition le_cond (s : assertion) (x : id) (y : interval) : assertion :=
  assign s x (Interval.le_cond (assertion_to_map s x) y).

Lemma le_cond_sound : forall (s : assertion) (x : id) (y : interval) (st : state) (n : Z),
  include y n ->
  st |= s ->
  st x <=? n = true ->
  st |= le_cond s x y.
Proof.
  intros. apply assign_sound2 with (n := st x); auto.
  apply Interval.le_cond_sound with n; auto. arith.
Qed.

Definition ge_cond (s : assertion) (x : id) (y : interval) : assertion :=
  assign s x (Interval.ge_cond (assertion_to_map s x) y).

Lemma ge_cond_sound : forall (s : assertion) (x : id) (y : interval) (st : state) (n : Z),
  include y n ->
  st |= s ->
  n <=? st x = true ->
  st |= ge_cond s x y.
Proof.
  intros. apply assign_sound2 with (n := st x); auto.
  apply Interval.ge_cond_sound with n; auto. arith.
Qed.
*)


