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

Open Scope Z_scope.

Definition assertion : Type := total_map interval.

Definition default_interval : interval := IInterval (Some 0) (Some 0).

Definition empty : assertion := t_empty default_interval.

Definition state_in_range (st : state) (s : assertion) : Prop :=
  forall (x : id), include (s x) (st x).

(* annotation :=
 * (assertion)
 * code
 * (assertion)
 * code
 * (assertion)
 *
 * annotation' :=
 * code
 * (assertion)
 * code
 * (assertion)
 *
 * If diagram :
 * (assertion)
 * if(...){
 *   (assertion)
 *   code
 *   (assertion)
 * } else {
 *   (assertion)
 *   code
 *   (assertion)
 * }
 * (assertion)
 *
 * While diagram :
 * (assertion)
 * while(...)
 * (invariant)
 * {
 *   (assertion)
 *   code
 *   (assertion)
 * }
 * (assertion)
 *)
 

Inductive annotation : Type :=
  | APre : assertion -> annotation' -> annotation
  with
  annotation' : Type :=
  | ASkip : assertion -> annotation'
  | AAss : id -> aexp -> assertion -> annotation'
  | ASeq : annotation' -> annotation' -> annotation'
  | AIf : bexp -> annotation -> annotation -> assertion -> annotation'
  | AWhile : bexp -> assertion -> annotation -> assertion -> annotation'.

Fixpoint get_com (A : annotation) : com :=
  match A with
  | APre _ A' => get_com' A'
  end
  with
  get_com' (A' : annotation') : com :=
  match A' with
  | ASkip _ => CSkip
  | AAss x a1 _ => CAss x a1
  | ASeq A1 A2 => CSeq (get_com' A1) (get_com' A2)
  | AIf b1 A1 A2 _ => CIf b1 (get_com A1) (get_com A2)
  | AWhile b1 _ A _ => CWhile b1 (get_com A)
  end.

Definition precondition (A : annotation) : assertion :=
  match A with
  | APre s _ => s
  end.

Fixpoint postcondition' (A' : annotation') : assertion :=
  match A' with
  | ASkip s => s
  | AAss _ _ s => s
  | ASeq _ A2 => postcondition' A2
  | AIf _ _ _ s => s
  | AWhile _ _ _ s => s
  end.

Definition postcondition (A : annotation) : assertion :=
  match A with
  | APre _ A' => postcondition' A'
  end.

Definition valid' (s : assertion) (A' : annotation') : Prop :=
  forall st st', get_com' A' / st \\ st' ->
  state_in_range st s ->
  state_in_range st' (postcondition' A').

Definition valid (A : annotation) : Prop :=
  match A with
  | APre s A' => valid' s A'
  end.

Inductive step_valid : annotation -> Prop :=
  | SVPre : forall s A', step_valid' s A' -> step_valid (APre s A')
  with
  step_valid' : assertion -> annotation' -> Prop :=
  | SVSkip : forall s s',
    (forall st, state_in_range st s -> state_in_range st s')
    -> step_valid' s (ASkip s')
  | SVAss : forall s x a s',
    (forall st, state_in_range st s -> state_in_range (t_update st x (aeval st a)) s')
    -> step_valid' s (AAss x a s')
  | SVSeq : forall s A1 A2,
    step_valid' s A1 ->
    step_valid' (postcondition' A1) A2 ->
    step_valid' s (ASeq A1 A2)
  | SVIf : forall s b A1 A2 s',
    (forall st, state_in_range st s -> beval st b = true -> state_in_range st (precondition A1)) ->
    (forall st, state_in_range st s -> beval st b = false -> state_in_range st (precondition A2)) ->
    step_valid A1 ->
    step_valid A2 ->
    (forall st, state_in_range st (postcondition A1) -> state_in_range st s') ->
    (forall st, state_in_range st (postcondition A2) -> state_in_range st s') ->
    step_valid' s (AIf b A1 A2 s')
  | SVWhile : forall s b inv A s',
    (forall st, state_in_range st s -> state_in_range st inv) ->
    (forall st, state_in_range st inv -> beval st b = true -> state_in_range st (precondition A)) ->
    (forall st, state_in_range st inv -> beval st b = false -> state_in_range st s') ->
    step_valid A ->
    (forall st, state_in_range st (postcondition A) -> state_in_range st inv) ->
    step_valid' s (AWhile b inv A s').

Scheme step_valid_ind_2 := Minimality for step_valid Sort Prop
  with step_valid'_ind_2 := Minimality for step_valid' Sort Prop.


Theorem step_valid_valid : forall (A : annotation),
  step_valid A -> valid A.
Proof.
  apply step_valid_ind_2 with (P0 := (fun s A' => valid' s A')); intros; auto; unfold valid';
    simpl postcondition'; simpl get_com'; intros;
    match goal with
    | H : _ / _ \\ _ |- _ => inversion H
    end;
    subst; eauto.
  - destruct A1. eauto.
  - destruct A2. eauto.
  - clear dependent st'0.
    assert (state_in_range st inv) by auto.
    clear dependent s.
    clear H9.
    remember (WHILE b DO get_com A END) as c.
    induction H5; inversion Heqc; subst.
    + auto.
    + apply IHceval2; auto. destruct A. eauto.
Qed.



















