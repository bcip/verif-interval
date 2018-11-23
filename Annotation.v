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
 * while(...){
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
  | AWhile : bexp -> annotation -> assertion -> annotation'.

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
  | AWhile b1 A _ => CWhile b1 (get_com A)
  end.


























