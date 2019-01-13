Require Import Maps.
Require Import Program.
Require Import Interval.
Require Import Assertion.
Require Import Annotation.
Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.
Open Scope Z_scope.

(* In argument initial, only precondition and program inside
  effect result (expecting other assertions are not greater
  than assertions in the same positions in result. These
  assertions in middle are expected to provide results from
  previous iterations, which reduce repeated work to guarantee
  algorithm complexity. *)

Ltac interval_analysis_solver initial :=
  let solver initial :=
    let initial := eval compute in initial in
    let solver' s initial' :=
      let initial' := eval compute in initial' in
      match initial' with
      | ASkip ?s' => idtac (* TODO *)
      | AAss ?x ?a1 ?s' => idtac (* TODO *)
      | ASeq ?A1 ?A2 => idtac (* TODO *)
      | AIf ?b1 ?A1 ?A2 ?s' => idtac (* TODO *)
      | AWhile ?b1 ?inv ?A ?s' => idtac (* TODO *)
      end
    in
    match initial with
    APre ?s ?initial' =>
      refine (SVPre s initial' ltac:(solver' s initial'))
    end
  in
  solver initial.

Fixpoint initial_annotation' (c : com) : annotation' :=
  match c with
  | CSkip => ASkip bottom
  | CAss x a1 => AAss x a1 bottom
  | CSeq c1 c2 => ASeq (initial_annotation' c1) (initial_annotation' c2)
  | CIf b1 c1 c2 => AIf b1 (APre bottom (initial_annotation' c1)) (APre bottom (initial_annotation' c2)) bottom
  | CWhile b1 c => AWhile b1 bottom (APre None (initial_annotation' c)) bottom
  end.

Definition initial_annotation (s : assertion) (c : com) : annotation :=
  APre s (initial_annotation' c).

Ltac interval_analysis initial :=
  refine (step_valid_valid _ ltac:(interval_analysis_solver initial)).

Ltac interval_analysis0 :=
  interval_analysis default.


