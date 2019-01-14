Require Import Maps.
Require Import Program.
Require Import Interval.
Require Import Assertion.
Require Import Annotation.
Require Import Forward.
Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.
Open Scope Z_scope.


Require Import Coq.Program.Tactics.

(* In argument initial, only precondition and program inside
  effect result (expecting other assertions are not greater
  than assertions in the same positions in result. These
  assertions in middle are expected to provide results from
  previous iterations, which reduce repeated work to guarantee
  algorithm complexity. *)



(* Lemma forward_ass (s x a1 s' : assertion) : step_valid' s (AAss x a1 (join  s')).
  apply SVSkip. apply le_assertion_in_assertion.
  eapply proj1. apply join_sound.
Qed. *)

Ltac solver' initial' :=
  show_goal;
  let s :=
    match goal with
    | |- step_valid' ?s _ => eval compute in s
    end
  in
  let initial' := eval compute in initial' in
  lazymatch initial' with
  | ASkip ?s' =>
    let res := eval compute in (forward_skip s s') in
    refine (forward_skip_valid s s' res _); reflexivity
  | AAss ?x ?a1 ?s' =>
    let res := eval compute in (forward_ass s x a1 s') in
      refine (forward_ass_valid s x a1 s' res _); reflexivity (* TODO *)
  | ASeq ?A1 ?A2 => refine (SVSeq s _ _ _ _); [solver' A1 | solver' A2]
  | AIf ?b1 ?A1 ?A2 ?s' => idtac (* TODO *)
  | AWhile ?b1 ?inv ?A ?s' => idtac (* TODO *)
  end.

Ltac solver initial :=
  let initial := eval compute in initial in
  match initial with
  APre ?s ?initial' =>
    refine (SVPre s _ _); solver' initial'
  end.

Ltac interval_analysis_solver initial :=
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
  refine (step_valid_valid _ _);
  interval_analysis_solver initial.

Ltac interval_analysis0 prog :=
  interval_analysis (initial_annotation default prog).


Definition subtract_slowly_body : com :=
  Y ::= AMinus (AId Y) (ANum 1) ;;
  X ::= AMinus (AId X) (ANum 1).

Definition test := ltac:(interval_analysis0 subtract_slowly_body).
(* 
test

Goal True.
pose test. simpl in v.

Definition test : step_valid _ :=
  ltac:(interval_analysis_solver (APre (Some nil) (AAss (Id "X") (APlus (AId (Id "X")) (ANum 2)) None))).

Definition test := ltac:(interval_analysis0 plus2).





plus2
Search com.
*)
