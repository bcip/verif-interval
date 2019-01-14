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

Definition update_precondition (A : annotation) (s : assertion) :=
  match A with
  | APre _ A' => APre s A'
  end.

Ltac solver' initial' :=
  let s :=
    match goal with
    | |- step_valid' ?s _ => eval compute in s
    end
  in
  let initial' := eval compute in initial' in
  lazymatch initial' with
  | ASkip ?s' =>
    refine (forward_skip_valid s s' _ _); compute; reflexivity
  | AAss ?x ?a1 ?s' =>
      refine (forward_ass_valid s x a1 s' _ _); compute; reflexivity
  | ASeq ?A1 ?A2 => refine (SVSeq s _ _ _ _); [solver' A1 | solver' A2]
  | AIf ?b ?A1 ?A2 ?s' =>
    let new_A1 := eval compute in (update_precondition A1 (forward_cond_true s b)) in
    let new_A2 := eval compute in (update_precondition A2 (forward_cond_false s b)) in
    refine (forward_if s b _ _ s' _ _ _ _ _ _); show_goal; [solver' A1 | solver' A2]
  | AWhile ?b ?inv ?A ?s' => idtac (* TODO *)
  end.

Ltac solver initial :=
  let solver' initial' :=
    let s :=
      match goal with
      | |- step_valid' ?s _ => eval compute in s
      end
    in
    let initial' := eval compute in initial' in
    lazymatch initial' with
    | ASkip ?s' =>
      refine (forward_skip_valid s s' _ _); compute; reflexivity
    | AAss ?x ?a1 ?s' =>
        refine (forward_ass_valid s x a1 s' _ _); compute; reflexivity
    | ASeq ?A1 ?A2 => refine (SVSeq s _ _ _ _); [solver' A1 | solver' A2]
    | AIf ?b ?A1 ?A2 ?s' =>
      let new_A1 := constr:(update_precondition A1 (forward_cond_true s b)) in
      let new_A2 := constr:(update_precondition A2 (forward_cond_false s b)) in
      refine (forward_if s b _ _ s' _ _ _ _ _ _); show_goal;
        [ solver new_A1
        | solver new_A2
        | apply forward_cond_true_valid; reflexivity
        | apply forward_cond_false_valid; reflexivity
        | compute; reflexivity ]; fail
    | AWhile ?b ?inv ?A ?s' => idtac (* TODO *)
    end
  in
  let initial := eval compute in initial in
  lazymatch initial with
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
  | CIf b c1 c2 => AIf b (APre bottom (initial_annotation' c1)) (APre bottom (initial_annotation' c2)) bottom
  | CWhile b c => AWhile b bottom (APre None (initial_annotation' c)) bottom
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

Definition sample_prog : com :=
  X ::= ANum 2;;
     IFB BLe (AId X) (ANum 1)
       THEN Y ::= (ANum 3)
       ELSE W ::= (ANum 4)
     FI.

Definition sample_prog2 : com :=
     IFB BLe (AId X) (ANum 1)
       THEN Y ::= (ANum 3)
       ELSE W ::= (ANum 4)
     FI.

Definition simple_if : com :=
     IFB BLe (AId X) (ANum 1)
       THEN SKIP
       ELSE SKIP
     FI.

(* Definition test := ltac:(interval_analysis0 sample_prog). *)

(* Check test. *)
