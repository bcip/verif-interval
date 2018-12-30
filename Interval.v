Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.
Open Scope Z_scope.

Hint Rewrite Z.eqb_eq Z.ltb_lt Z.leb_le Z.gtb_lt Z.geb_le Z.eqb_neq: arith.

Ltac arith := 
  autorewrite with arith in *;
  omega.

Inductive interval : Type :=
  | IInterval : forall (lo hi : option Z), interval.

Definition include (i : interval) (x : Z) : Prop :=
  match i with
  | IInterval lo hi =>
    match lo with
    | Some y => y <= x
    | None => True
    end /\
    match hi with
    | Some z => x <= z
    | None => True
    end
  end.

Definition inb (i : interval) (x : Z) : bool :=
  match i with
  | IInterval lo hi =>
    let lob := match lo with
              | Some y => Z.leb y x
              | None => true
              end
    in
    let hib := match hi with
              | Some z => Z.leb x z
              | None => true
              end
    in
    andb lob hib
  end.

Definition emptyb (x : interval) : bool :=
  match x with
  | IInterval (Some y) (Some z) =>
    z <? y
  | _ => false
  end.

Definition bottom := IInterval (Some 1) (Some 0).

Definition add (x: interval) (y: interval) : interval :=
  if orb (emptyb x) (emptyb y) then bottom else
    match x, y with
    | IInterval xlo xhi, IInterval ylo yhi =>
      let lower := match (xlo, ylo) with
        | (Some a, Some b) => Some (a + b)
        | _ => None
      end
      in
      let upper := match xhi, yhi with
        | Some a, Some b => Some (a + b)
        | _, _ => None
      end
      in
      IInterval lower upper
    end.

Lemma include_non_empty : forall (x : interval) (n : Z),
  include x n ->
  emptyb x = false. 
Proof.
  unfold include. intros.
  destruct x as [[] []]; auto.
  simpl. rewrite Z.ltb_ge. omega.
Qed.

(* TODO *)
Lemma include_inb : forall i x,
  include i x -> inb i x = true.
Proof.
  unfold include.
  destruct i as [[] []];
  unfold inb; intros.
  
Lemma add_sound : forall (x y : interval) (n m : Z),
  include x n ->
  include y m ->
  include (add x y) (n + m).
Proof.
  intros.
  unfold include. intros.
  destruct x as [[] []], y as [[] []];
  unfold add; erewrite !include_non_empty by eauto;
  simpl; repeat split;
  unfold include in *; omega.
Qed.

Definition neg (x: interval) : interval :=
  if emptyb x then bottom else
    match x with
    | IInterval xlo xhi => 
      let upper := match xlo with
        | Some a => Some (- a)
        | None => None
        end
      in
      let lower := match xhi with 
        | Some a => Some (- a)
        | None => None
        end
      in
      IInterval lower upper
    end.
    
Lemma neg_sound : forall (x: interval) (n: Z),
  include x n ->
  include (neg x) (-n).
Proof.
  intros.
  unfold include.
  destruct x as [[] []];
  unfold neg; erewrite !include_non_empty by eauto;
  repeat split.
  all: (unfold include in *; omega).
Qed.

Definition mul_const (k: Z) (x: interval) : interval :=
  if emptyb x then bottom 
  else if k =? 0 then IInterval (Some 0) (Some 0)
  else match x with
    | IInterval xlo xhi => 
      if k >? 0 then
        let upper := match xhi with
          | Some a => Some (a * k)
          | None => None
          end
        in
        let lower := match xlo with
          | Some a => Some (a * k)
          | None => None
          end
        in
        IInterval lower upper
      else 
        let lower := match xhi with
          | Some a => Some (a * k)
          | None => None
          end
        in
        let upper := match xlo with
          | Some a => Some (a * k)
          | None => None
          end
        in
        IInterval lower upper
    end.

(*TODO*)

Lemma mul_const_sound : forall (x: interval) (n k : Z),
  include x n ->
  include (mul_const k x ) (k * n).
Proof.
  intros.
  unfold include. 
  unfold mul_const.
  destruct x as [[] []];
  erewrite !include_non_empty by eauto;
  unfold include in *;
  destruct (k =? 0) eqn:?;
  destruct (k >? 0) eqn:?;
  repeat split; try arith.
  assert (k*n = 0). apply Z_eq_mult; arith. omega.
  assert (k*n = 0). apply Z_eq_mult; arith. omega.
  rewrite Z.mul_comm;apply Z.mul_le_mono_pos_l;arith.
  rewrite Z.mul_comm;apply Z.mul_le_mono_pos_r;arith.
  rewrite Z.mul_comm.
  assert (k < 0). 
  
  Search (_< 0).
  

Definition join (x: interval) (y: interval) : interval :=
  if emptyb x then y
  else if emptyb y then x
  else match x,y with
    | IInterval xlo xhi, IInterval ylo yhi =>
      let lower := match xlo, ylo with
      | Some a, Some b => Some (Z.min a b)
      | _,_ => None
      end
      in
      let upper := match xhi, yhi with
      | Some a, Some b => Some (Z.max a b)
      | _,_ => None
      end
      in
      IInterval lower upper
    end.


Lemma join_sound : forall (x y : interval) (n m : Z),
  include x n ->
  include y m ->
  include (join x y) (n) /\ include (join x y) (m).
Proof.
  intros.
  split;
  unfold include;
  destruct x as [[] []], y as [[] []];
  unfold join;
  erewrite !include_non_empty by eauto;
  simpl; auto.
  unfold include in *.
  all : repeat split.
  assert (Z.min z z1 <= z).
  apply Z.le_min_l.
  omega.
  assert (z0 <= Z.max z0 z2).
  apply Z.le_max_l.
  omega.
  unfold include in *.
  assert (Z.min z z1 <= z).
  apply Z.le_min_l.
  omega.
  unfold include in *.
  assert (z0 <= Z.max z0 z1).
  apply Z.le_max_l.
  omega.
  unfold include in *.
  assert (Z.min z z0 <= z).
  apply Z.le_min_l.
  omega.
  unfold include in *.
  assert (Z.min z z0 <= z).
  apply Z.le_min_l.
  omega.
  unfold include in *.
  assert (z <= Z.max z z1).
  apply Z.le_max_l.
  omega.
  unfold include in *.
  assert (z <= Z.max z z0).
  apply Z.le_max_l.
  omega.
  unfold include in *.
  assert (Z.min z z1 <= z1).
  apply Z.le_min_r.
  omega.
  unfold include in *.
  assert (z2 <= Z.max z0 z2).
  apply Z.le_max_r.
  omega.
  unfold include in *.
  assert (Z.min z z1 <= z1).
  apply Z.le_min_r.
  omega.
  unfold include in *.
  assert (z1 <= Z.max z0 z1).
  apply Z.le_max_r.
  omega.
  unfold include in *.
  assert (Z.min z z0 <= z0).
  try apply Z.le_min_r.
  try omega.
  unfold include in *.
  assert (Z.min z z0 <= z0).
  apply Z.le_min_r.
  omega.
  unfold include in *.
  assert (z1 <= Z.max z z1).
  apply Z.le_max_r.
  omega.
  unfold include in *.
  assert (z0 <= Z.max z z0).
  apply Z.le_max_r.
  omega.
Qed.
  
Definition meet (x: interval) (y: interval) : interval :=
  if orb (emptyb x) (emptyb y) then bottom else
    match x,y with
    | IInterval xlo xhi, IInterval ylo yhi =>
      let lower := 
      match xlo, ylo with
      | Some a, None => Some a
      | None, Some a => Some a
      | Some a, Some b => Some (Z.max a b)
      | None, None => None
      end
      in
      let upper := 
      match xhi, yhi with
      | Some a, None => Some a
      | None, Some a => Some a
      | Some a, Some b => Some (Z.min a b)
      | None, None => None
      end
      in
      IInterval lower upper
    end.

Lemma meet_sound : forall (x y : interval) (n : Z),
  include x n ->
  include y n ->
  include (meet x y) (n).
Proof.
  intros.
  unfold include.
  destruct x as [[] []], y as [[] []];
  unfold meet;
  erewrite !include_non_empty by eauto;
  simpl; auto.
  unfold include in *.
  all: repeat split.
  all: try apply Z.max_lub; try apply Z.min_glb; try omega.
  all: (unfold include in *; omega).
Qed.

Definition is_nonnegb (x: interval) : bool :=
  match x with
  | IInterval xlo xhi =>
    match xlo with
    | None => false
    | Some a => Z.leb 0 a
    end
  end.

(* TODO *)

Lemma is_nonnegb_sound : forall (x: interval) (n : Z),
  include x n ->
  is_nonnegb x = true ->
  n >= 0.
Proof.
  unfold include.
  destruct x as [[] []];
  unfold is_nonnegb;
  intros. 
  all: try arith.


Definition is_nonposb (x: interval) : bool :=
match x with
| IInterval xlo xhi =>
  match xhi with
  | None => false
  | Some a => Z.leb a 0
  end
end.

(* TODO *)

Lemma is_nonposb_sound : forall (x: interval) (n : Z),
  include x n ->
  is_nonposb x = true ->
  n <= 0.
Proof.
  unfold include.
  destruct x as [[] []];
  unfold is_nonposb;
  intros. 
  all: try arith.
 
Definition top := IInterval None None.

Definition mul (x: interval) (y: interval) : interval :=
  if orb (emptyb x) (emptyb y) then bottom else
    match x,y with
    | IInterval xlo xhi, IInterval ylo yhi =>
      match xlo, xhi with
      | Some a, Some b => join (mul_const a y) (mul_const b y)
      | None, None => top
      | None, Some a => 
        if is_nonnegb y then
          match mul_const a y with
          | IInterval lo hi => IInterval None hi
          end
        else if is_nonposb y then
          match mul_const a y with
          | IInterval lo hi => IInterval lo None
          end
        else top
      | Some a, None =>
          if is_nonposb y then
          match mul_const a y with
          | IInterval lo hi => IInterval None hi
          end
        else if is_nonnegb y then
          match mul_const a y with
          | IInterval lo hi => IInterval lo None
          end
        else top
      end
    end.

(* TODO mul_sound *)

Definition elem (a: Z) (x: interval) : bool :=
  match x with
  | IInterval xlo xhi =>
    match xlo, xhi with
    | None, None => true
    | None, Some b => a <=? b
    | Some b, None => a >=? b
    | Some b, Some c => andb (a >=? b) (a <=? c)
    end
  end.
  
(* TODO inb =? elem *)

Definition div (x: interval) (y: interval) : interval :=
  if orb (emptyb x) (emptyb y) then bottom else
    match y with
    | IInterval ylo yhi =>
      match ylo, yhi with
      | Some a, Some b => 
        if elem 0 y then top
        else join (mul_const (1/a) x) (mul_const (1/b) x)
      | _,_ => top
      end
    end.

(* TODO div_sound *)

Definition abs (x: interval) : interval :=
  if emptyb x then bottom 
  else if is_nonnegb x then x
  else if is_nonposb x then neg x
  else match x with
    | IInterval xlo xhi =>
      let upper := 
      match xlo, xhi with
      | Some a, Some b => Some (Z.max (-a) b)
      | _,_ => None
      end
      in IInterval (Some 0) upper
    end.

(* TODO abs_sound *)

(* Compare whether interval x is contained by interval y *)
Definition leb (x: interval) (y: interval) : bool :=
  if emptyb x then true 
  else if emptyb y then false
  else
  match x,y with
    | IInterval xlo xhi, IInterval ylo yhi =>
      match xlo, ylo with
      | _, None =>
        match xhi, yhi with
        | _ , None => true
        | None, Some c => false
        | Some c, Some d => Z.leb c d
        end
      | None, Some a => false
      | Some a, Some b =>
        if Z.geb a b then 
        match xhi, yhi with
        | _ , None => true
        | None, Some c => false
        | Some c, Some d => Z.leb c d
        end
        else false
      end
   end.

Definition eqb (x y : interval) : bool :=
  andb (leb x y) (leb y x).
  
Definition geb (x y : interval) : bool :=
  leb y x.

Definition le (x y : interval) : Prop := 
  forall n, include x n -> include y n.

Definition ge (x y : interval) : Prop := 
  le y x.

Definition feq (x y : interval) : Prop := 
  le x y /\ le y x.

(*TODO*)
Lemma leb_le : forall x y : interval,
  leb x y = true <-> le x y.
Admitted.

Lemma eqb_feq : forall x y : interval,
  eqb x y = true <-> feq x y.
Admitted.

Axiom feq_sym : forall x y : interval,
  feq x y -> feq y x.

Lemma geb_ge : forall x y : interval,
  geb x y = true <-> ge x y.
Proof.
  intros.
  pose (leb_le y x).
  tauto.
Qed.

Lemma eq_dec (x y : interval) : (x = y) + (x <> y).
Proof.
  destruct x as [[xlo | ] [xhi | ]], y as [[ylo | ] [yhi | ]];
  try solve [right; inversion 1];
  try destruct (Z.eq_dec xlo ylo);
  try destruct (Z.eq_dec xhi yhi);
  try solve [left; subst; auto];
  solve [right; inversion 1; congruence].
Qed.





