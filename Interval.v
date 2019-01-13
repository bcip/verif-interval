Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.
Open Scope Z_scope.

Hint Rewrite Z.eqb_eq Z.ltb_lt Z.leb_le Z.gtb_lt Z.geb_le : arith.

Module Z.
Lemma gtb_nlt : forall n m, (Z.gtb n m = false) <-> ~ (Z.lt m n).
Proof.
  intros.
  split; intros.
  - intro. rewrite <- Z.gtb_lt in *. congruence.
  - destruct (n >? m) eqn:?.
    + rewrite Z.gtb_lt in *. tauto.
    + auto.
Qed.

Lemma geb_nle : forall n m, (Z.geb n m = false) <-> ~ (Z.le m n).
Proof.
  intros.
  split; intros.
  - intro. rewrite <- Z.geb_le in *. congruence.
  - destruct (n >=? m) eqn:?.
    + rewrite Z.geb_le in *. tauto.
    + auto.
Qed.
End Z.

Hint Rewrite Z.eqb_neq Z.ltb_nlt Z.leb_nle Z.gtb_nlt Z.geb_nle : arith.

Ltac arith :=
  repeat rewrite Bool.andb_true_iff in *;
  repeat rewrite Bool.orb_false_iff in *;
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

Definition top := IInterval None None.

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

Lemma include_inb : forall i x,
  include i x -> inb i x = true.
Proof.
  unfold include.
  destruct i as [[] []];
  unfold inb; intros.
  arith.
  all: (repeat rewrite Bool.andb_true_iff; split; try arith; auto).
Qed.

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
  repeat split; 
  unfold include in *; omega.
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
  rewrite Z.mul_comm;apply Z.mul_le_mono_neg_l; arith; omega.
  rewrite Z.mul_comm;apply Z.mul_le_mono_neg_r; arith; omega.
  assert (k*n = 0). apply Z_eq_mult; arith. omega.
  assert (k*n = 0). apply Z_eq_mult; arith. omega.
  rewrite Z.mul_comm;apply Z.mul_le_mono_pos_l;arith.
  rewrite Z.mul_comm;apply Z.mul_le_mono_neg_r;arith.
  assert (k*n = 0). apply Z_eq_mult; arith. omega.
  assert (k*n = 0). apply Z_eq_mult; arith. omega.
  rewrite Z.mul_comm;apply Z.mul_le_mono_pos_r;arith.
  rewrite Z.mul_comm;apply Z.mul_le_mono_neg_l; arith; omega.
  assert (k*n = 0). apply Z_eq_mult; arith. omega.
  assert (k*n = 0). apply Z_eq_mult; arith. omega.
Qed.

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

Lemma join_sound2 : forall (x y : interval) (n m p: Z),
  include x n ->
  include y m ->
  (Z.min n m) <= p <= (Z.max n m) ->
  include (join x y) (p).
Proof.
  intros.
  unfold include;destruct x as [[] []], y as [[] []];
  unfold join;
  erewrite !include_non_empty by eauto;
  split;simpl; auto; unfold include in *.
  assert ((Z.min z z1) <= (Z.min n m)).
  apply Z.min_le_compat; omega. omega.
  assert ((Z.max n m) <= (Z.max z0 z2)).
  apply Z.max_le_compat; omega. omega.
  assert ((Z.min z z1) <= (Z.min n m)).
  apply Z.min_le_compat; omega. omega.  
  assert ((Z.max n m) <= (Z.max z0 z1)).
  apply Z.max_le_compat; omega. omega.
  assert ((Z.min z z0) <= (Z.min n m)).
  apply Z.min_le_compat; omega. omega.
  assert ((Z.min z z0) <= (Z.min n m)).
  apply Z.min_le_compat; omega. omega.
  assert ((Z.max n m) <= (Z.max z z1)).
  apply Z.max_le_compat; omega. omega.
  assert ((Z.max n m) <= (Z.max z z0)).
  apply Z.max_le_compat; omega. omega.
Qed.

Lemma join_sound' : forall (x y : interval) (n m : Z),
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
  simpl; auto; unfold include in *; repeat split.
  assert (Z.min z z1 <= z).
  apply Z.le_min_l.
  omega.
  assert (z0 <= Z.max z0 z2).
  apply Z.le_max_l.
  omega.
  assert (Z.min z z1 <= z).
  apply Z.le_min_l.
  omega.
  assert (z0 <= Z.max z0 z1).
  apply Z.le_max_l.
  omega.
  assert (Z.min z z0 <= z).
  apply Z.le_min_l.
  omega.
  assert (Z.min z z0 <= z).
  apply Z.le_min_l.
  omega.
  assert (z <= Z.max z z1).
  apply Z.le_max_l.
  omega.
  assert (z <= Z.max z z0).
  apply Z.le_max_l.
  omega.
  assert (Z.min z z1 <= z1).
  apply Z.le_min_r.
  omega.
  assert (z2 <= Z.max z0 z2).
  apply Z.le_max_r.
  omega.
  assert (Z.min z z1 <= z1).
  apply Z.le_min_r.
  omega.
  assert (z1 <= Z.max z0 z1).
  apply Z.le_max_r.
  omega.
  assert (Z.min z z0 <= z0).
  try apply Z.le_min_r.
  try omega.
  assert (Z.min z z0 <= z0).
  apply Z.le_min_r.
  omega.
  assert (z1 <= Z.max z z1).
  apply Z.le_max_r.
  omega.
  assert (z0 <= Z.max z z0).
  apply Z.le_max_r.
  omega.
Qed.

Lemma join_sound : forall (x y : interval),
  le x (join x y) /\ le y (join x y).
Proof.
  intros; split; do 2 intro.
Admitted.

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
  unfold include;
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



Lemma is_nonnegb_sound : forall (x: interval) (n : Z),
  include x n ->
  is_nonnegb x = true ->
  n >= 0.
Proof.
  unfold include;unfold is_nonnegb;
  destruct x as [[] []];intros. 
  all: try arith.
  all: discriminate.
Qed.


Definition is_nonposb (x: interval) : bool :=
match x with
| IInterval xlo xhi =>
  match xhi with
  | None => false
  | Some a => Z.leb a 0
  end
end.


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
  all: discriminate.
Qed.

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

Lemma mul_sound : forall (x y : interval) (n m : Z),
  include x n ->
  include y m ->
  include (mul x y) (n * m).
Proof.
  pose mul_const_sound.
  pose join_sound2.
  intros.
  unfold mul; destruct x as [[] []], y as [[] []];
  erewrite !include_non_empty by eauto; simpl.
  assert (include (mul_const z (IInterval (Some z1) (Some z2))) (z * m)).
  assert (include (IInterval (Some z1) (Some z2)) m).
  unfold include in *; split; omega.
  auto.
  assert (include (mul_const z0 (IInterval (Some z1) (Some z2))) (z0 * m)).
  assert (include (IInterval (Some z1) (Some z2)) m).
  unfold include in *; split; omega.
  auto.
  assert ((Z.min (z * m) (z0 * m)) <= n*m <=(Z.max (z * m) (z0 * m))).

Admitted.
  
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


Definition widen (x y : interval) : interval.
Admitted.

Lemma widen_sound : forall x y : interval,
  le x (widen x y) /\ le y (widen x y).
Admitted.

(*TODO*)
Lemma leb_le : forall x y : interval,
  leb x y = true <-> le x y.
Proof.
intros.
split; destruct x as [[] []], y as [[] []];
unfold leb; unfold le; unfold include; unfold emptyb.
destruct (z0 <? z) eqn:?, (z2 <? z1) eqn:?, (z >=? z1) eqn:?, (z0 <=? z2) eqn:?;
intros; try discriminate; try arith. 

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

Definition default_interval : interval := IInterval (Some 0) (Some 0).

Definition empty_interval : interval := IInterval (Some 1) (Some 0).

Lemma empty_interval_le_all : forall (x : interval),
  Interval.le empty_interval x.
Admitted.

Lemma interval_le_refl : forall (x : interval),
  Interval.le x x.
Admitted.



