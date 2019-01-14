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

Lemma minus_sound : forall (x y : interval) (n m : Z),
  include x n ->
  include y m ->
  include (add x (neg y)) (n - m).
Proof.
intros.
assert (n - m = n + (- m)) by omega.
assert (include (neg y) (- m)) by (apply neg_sound;auto).
apply add_sound;auto.
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

(* TODO *)
Lemma join_sound : forall (x y : interval),
  le x (join x y) /\ le y (join x y).
Proof.
  intros; split; do 2 intro;
  unfold include;
  destruct x as [[] []], y as [[] []];
  unfold join;
  try erewrite !include_non_empty by eauto;
  unfold emptyb;
  unfold include in *.
  
  destruct (z2 <? z1);auto;split; auto.
  assert (Z.min z z1 <= Z.min n z1).
  apply Z.min_le_compat_r;omega.
  assert (Z.min n z1 <= n) by apply Z.le_min_l.
  omega.
  assert (Z.max n z2 <= Z.max z0 z2).
  apply Z.max_le_compat_r;omega.
  assert (n <= Z.max n z2) by apply Z.le_max_l.
  omega.
  1-3: split;auto.
  assert (Z.min z z1 <= Z.min n z1).
  apply Z.min_le_compat_r;omega.
  assert (Z.min n z1 <= n) by apply Z.le_min_l.
  omega.
  assert (Z.max n z1 <= Z.max z0 z1).
  apply Z.max_le_compat_r;omega.
  assert (n <= Z.max n z1) by apply Z.le_max_l.
  omega.
  
  destruct (z1 <? z0);auto.
  1-4:split;auto.
  assert (Z.min z z0 <= Z.min n z0).
  apply Z.min_le_compat_r;omega.
  assert (Z.min n z0 <= n) by apply Z.le_min_l.
  omega.
  assert (Z.min z z0 <= Z.min n z0).
  apply Z.min_le_compat_r;omega.
  assert (Z.min n z0 <= n) by apply Z.le_min_l.
  omega.
  
  destruct (z1 <? z0);auto.
  1-4:split;auto.
  assert (Z.max n z1 <= Z.max z z1).
  apply Z.max_le_compat_r;omega.
  assert (n <= Z.max n z1) by apply Z.le_max_l.
  omega.
  assert (Z.max n z0 <= Z.max z z0).
  apply Z.max_le_compat_r;omega.
  assert (n <= Z.max n z0) by apply Z.le_max_l.
  omega.
  
  destruct (z0 <? z);auto.
  1-3:split;auto.

  
  1-4: destruct (z0 <? z);auto.
  assert (z2 <? z1 = false) by arith.
  erewrite H0 by eauto.
  split.
  assert (Z.min z z1 <= Z.min z n).
  apply Z.min_le_compat_l;omega.
  assert (Z.min z n <= n) by apply Z.le_min_r.
  omega.
  assert (Z.max z0 n <= Z.max z0 z2).
  apply Z.max_le_compat_l;omega.
  assert (n <= Z.max z0 n) by apply Z.le_max_r.
  omega.
  1-2: split;auto.
  assert (Z.min z z1 <= Z.min z n).
  apply Z.min_le_compat_l;omega.
  assert (Z.min z n <= n) by apply Z.le_min_r.
  omega.
  assert (Z.max z0 n <= Z.max z0 z1).
  apply Z.max_le_compat_l;omega.
  assert (n <= Z.max z0 n) by apply Z.le_max_r.
  omega.
  
  1,5:assert (z1 <? z0 = false) by arith.
  1-2:erewrite H0 by eauto.
  1-8: split;auto.
  assert (Z.min z z0 <= Z.min z n).
  apply Z.min_le_compat_l;omega.
  assert (Z.min z n <= n) by apply Z.le_min_r.
  omega.
  assert (Z.max z n <= Z.max z z1).
  apply Z.max_le_compat_l;omega.
  assert (n <= Z.max z n) by apply Z.le_max_r.
  omega.
  assert (Z.min z z0 <= Z.min z n).
  apply Z.min_le_compat_l;omega.
  assert (Z.min z n <= n) by apply Z.le_min_r.
  omega.
  assert (Z.max z n <= Z.max z z0).
  apply Z.max_le_compat_l;omega.
  assert (n <= Z.max z n) by apply Z.le_max_r.
  omega.
  
  assert (z0 <? z = false) by arith.
  erewrite H0 by eauto.
  all: split;auto.
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

(* given a <= b, and a in x, b in y, update the interval of a*)
Definition le_cond (x y: interval): interval :=
  if (emptyb y) then x else
    match y with
    | IInterval ylo yhi => meet x (IInterval None yhi)
    end.

Lemma le_cond_sound : forall (x y: interval) (n m:Z),
  include x n ->
  include y m ->
  n <= m ->
  include (le_cond x y) n.
Proof.
intros; unfold le_cond; erewrite !include_non_empty by eauto.
destruct y as [[] []];apply meet_sound;auto.
all: unfold include in *;split;auto;omega.
Qed.

Definition ge_cond (x y: interval): interval :=
  if (emptyb y) then x else
    match y with
    | IInterval ylo yhi => meet x (IInterval ylo None)
    end.

Lemma ge_cond_sound : forall (x y: interval) (n m:Z),
  include x n ->
  include y m ->
  n >= m ->
  include (ge_cond x y) n.
Proof.
intros; unfold ge_cond; erewrite !include_non_empty by eauto.
destruct y as [[] []];apply meet_sound;auto.
all: unfold include in *;split;auto;omega.
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
  erewrite !include_non_empty by eauto; simpl;unfold include in H, H0.
  
  assert (include (mul_const z (IInterval (Some z1) (Some z2))) (z * m));
  assert (include (IInterval (Some z1) (Some z2)) m) by 
  (unfold include in *; split; omega); auto.
  assert (include (mul_const z0 (IInterval (Some z1) (Some z2))) (z0 * m));
  assert (include (IInterval (Some z1) (Some z2)) m) by
  (unfold include in *; split; omega);auto.
  
  assert ((Z.min (z * m) (z0 * m)) <= n*m <=(Z.max (z * m) (z0 * m))).
  destruct (m >? 0) eqn:?.
  assert ( (z * m) <= (n* m) <= (z0 * m));split.
  1-2: apply Zmult_lt_0_le_compat_r; arith. 
  assert (Z.min (n * m) (z0 * m) <= n * m) by apply Z.le_min_l.
  assert (Z.min (z * m) (z0 * m) <= Z.min (n * m) (z0 * m)).
  apply Z.min_le_compat_r;arith.
  arith.
  assert (n * m <= Z.max (z * m) (n * m)) by apply Z.le_max_r.
  assert (Z.max (z * m) (n * m) <= Z.max (z * m) (z0 * m)).
  apply Z.max_le_compat_l;arith.
  arith.
  assert ( (z0 * m) <= (n* m) <= (z * m));split.
  1-2: apply Z.mul_le_mono_nonpos_r; arith.
  assert (Z.min (z * m) (n * m) <= n * m) by apply Z.le_min_r.
  assert (Z.min (z * m) (z0 * m) <= Z.min (z * m) (n * m) ).
  apply Z.min_le_compat_l;arith.
  arith.
  assert (n * m <= Z.max (n * m) (z0 * m)) by apply Z.le_max_l.
  assert (Z.max (n * m) (z0 * m) <= Z.max (z * m) (z0 * m)).
  apply Z.max_le_compat_r; arith.
  arith.
  eauto.
  
  assert (include (mul_const z0 (IInterval (Some z1) None)) (z0 * m));
  assert (include (IInterval (Some z1) None) m) by 
  (unfold include; auto);auto.
  assert (include (mul_const z (IInterval (Some z1) None)) (z * m));
  assert (include (IInterval (Some z1) None) m) by
  (unfold include; auto);auto.
  
  assert ((Z.min (z * m) (z0 * m)) <= n*m <=(Z.max (z * m) (z0 * m))).
  destruct (m >? 0) eqn:?.
  assert ( (z * m) <= (n* m) <= (z0 * m));split.
  1-2: apply Zmult_lt_0_le_compat_r; arith. 
  assert (Z.min (n * m) (z0 * m) <= n * m) by apply Z.le_min_l.
  assert (Z.min (z * m) (z0 * m) <= Z.min (n * m) (z0 * m)).
  apply Z.min_le_compat_r;arith.
  arith.
  assert (n * m <= Z.max (z * m) (n * m)) by apply Z.le_max_r.
  assert (Z.max (z * m) (n * m) <= Z.max (z * m) (z0 * m)).
  apply Z.max_le_compat_l;arith.
  arith.
  assert ( (z0 * m) <= (n* m) <= (z * m));split.
  1-2: apply Z.mul_le_mono_nonpos_r; arith.
  assert (Z.min (z * m) (n * m) <= n * m) by apply Z.le_min_r.
  assert (Z.min (z * m) (z0 * m) <= Z.min (z * m) (n * m) ).
  apply Z.min_le_compat_l;arith.
  arith.
  assert (n * m <= Z.max (n * m) (z0 * m)) by apply Z.le_max_l.
  assert (Z.max (n * m) (z0 * m) <= Z.max (z * m) (z0 * m)).
  apply Z.max_le_compat_r; arith.
  arith.
  eauto.
  
  assert (include (mul_const z (IInterval None (Some z1))) (z * m));
  assert (include (IInterval None (Some z1)) m) by 
  (unfold include; auto);auto.
  assert (include (mul_const z0 (IInterval None (Some z1))) (z0 * m));
  assert (include (IInterval None (Some z1)) m) by
  (unfold include; auto);auto.

  assert ((Z.min (z * m) (z0 * m)) <= n*m <=(Z.max (z * m) (z0 * m))).
  destruct (m >? 0) eqn:?.
  assert ( (z * m) <= (n* m) <= (z0 * m));split.
  1-2: apply Zmult_lt_0_le_compat_r; arith. 
  assert (Z.min (n * m) (z0 * m) <= n * m) by apply Z.le_min_l.
  assert (Z.min (z * m) (z0 * m) <= Z.min (n * m) (z0 * m)).
  apply Z.min_le_compat_r;arith.
  arith.
  assert (n * m <= Z.max (z * m) (n * m)) by apply Z.le_max_r.
  assert (Z.max (z * m) (n * m) <= Z.max (z * m) (z0 * m)).
  apply Z.max_le_compat_l;arith.
  arith.
  assert ( (z0 * m) <= (n* m) <= (z * m));split.
  1-2: apply Z.mul_le_mono_nonpos_r; arith.
  assert (Z.min (z * m) (n * m) <= n * m) by apply Z.le_min_r.
  assert (Z.min (z * m) (z0 * m) <= Z.min (z * m) (n * m) ).
  apply Z.min_le_compat_l;arith.
  arith.
  assert (n * m <= Z.max (n * m) (z0 * m)) by apply Z.le_max_l.
  assert (Z.max (n * m) (z0 * m) <= Z.max (z * m) (z0 * m)).
  apply Z.max_le_compat_r; arith.
  arith.
  eauto.
  
  assert (include (mul_const z (IInterval None None)) (z * m));
  assert (include (IInterval None None) m) by 
  (unfold include; auto);auto.
  assert (include (mul_const z0 (IInterval None None)) (z0 * m));
  assert (include (IInterval None None) m) by
  (unfold include; auto);auto.

  assert ((Z.min (z * m) (z0 * m)) <= n*m <=(Z.max (z * m) (z0 * m))).
  destruct (m >? 0) eqn:?.
  assert ( (z * m) <= (n* m) <= (z0 * m));split.
  1-2: apply Zmult_lt_0_le_compat_r; arith. 
  assert (Z.min (n * m) (z0 * m) <= n * m) by apply Z.le_min_l.
  assert (Z.min (z * m) (z0 * m) <= Z.min (n * m) (z0 * m)).
  apply Z.min_le_compat_r;arith.
  arith.
  assert (n * m <= Z.max (z * m) (n * m)) by apply Z.le_max_r.
  assert (Z.max (z * m) (n * m) <= Z.max (z * m) (z0 * m)).
  apply Z.max_le_compat_l;arith.
  arith.
  assert ( (z0 * m) <= (n* m) <= (z * m));split.
  1-2: apply Z.mul_le_mono_nonpos_r; arith.
  assert (Z.min (z * m) (n * m) <= n * m) by apply Z.le_min_r.
  assert (Z.min (z * m) (z0 * m) <= Z.min (z * m) (n * m) ).
  apply Z.min_le_compat_l;arith.
  arith.
  assert (n * m <= Z.max (n * m) (z0 * m)) by apply Z.le_max_l.
  assert (Z.max (n * m) (z0 * m) <= Z.max (z * m) (z0 * m)).
  apply Z.max_le_compat_r; arith.
  arith.
  eauto.
  
  all: unfold include.
  destruct (z1 <=? 0) eqn:?.
  unfold mul_const;unfold emptyb.
  assert (z1 <? z0 = false) by arith.
  erewrite H1 by eauto.
  destruct (z =? 0) eqn:?.
  assert (0 <= n) by arith.
  assert (m <=0) by arith.
  assert (n*m <=0) by (apply Z.mul_nonneg_nonpos;arith).
  split;auto;omega.
  destruct (z >? 0) eqn:?; split; auto.
  assert (z1 * n <= z1 * z) by (apply Z.mul_le_mono_nonpos_l;arith).
  assert (m * n <= z1 * n) by (apply Zmult_gt_0_le_compat_r; arith).
  1-2: assert ( n * m = m * n) by apply Z.mul_comm.
  omega.
  
  assert (z0 * n <= z0 * z) by (apply Z.mul_le_mono_nonpos_l;arith).
  destruct ( n >?0) eqn:?.
  assert (m*n <= 0) by (apply Z.mul_nonpos_nonneg; arith).
  assert ( 0 <= z0 * z)by (apply Z.mul_nonpos_nonpos; arith).
  omega.
  assert (m * n <= z0 * n) by (apply Z.mul_le_mono_nonpos_r;arith).
  omega.
  
  1-2: destruct (0 <=? z0) eqn:?;
  unfold mul_const;unfold emptyb.
  assert (z1 <? z0 = false) by arith.
  erewrite H1 by eauto.
  
  destruct (z =? 0) eqn:?.
  assert (0 <= n) by arith.
  split;auto.
  apply Z.mul_nonneg_nonneg;arith.
  destruct (z >? 0) eqn:?; split; auto.
  1-2: assert ( n * m = m * n) by apply Z.mul_comm.
  assert (z0 * z <= m * z) by (apply Z.mul_le_mono_nonneg_r; arith).
  assert (m * z <= m *n) by (apply Z.mul_le_mono_nonneg_l; arith).
  arith.
  assert (z1 * z <= m * z) by (apply Z.mul_le_mono_neg_r; arith).
  assert (m * z <= m *n) by (apply Z.mul_le_mono_nonneg_l; arith).
  arith.
  
  unfold top;split;auto.
  
  destruct (z =? 0) eqn:?.
  assert (0 <= n) by arith.
  unfold include;split;auto.
  apply Z.mul_nonneg_nonneg;arith.
  
  destruct (z >? 0) eqn:?; split; auto.
  assert ( n * m = m * n) by apply Z.mul_comm.
  assert (z0 * z <= m * z) by (apply Z.mul_le_mono_nonneg_r; arith).
  assert (m * z <= m *n) by (apply Z.mul_le_mono_nonneg_l; arith).
  arith.
  
  unfold top;split;auto.
  
  1,5: destruct (z0 <=? 0) eqn:?.
  6-7: destruct (0 <=? z0) eqn:?.
  2,4,9: unfold top;split;auto.
  3,7-11: split;auto.
  4: destruct (z1 <=? 0) eqn:?.
  all: unfold mul_const; unfold emptyb.
  5: unfold top;split;auto.
  
  1,2,5: destruct (z =? 0) eqn:?.
  1,3,5: split;auto.
  apply Z.mul_nonneg_nonpos;arith.
  apply Z.mul_nonpos_nonpos;arith.
  apply Z.mul_nonpos_nonneg;arith.
  1-3: destruct (z >? 0) eqn:?.
  1-6: split; auto.
  
  1-3: assert ( n * m = m * n) by apply Z.mul_comm.
  assert (m * n <= z0 * n <= z0 * z).
  split.
  apply Z.mul_le_mono_nonneg_r; arith.
  apply Z.mul_le_mono_nonpos_l; arith.
  omega.
  assert (z0 * z <= z0 * n <= m * n).
  split.
  apply Z.mul_le_mono_nonpos_l; arith.
  apply Z.mul_le_mono_nonpos_r; arith.
  omega.
  assert (m * n <= z0 * n <= z0 * z).
  split.
  apply Z.mul_le_mono_nonpos_r; arith.
  apply Z.mul_le_mono_nonneg_l; arith.
  omega.
  
  all: assert (z1 <? z0 = false) by arith.
  all: erewrite H1 by eauto.
  all: destruct (z =? 0) eqn:?.
  1,3: split;auto.
  apply Z.mul_nonpos_nonneg;arith.
  apply Z.mul_nonpos_nonpos;arith.
  all:destruct (z >? 0) eqn:?.
  all: split;auto.
  all: assert ( n * m = m * n) by apply Z.mul_comm.
  
  assert (m * n <= m * z <= z1 * z).
  split.
  apply Z.mul_le_mono_nonneg_l; arith.
  apply Z.mul_le_mono_nonneg_r; arith.
  omega.
  
  assert (m * n <= m * z <= z0 * z).
  split.
  apply Z.mul_le_mono_nonneg_l; arith.
  apply Z.mul_le_mono_nonpos_r; arith.
  omega.
  

  assert (z0 * z <= m * z <=  m * n ).
  split.
  apply Z.mul_le_mono_nonneg_r; arith.
  apply Z.mul_le_mono_nonpos_l; arith.
  omega.
  
  assert (z1 * z <= m * z <=  m * n ).
  split.
  apply Z.mul_le_mono_nonpos_r; arith.
  apply Z.mul_le_mono_nonpos_l; arith.
  omega.
  
Qed.
  
(* Same as inb
Definition elem (a: Z) (x: interval) : bool :=
  match x with
  | IInterval xlo xhi =>
    match xlo, xhi with
    | None, None => true
    | None, Some b => a <=? b
    | Some b, None => a >=? b
    | Some b, Some c => andb (a >=? b) (a <=? c)
    end
  end. *)
  


Definition div (x: interval) (y: interval) : interval :=
  if orb (emptyb x) (emptyb y) then bottom else
    match y with
    | IInterval ylo yhi =>
      match ylo, yhi with
      | Some a, Some b => 
        if inb y 0 then top
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

    
Definition widen (x y : interval) : interval:=
  if emptyb x then y
  else if emptyb y then x
  else match x,y with
    | IInterval xlo xhi, IInterval ylo yhi =>
      let lower := match xlo, ylo with
      | Some a, Some b => 
        if b <? a then None
        else Some a
      | _,_ => None
      end
      in
      let upper := match xhi, yhi with
      | Some a, Some b => 
        if a <? b then None
        else Some a
      | _,_ => None
      end
      in
      IInterval lower upper
    end.
    

Lemma widen_sound : forall x y : interval,
  le x (widen x y) /\ le y (widen x y).
Proof.
  intros; split; do 2 intro;
  unfold include;
  destruct x as [[] []], y as [[] []];
  unfold widen;
  try erewrite !include_non_empty by eauto;
  unfold emptyb;
  unfold include in *.
  destruct (z2 <? z1);auto;split; auto.
  destruct (z1 <? z) ;auto;omega.
  destruct (z0 <? z2);auto;omega.
  destruct (z1 <? z);split;auto;omega.
  split;auto.
  destruct (z0 <? z1) eqn:?;auto;omega.
  split;auto.
  
  destruct (z1 <? z0);split;auto. omega.
  1-2: destruct (z0 <? z);auto. omega.
  1-2: split; auto.
  
  destruct (z1 <? z0);split;auto. omega.
  
  destruct (z <? z1);auto;omega.
  1-3: split;auto.
  
  destruct (z <? z0);auto;omega.
  
  destruct (z0 <? z).
  1-5: split;auto.
  
  1-4: destruct (z0 <? z).
  auto.
  
  assert (z2 <? z1 = false) by arith.
  erewrite H0 by eauto.
  
  all: try split;auto.
  
  destruct (z1 <? z) eqn:?; auto.
  arith.
  
  destruct (z0 <? z2)eqn:?;auto. 
  1-2: arith.

  destruct (z1 <? z) eqn:?; auto.
  1-2: arith.

  destruct (z0 <? z1)eqn:?;auto. 
  arith.

  1,3: assert (z1 <? z0 = false) by arith.
  1-2: erewrite H0 by eauto.
  2: split;auto.
  
  1,3,5: destruct (z0 <? z) eqn:?; try split; auto.
  1-2: arith.
  
  destruct (z <? z1) eqn:?;auto. arith.
  
  destruct (z <? z0)eqn:?;auto. arith.
Qed.

(*TODO <-*)
Lemma leb_le : forall x y : interval,
  leb x y = true -> le x y.
Proof.
destruct x as [[] []], y as [[] []];
unfold leb; unfold le; unfold include; unfold emptyb.
1-16 : repeat match goal with
| |- ((if ?cond then _ else _) = true) -> _ => (destruct cond eqn:?)
end; intros; try discriminate; repeat split; try arith.
(*all: intros;
repeat match goal with
| |- ((if ?cond then _ else _) = true) => (destruct cond eqn:?)
end; auto; try arith.*)

Qed.

Lemma eqb_feq : forall x y : interval,
  eqb x y = true -> feq x y.
Proof.
destruct x as [[] []], y as [[] []];
unfold eqb; unfold feq;pose leb_le;
rewrite Bool.andb_true_iff; intros []; split;auto.

Qed.


Lemma feq_sym : forall x y : interval,
  feq x y -> feq y x.
Proof.
unfold feq;intros; destruct H;split;auto.
Qed.

Lemma geb_ge : forall x y : interval,
  geb x y = true -> ge x y.
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
  le empty_interval x.
Proof.
unfold le;unfold empty_interval;unfold include.
intros.
assert (1 <= 0) by omega.
assert (0 < 1) by omega.
contradiction.
Qed.


Lemma interval_le_refl : forall (x : interval),
  le x x.
Proof.
intro.
unfold le.
intros.
auto.
Qed.



