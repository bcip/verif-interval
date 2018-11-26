Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.
Open Scope Z_scope.

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

(* Lemma include_inb : forall i x,
  include i x -> inb i x = true. *)

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
      

Definition is_nonnegb (x: interval) : bool :=
  match x with
  | IInterval xlo xhi =>
    match xlo with
    | None => false
    | Some a => Z.leb 0 a
    end
  end.
  
Definition is_nonposb (x: interval) : bool :=
match x with
| IInterval xlo xhi =>
  match xhi with
  | None => false
  | Some a => Z.leb a 0
  end
end.

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







