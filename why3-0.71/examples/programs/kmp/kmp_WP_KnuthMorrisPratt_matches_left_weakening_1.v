(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import ZArith.
Require Import Rbase.
Definition unit  := unit.

Parameter mark : Type.

Parameter at1: forall (a:Type), a -> mark  -> a.

Implicit Arguments at1.

Parameter old: forall (a:Type), a  -> a.

Implicit Arguments old.

Inductive ref (a:Type) :=
  | mk_ref : a -> ref a.
Implicit Arguments mk_ref.

Definition contents (a:Type)(u:(ref a)): a :=
  match u with
  | mk_ref contents1 => contents1
  end.
Implicit Arguments contents.

Parameter map : forall (a:Type) (b:Type), Type.

Parameter get: forall (a:Type) (b:Type), (map a b) -> a  -> b.

Implicit Arguments get.

Parameter set: forall (a:Type) (b:Type), (map a b) -> a -> b  -> (map a b).

Implicit Arguments set.

Axiom Select_eq : forall (a:Type) (b:Type), forall (m:(map a b)),
  forall (a1:a) (a2:a), forall (b1:b), (a1 = a2) -> ((get (set m a1 b1)
  a2) = b1).

Axiom Select_neq : forall (a:Type) (b:Type), forall (m:(map a b)),
  forall (a1:a) (a2:a), forall (b1:b), (~ (a1 = a2)) -> ((get (set m a1 b1)
  a2) = (get m a2)).

Parameter const: forall (b:Type) (a:Type), b  -> (map a b).

Set Contextual Implicit.
Implicit Arguments const.
Unset Contextual Implicit.

Axiom Const : forall (b:Type) (a:Type), forall (b1:b) (a1:a), ((get (const(
  b1):(map a b)) a1) = b1).

Inductive array (a:Type) :=
  | mk_array : Z -> (map Z a) -> array a.
Implicit Arguments mk_array.

Definition elts (a:Type)(u:(array a)): (map Z a) :=
  match u with
  | mk_array _ elts1 => elts1
  end.
Implicit Arguments elts.

Definition length (a:Type)(u:(array a)): Z :=
  match u with
  | mk_array length1 _ => length1
  end.
Implicit Arguments length.

Definition get1 (a:Type)(a1:(array a)) (i:Z): a := (get (elts a1) i).
Implicit Arguments get1.

Definition set1 (a:Type)(a1:(array a)) (i:Z) (v:a): (array a) :=
  match a1 with
  | mk_array xcl0 _ => (mk_array xcl0 (set (elts a1) i v))
  end.
Implicit Arguments set1.

Parameter char : Type.

Definition matches(a1:(array char)) (i1:Z) (a2:(array char)) (i2:Z)
  (n:Z): Prop := ((0%Z <= i1)%Z /\ (i1 <= ((length a1) - n)%Z)%Z) /\
  (((0%Z <= i2)%Z /\ (i2 <= ((length a2) - n)%Z)%Z) /\ forall (i:Z),
  ((0%Z <= i)%Z /\ (i <  n)%Z) -> ((get1 a1 (i1 + i)%Z) = (get1 a2
  (i2 + i)%Z))).

Axiom matches_empty : forall (a1:(array char)) (a2:(array char)) (i1:Z)
  (i2:Z), ((0%Z <= i1)%Z /\ (i1 <= (length a1))%Z) -> (((0%Z <= i2)%Z /\
  (i2 <= (length a2))%Z) -> (matches a1 i1 a2 i2 0%Z)).

Axiom matches_right_extension : forall (a1:(array char)) (a2:(array char))
  (i1:Z) (i2:Z) (n:Z), (matches a1 i1 a2 i2 n) ->
  ((i1 <= (((length a1) - n)%Z - 1%Z)%Z)%Z ->
  ((i2 <= (((length a2) - n)%Z - 1%Z)%Z)%Z -> (((get1 a1
  (i1 + n)%Z) = (get1 a2 (i2 + n)%Z)) -> (matches a1 i1 a2 i2
  (n + 1%Z)%Z)))).

Axiom matches_contradiction_at_first : forall (a1:(array char)) (a2:(array
  char)) (i1:Z) (i2:Z) (n:Z), (0%Z <  n)%Z -> ((~ ((get1 a1 i1) = (get1 a2
  i2))) -> ~ (matches a1 i1 a2 i2 n)).

Axiom matches_contradiction_at_i : forall (a1:(array char)) (a2:(array char))
  (i1:Z) (i2:Z) (i:Z) (n:Z), (0%Z <  n)%Z -> (((0%Z <= i)%Z /\ (i <  n)%Z) ->
  ((~ ((get1 a1 (i1 + i)%Z) = (get1 a2 (i2 + i)%Z))) -> ~ (matches a1 i1 a2
  i2 n))).

Axiom matches_right_weakening : forall (a1:(array char)) (a2:(array char))
  (i1:Z) (i2:Z) (n:Z) (nqt:Z), (matches a1 i1 a2 i2 n) -> ((nqt <  n)%Z ->
  (matches a1 i1 a2 i2 nqt)).

Theorem matches_left_weakening : forall (a1:(array char)) (a2:(array char))
  (i1:Z) (i2:Z) (n:Z) (nqt:Z), (matches a1 (i1 - (n - nqt)%Z)%Z a2
  (i2 - (n - nqt)%Z)%Z n) -> ((nqt <  n)%Z -> (matches a1 i1 a2 i2 nqt)).
(* YOU MAY EDIT THE PROOF BELOW *)
intros a1 a2 i1 i2 n n' Hmatch Hn.
destruct Hmatch. destruct H0.
red.
split.
 omega.
split.
 omega.
intros i Hi.
replace (i1 + i)%Z with (i1 - (n - n') + (i + (n - n')))%Z.
replace (i2 + i)%Z with (i2 - (n - n') + (i + (n - n')))%Z.
apply H1.
omega.
 omega.
 omega.
Qed.
(* DO NOT EDIT BELOW *)


