(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import ZArith.
Require Import Rbase.
Parameter ident : Type.

Parameter mk_ident: Z -> ident.


Inductive operator  :=
  | Oplus : operator 
  | Ominus : operator 
  | Omult : operator .

Inductive expr  :=
  | Econst : Z -> expr 
  | Evar : ident -> expr 
  | Ebin : expr -> operator -> expr -> expr .

Inductive stmt  :=
  | Sskip : stmt 
  | Sassign : ident -> expr -> stmt 
  | Sseq : stmt -> stmt -> stmt 
  | Sif : expr -> stmt -> stmt -> stmt 
  | Swhile : expr -> stmt -> stmt .

Axiom check_skip : forall (s:stmt), (s = Sskip) \/ ~ (s = Sskip).

Parameter map : forall (a:Type) (b:Type), Type.

Parameter get: forall (a:Type) (b:Type), (map a b) -> a -> b.

Implicit Arguments get.

Parameter set: forall (a:Type) (b:Type), (map a b) -> a -> b -> (map a b).

Implicit Arguments set.

Axiom Select_eq : forall (a:Type) (b:Type), forall (m:(map a b)),
  forall (a1:a) (a2:a), forall (b1:b), (a1 = a2) -> ((get (set m a1 b1)
  a2) = b1).

Axiom Select_neq : forall (a:Type) (b:Type), forall (m:(map a b)),
  forall (a1:a) (a2:a), forall (b1:b), (~ (a1 = a2)) -> ((get (set m a1 b1)
  a2) = (get m a2)).

Parameter const: forall (b:Type) (a:Type), b -> (map a b).

Set Contextual Implicit.
Implicit Arguments const.
Unset Contextual Implicit.

Axiom Const : forall (b:Type) (a:Type), forall (b1:b) (a1:a), ((get (const(
  b1):(map a b)) a1) = b1).

Definition state  := (map ident Z).

Definition eval_bin(x:Z) (op:operator) (y:Z): Z :=
  match op with
  | Oplus => (x + y)%Z
  | Ominus => (x - y)%Z
  | Omult => (x * y)%Z
  end.

Set Implicit Arguments.
Fixpoint eval_expr(s:(map ident Z)) (e:expr) {struct e}: Z :=
  match e with
  | (Econst n) => n
  | (Evar x) => (get s x)
  | (Ebin e1 op e2) => (eval_bin (eval_expr s e1) op (eval_expr s e2))
  end.
Unset Implicit Arguments.

Inductive one_step : (map ident Z) -> stmt -> (map ident Z)
  -> stmt -> Prop :=
  | one_step_assign : forall (s:(map ident Z)) (x:ident) (e:expr),
      (one_step s (Sassign x e) (set s x (eval_expr s e)) Sskip)
  | one_step_seq : forall (s:(map ident Z)) (sqt:(map ident Z)) (i1:stmt)
      (i1qt:stmt) (i2:stmt), (one_step s i1 sqt i1qt) -> (one_step s (Sseq i1
      i2) sqt (Sseq i1qt i2))
  | one_step_seq_skip : forall (s:(map ident Z)) (i:stmt), (one_step s
      (Sseq Sskip i) s i)
  | one_step_if_true : forall (s:(map ident Z)) (e:expr) (i1:stmt) (i2:stmt),
      (~ ((eval_expr s e) = 0%Z)) -> (one_step s (Sif e i1 i2) s i1)
  | one_step_if_false : forall (s:(map ident Z)) (e:expr) (i1:stmt)
      (i2:stmt), ((eval_expr s e) = 0%Z) -> (one_step s (Sif e i1 i2) s i2)
  | one_step_while_true : forall (s:(map ident Z)) (e:expr) (i:stmt),
      (~ ((eval_expr s e) = 0%Z)) -> (one_step s (Swhile e i) s (Sseq i
      (Swhile e i)))
  | one_step_while_false : forall (s:(map ident Z)) (e:expr) (i:stmt),
      ((eval_expr s e) = 0%Z) -> (one_step s (Swhile e i) s Sskip).

Axiom progress : forall (s:(map ident Z)) (i:stmt), (~ (i = Sskip)) ->
  exists sqt:(map ident Z), exists iqt:stmt, (one_step s i sqt iqt).

Inductive many_steps : (map ident Z) -> stmt -> (map ident Z)
  -> stmt -> Prop :=
  | many_steps_refl : forall (s:(map ident Z)) (i:stmt), (many_steps s i s i)
  | many_steps_trans : forall (s1:(map ident Z)) (s2:(map ident Z)) (s3:(map
      ident Z)) (i1:stmt) (i2:stmt) (i3:stmt), (one_step s1 i1 s2 i2) ->
      ((many_steps s2 i2 s3 i3) -> (many_steps s1 i1 s3 i3)).

Axiom many_steps_seq_rec : forall (s1:(map ident Z)) (s3:(map ident Z))
  (i:stmt) (i3:stmt), (many_steps s1 i s3 i3) -> ((i3 = Sskip) ->
  forall (i1:stmt) (i2:stmt), (i = (Sseq i1 i2)) -> exists s2:(map ident Z),
  (many_steps s1 i1 s2 Sskip) /\ (many_steps s2 i2 s3 Sskip)).

Axiom many_steps_seq : forall (s1:(map ident Z)) (s3:(map ident Z)) (i1:stmt)
  (i2:stmt), (many_steps s1 (Sseq i1 i2) s3 Sskip) -> exists s2:(map ident
  Z), (many_steps s1 i1 s2 Sskip) /\ (many_steps s2 i2 s3 Sskip).

Inductive fmla  :=
  | Fterm : expr -> fmla .

Definition eval_fmla(s:(map ident Z)) (f:fmla): Prop :=
  match f with
  | (Fterm e) => ~ ((eval_expr s e) = 0%Z)
  end.

Parameter subst_expr: expr -> ident -> expr -> expr.


Axiom subst_expr_def : forall (e:expr) (x:ident) (t:expr),
  match e with
  | (Econst _) => ((subst_expr e x t) = e)
  | (Evar y) => ((x = y) -> ((subst_expr e x t) = t)) /\ ((~ (x = y)) ->
      ((subst_expr e x t) = e))
  | (Ebin e1 op e2) => ((subst_expr e x t) = (Ebin (subst_expr e1 x t) op
      (subst_expr e2 x t)))
  end.

Axiom eval_subst_expr : forall (s:(map ident Z)) (e:expr) (x:ident) (t:expr),
  ((eval_expr s (subst_expr e x t)) = (eval_expr (set s x (eval_expr s t))
  e)).

Definition subst(f:fmla) (x:ident) (t:expr): fmla :=
  match f with
  | (Fterm e) => (Fterm (subst_expr e x t))
  end.

Axiom eval_subst : forall (s:(map ident Z)) (f:fmla) (x:ident) (t:expr),
  (eval_fmla s (subst f x t)) -> (eval_fmla (set s x (eval_expr s t)) f).

Inductive triple  :=
  | T : fmla -> stmt -> fmla -> triple .

Definition valid_triple(t:triple): Prop :=
  match t with
  | (T p i q) => forall (s:(map ident Z)), (eval_fmla s p) ->
      forall (sqt:(map ident Z)), (many_steps s i sqt Sskip) ->
      (eval_fmla sqt q)
  end.

Axiom assign_rule : forall (q:fmla) (x:ident) (e:expr),
  (valid_triple (T (subst q x e) (Sassign x e) q)).

(* YOU MAY EDIT THE CONTEXT BELOW *)

(* DO NOT EDIT BELOW *)

Theorem seq_rule : forall (p:fmla) (q:fmla) (r:fmla) (i1:stmt) (i2:stmt),
  ((valid_triple (T p i1 r)) /\ (valid_triple (T r i2 q))) ->
  (valid_triple (T p (Sseq i1 i2) q)).
(* YOU MAY EDIT THE PROOF BELOW *)
intros p q r i1 i2 (H1,H2).
unfold valid_triple in *.
intros s Hp s' Hsteps.
generalize (many_steps_seq _ _ _ _ Hsteps).
intro H; elim H;clear H.
intros s0 (H3,H4).
apply H2 with (s:=s0); auto.
apply H1 with (s:=s); auto.
Qed.
(* DO NOT EDIT BELOW *)


