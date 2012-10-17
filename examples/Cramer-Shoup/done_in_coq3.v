(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)
Require Export Why.

(*Why logic*) Definition bool_and : bool -> bool -> bool.
Admitted.

(*Why logic*) Definition bool_or : bool -> bool -> bool.
Admitted.

(*Why logic*) Definition bool_xor : bool -> bool -> bool.
Admitted.

(*Why logic*) Definition bool_not : bool -> bool.
Admitted.

(*Why axiom*) Lemma bool_and_def :
  (forall (a:bool),
   (forall (b:bool), ((bool_and a b) = true <-> a = true /\ b = true))).
Admitted.

(*Why axiom*) Lemma bool_or_def :
  (forall (a:bool),
   (forall (b:bool), ((bool_or a b) = true <-> a = true \/ b = true))).
Admitted.

(*Why axiom*) Lemma bool_xor_def :
  (forall (a:bool), (forall (b:bool), ((bool_xor a b) = true <-> ~(a = b)))).
Admitted.

(*Why axiom*) Lemma bool_not_def :
  (forall (a:bool), ((bool_not a) = true <-> a = false)).
Admitted.

(*Why logic*) Definition ite : forall (A1:Set), bool -> A1 -> A1 -> A1.
Admitted.
Implicit Arguments ite.

(*Why axiom*) Lemma ite_true :
  forall (A1:Set),
  (forall (x:A1), (forall (y:A1), (if_then_else true x y) = x)).
Admitted.

(*Why axiom*) Lemma ite_false :
  forall (A1:Set),
  (forall (x:A1), (forall (y:A1), (if_then_else false x y) = y)).
Admitted.

(*Why logic*) Definition lt_int_bool : Z -> Z -> bool.
Admitted.

(*Why logic*) Definition le_int_bool : Z -> Z -> bool.
Admitted.

(*Why logic*) Definition gt_int_bool : Z -> Z -> bool.
Admitted.

(*Why logic*) Definition ge_int_bool : Z -> Z -> bool.
Admitted.

(*Why logic*) Definition eq_int_bool : Z -> Z -> bool.
Admitted.

(*Why logic*) Definition neq_int_bool : Z -> Z -> bool.
Admitted.

(*Why axiom*) Lemma lt_int_bool_axiom :
  (forall (x:Z), (forall (y:Z), ((lt_int_bool x y) = true <-> x < y))).
Admitted.

(*Why axiom*) Lemma le_int_bool_axiom :
  (forall (x:Z), (forall (y:Z), ((le_int_bool x y) = true <-> x <= y))).
Admitted.

(*Why axiom*) Lemma gt_int_bool_axiom :
  (forall (x:Z), (forall (y:Z), ((gt_int_bool x y) = true <-> x > y))).
Admitted.

(*Why axiom*) Lemma ge_int_bool_axiom :
  (forall (x:Z), (forall (y:Z), ((ge_int_bool x y) = true <-> x >= y))).
Admitted.

(*Why axiom*) Lemma eq_int_bool_axiom :
  (forall (x:Z), (forall (y:Z), ((eq_int_bool x y) = true <-> x = y))).
Admitted.

(*Why axiom*) Lemma neq_int_bool_axiom :
  (forall (x:Z), (forall (y:Z), ((neq_int_bool x y) = true <-> x <> y))).
Admitted.

(*Why logic*) Definition abs_int : Z -> Z.
Admitted.

(*Why axiom*) Lemma abs_int_pos :
  (forall (x:Z), (x >= 0 -> (abs_int x) = x)).
Admitted.

(*Why axiom*) Lemma abs_int_neg :
  (forall (x:Z), (x <= 0 -> (abs_int x) = (Zopp x))).
Admitted.

(*Why logic*) Definition int_max : Z -> Z -> Z.
Admitted.

(*Why logic*) Definition int_min : Z -> Z -> Z.
Admitted.

(*Why axiom*) Lemma int_max_is_ge :
  (forall (x:Z), (forall (y:Z), (int_max x y) >= x /\ (int_max x y) >= y)).
Admitted.

(*Why axiom*) Lemma int_max_is_some :
  (forall (x:Z), (forall (y:Z), (int_max x y) = x \/ (int_max x y) = y)).
Admitted.

(*Why axiom*) Lemma int_min_is_le :
  (forall (x:Z), (forall (y:Z), (int_min x y) <= x /\ (int_min x y) <= y)).
Admitted.

(*Why axiom*) Lemma int_min_is_some :
  (forall (x:Z), (forall (y:Z), (int_min x y) = x \/ (int_min x y) = y)).
Admitted.

(*Why logic*) Definition computer_div : Z -> Z -> Z.
Admitted.

(*Why logic*) Definition computer_mod : Z -> Z -> Z.
Admitted.

(*Why logic*) Definition math_div : Z -> Z -> Z.
Admitted.

(*Why logic*) Definition math_mod : Z -> Z -> Z.
Admitted.

(*Why axiom*) Lemma math_div_mod :
  (forall (x:Z),
   (forall (y:Z), (y <> 0 -> x = (y * (math_div x y) + (math_mod x y))))).
Admitted.

(*Why axiom*) Lemma math_mod_bound :
  (forall (x:Z),
   (forall (y:Z),
    (y <> 0 -> 0 <= (math_mod x y) /\ (math_mod x y) < (abs_int y)))).
Admitted.

(*Why axiom*) Lemma computer_div_mod :
  (forall (x:Z),
   (forall (y:Z),
    (y <> 0 -> x = (y * (computer_div x y) + (computer_mod x y))))).
Admitted.

(*Why axiom*) Lemma computer_div_bound :
  (forall (x:Z),
   (forall (y:Z),
    (x >= 0 /\ y > 0 -> 0 <= (computer_div x y) /\ (computer_div x y) <= x))).
Admitted.

(*Why axiom*) Lemma computer_mod_bound :
  (forall (x:Z),
   (forall (y:Z), (y <> 0 -> (abs_int (computer_mod x y)) < (abs_int y)))).
Admitted.

(*Why axiom*) Lemma computer_mod_sign_pos :
  (forall (x:Z),
   (forall (y:Z), (x >= 0 /\ y <> 0 -> (computer_mod x y) >= 0))).
Admitted.

(*Why axiom*) Lemma computer_mod_sign_neg :
  (forall (x:Z),
   (forall (y:Z), (x <= 0 /\ y <> 0 -> (computer_mod x y) <= 0))).
Admitted.

(*Why axiom*) Lemma computer_rounds_toward_zero :
  (forall (x:Z),
   (forall (y:Z),
    (y <> 0 -> (abs_int ((computer_div x y) * y)) <= (abs_int x)))).
Admitted.
Require Import Reals.
(*Why logic*) Definition lt_real : R -> R -> Prop.
Admitted.

(*Why logic*) Definition le_real : R -> R -> Prop.
Admitted.

(*Why logic*) Definition gt_real : R -> R -> Prop.
Admitted.

(*Why logic*) Definition ge_real : R -> R -> Prop.
Admitted.

(*Why logic*) Definition eq_real : R -> R -> Prop.
Admitted.

(*Why logic*) Definition neq_real : R -> R -> Prop.
Admitted.

(*Why logic*) Definition add_real : R -> R -> R.
Admitted.

(*Why logic*) Definition sub_real : R -> R -> R.
Admitted.

(*Why logic*) Definition mul_real : R -> R -> R.
Admitted.

(*Why logic*) Definition div_real : R -> R -> R.
Admitted.

(*Why logic*) Definition neg_real : R -> R.
Admitted.

(*Why logic*) Definition real_of_int : Z -> R.
Admitted.

(*Why axiom*) Lemma real_of_int_zero : (eq (IZR 0) (0)%R).
Admitted.

(*Why axiom*) Lemma real_of_int_one : (eq (IZR 1) (1)%R).
Admitted.

(*Why axiom*) Lemma real_of_int_add :
  (forall (x:Z), (forall (y:Z), (eq (IZR (x + y)) (Rplus (IZR x) (IZR y))))).
Admitted.

(*Why axiom*) Lemma real_of_int_sub :
  (forall (x:Z), (forall (y:Z), (eq (IZR (x - y)) (Rminus (IZR x) (IZR y))))).
Admitted.

(*Why logic*) Definition truncate_real_to_int : R -> Z.
Admitted.

(*Why axiom*) Lemma truncate_down_pos :
  (forall (x:R),
   ((Rge x (0)%R) -> (Rle (IZR (truncate_real_to_int x)) x) /\
    (Rlt x (IZR ((truncate_real_to_int x) + 1))))).
Admitted.

(*Why axiom*) Lemma truncate_up_neg :
  (forall (x:R),
   ((Rle x (0)%R) -> (Rlt (IZR ((truncate_real_to_int x) - 1)) x) /\
    (Rle x (IZR (truncate_real_to_int x))))).
Admitted.

(*Why logic*) Definition floor_real_to_int : R -> Z.
Admitted.

(*Why logic*) Definition ceil_real_to_int : R -> Z.
Admitted.

(*Why logic*) Definition lt_real_bool : R -> R -> bool.
Admitted.

(*Why logic*) Definition le_real_bool : R -> R -> bool.
Admitted.

(*Why logic*) Definition gt_real_bool : R -> R -> bool.
Admitted.

(*Why logic*) Definition ge_real_bool : R -> R -> bool.
Admitted.

(*Why logic*) Definition eq_real_bool : R -> R -> bool.
Admitted.

(*Why logic*) Definition neq_real_bool : R -> R -> bool.
Admitted.

(*Why axiom*) Lemma lt_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((lt_real_bool x y) = true <-> (Rlt x y)))).
Admitted.

(*Why axiom*) Lemma le_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((le_real_bool x y) = true <-> (Rle x y)))).
Admitted.

(*Why axiom*) Lemma gt_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((gt_real_bool x y) = true <-> (Rgt x y)))).
Admitted.

(*Why axiom*) Lemma ge_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((ge_real_bool x y) = true <-> (Rge x y)))).
Admitted.

(*Why axiom*) Lemma eq_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((eq_real_bool x y) = true <-> (eq x y)))).
Admitted.

(*Why axiom*) Lemma neq_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((neq_real_bool x y) = true <-> ~(eq x y)))).
Admitted.

(*Why logic*) Definition real_max : R -> R -> R.
Admitted.

(*Why logic*) Definition real_min : R -> R -> R.
Admitted.

(*Why axiom*) Lemma real_max_is_ge :
  (forall (x:R),
   (forall (y:R), (Rge (real_max x y) x) /\ (Rge (real_max x y) y))).
Admitted.

(*Why axiom*) Lemma real_max_is_some :
  (forall (x:R),
   (forall (y:R), (eq (real_max x y) x) \/ (eq (real_max x y) y))).
Admitted.

(*Why axiom*) Lemma real_min_is_le :
  (forall (x:R),
   (forall (y:R), (Rle (real_min x y) x) /\ (Rle (real_min x y) y))).
Admitted.

(*Why axiom*) Lemma real_min_is_some :
  (forall (x:R),
   (forall (y:R), (eq (real_min x y) x) \/ (eq (real_min x y) y))).
Admitted.

(*Why function*) Definition sqr_real  (x:R) := (Rmult x x).

(*Why logic*) Definition sqrt_real : R -> R.
Admitted.

(*Why axiom*) Lemma sqrt_pos :
  (forall (x:R), ((Rge x (0)%R) -> (Rge (sqrt x) (0)%R))).
Admitted.

(*Why axiom*) Lemma sqrt_sqr :
  (forall (x:R), ((Rge x (0)%R) -> (eq (sqr_real (sqrt x)) x))).
Admitted.

(*Why axiom*) Lemma sqr_sqrt :
  (forall (x:R), ((Rge x (0)%R) -> (eq (sqrt (Rmult x x)) x))).
Admitted.

(*Why logic*) Definition pow_real : R -> R -> R.
Admitted.

(*Why logic*) Definition abs_real : R -> R.
Admitted.

(*Why axiom*) Lemma abs_real_pos :
  (forall (x:R), ((Rge x (0)%R) -> (eq (Rabs x) x))).
Admitted.

(*Why axiom*) Lemma abs_real_neg :
  (forall (x:R), ((Rle x (0)%R) -> (eq (Rabs x) (Ropp x)))).
Admitted.

(*Why logic*) Definition exp : R -> R.
Admitted.

(*Why logic*) Definition log : R -> R.
Admitted.

(*Why logic*) Definition log10 : R -> R.
Admitted.

(*Why axiom*) Lemma log_exp : (forall (x:R), (eq (log (exp x)) x)).
Admitted.

(*Why axiom*) Lemma exp_log :
  (forall (x:R), ((Rgt x (0)%R) -> (eq (exp (log x)) x))).
Admitted.

(*Why logic*) Definition cos : R -> R.
Admitted.

(*Why logic*) Definition sin : R -> R.
Admitted.

(*Why logic*) Definition tan : R -> R.
Admitted.

(*Why logic*) Definition pi : R.
Admitted.

(*Why logic*) Definition cosh : R -> R.
Admitted.

(*Why logic*) Definition sinh : R -> R.
Admitted.

(*Why logic*) Definition tanh : R -> R.
Admitted.

(*Why logic*) Definition acos : R -> R.
Admitted.

(*Why logic*) Definition asin : R -> R.
Admitted.

(*Why logic*) Definition atan : R -> R.
Admitted.

(*Why logic*) Definition atan2 : R -> R -> R.
Admitted.

(*Why logic*) Definition hypot : R -> R -> R.
Admitted.

(*Why axiom*) Lemma prod_pos :
  (forall (x:R),
   (forall (y:R),
    (((Rgt x (0)%R) /\ (Rgt y (0)%R) -> (Rgt (Rmult x y) (0)%R))) /\
    (((Rlt x (0)%R) /\ (Rlt y (0)%R) -> (Rgt (Rmult x y) (0)%R))))).
Admitted.

(*Why axiom*) Lemma abs_minus :
  (forall (x:R), (eq (Rabs (Ropp x)) (Rabs x))).
Admitted.

(*Why logic*) Definition poly_eq : forall (A1:Set), A1 -> A1 -> bool.
Admitted.
Implicit Arguments poly_eq.

(*Why axiom*) Lemma poly_eq_eq :
  forall (A1:Set),
  (forall (x:A1), (forall (y:A1), ((poly_eq x y) = true <-> x = y))).
Admitted.

(*Why axiom*) Lemma poly_eq_refl :
  forall (A1:Set), (forall (x:A1), (poly_eq x x) = true).
Admitted.

(*Why axiom*) Lemma not_true_false :
  (forall (b:bool), (~(b = true) -> b = false)).
Admitted.

(*Why axiom*) Lemma bool_not_false : (bool_not false) = true.
Admitted.

(*Why axiom*) Lemma not_eq_poly_eq_false :
  forall (A1:Set),
  (forall (x:A1), (forall (y:A1), (~(x = y) -> (poly_eq x y) = false))).
Admitted.

(*Why type*) Definition prod: Set -> Set ->Set.
Admitted.

(*Why logic*) Definition pair :
  forall (A1:Set), forall (A2:Set), A1 -> A2 -> (prod A1 A2).
Admitted.
Implicit Arguments pair.

(*Why logic*) Definition fst_prod :
  forall (A1:Set), forall (A2:Set), (prod A1 A2) -> A1.
Admitted.
Implicit Arguments fst_prod.

(*Why logic*) Definition snd_prod :
  forall (A1:Set), forall (A2:Set), (prod A2 A1) -> A1.
Admitted.
Implicit Arguments snd_prod.

(*Why axiom*) Lemma surjective_pairing :
  forall (A1:Set), forall (A2:Set),
  (forall (p:(prod A1 A2)), (pair (fst_prod p) (snd_prod p)) = p).
Admitted.

(*Why axiom*) Lemma fst_pair :
  forall (A1:Set), forall (A2:Set),
  (forall (a:A1), (forall (b:A2), (fst_prod (pair a b)) = a)).
Admitted.

(*Why axiom*) Lemma snd_pair :
  forall (A1:Set), forall (A2:Set),
  (forall (a:A1), (forall (b:A2), (snd_prod (pair a b)) = b)).
Admitted.

(*Why axiom*) Lemma pair_inj :
  forall (A1:Set), forall (A2:Set),
  (forall (a1:A1),
   (forall (a2:A1),
    (forall (b1:A2),
     (forall (b2:A2), ((pair a1 b1) = (pair a2 b2) -> a1 = a2 /\ b1 = b2))))).
Admitted.

(*Why type*) Definition option: Set ->Set.
Admitted.

(*Why logic*) Definition None : forall (A1:Set), (option A1).
Admitted.
Set Contextual Implicit.
Implicit Arguments None.
Unset Contextual Implicit.

(*Why logic*) Definition Some : forall (A1:Set), A1 -> (option A1).
Admitted.
Implicit Arguments Some.

(*Why axiom*) Lemma None_neq_Some :
  forall (A1:Set), (forall (x:A1), ~((@None A1) = (Some x))).
Admitted.

(*Why axiom*) Lemma Some_inj :
  forall (A1:Set),
  (forall (x:A1), (forall (y:A1), ((Some x) = (Some y) -> x = y))).
Admitted.

(*Why type*) Definition list: Set ->Set.
Admitted.

(*Why logic*) Definition Nil : forall (A1:Set), (list A1).
Admitted.
Set Contextual Implicit.
Implicit Arguments Nil.
Unset Contextual Implicit.

(*Why logic*) Definition Cons :
  forall (A1:Set), A1 -> (list A1) -> (list A1).
Admitted.
Implicit Arguments Cons.

(*Why logic*) Definition in_list : forall (A1:Set), A1 -> (list A1) -> bool.
Admitted.
Implicit Arguments in_list.

(*Why logic*) Definition length_list : forall (A1:Set), (list A1) -> Z.
Admitted.
Implicit Arguments length_list.

(*Why axiom*) Lemma Nil_neq_Cons :
  forall (A1:Set),
  (forall (a:A1), (forall (l:(list A1)), ~((@Nil A1) = (Cons a l)))).
Admitted.

(*Why axiom*) Lemma Cons_inj :
  forall (A1:Set),
  (forall (a1:A1),
   (forall (a2:A1),
    (forall (l1:(list A1)),
     (forall (l2:(list A1)),
      ((Cons a1 l1) = (Cons a2 l2) -> a1 = a2 /\ l1 = l2))))).
Admitted.

(*Why axiom*) Lemma in_list_Nil :
  forall (A1:Set), (forall (a:A1), (in_list a (@Nil A1)) = false).
Admitted.

(*Why axiom*) Lemma in_list_Cons :
  forall (A1:Set),
  (forall (a:A1),
   (forall (a':A1),
    (forall (l:(list A1)),
     (in_list a (Cons a' l)) = (bool_or (poly_eq a a') (in_list a l))))).
Admitted.

(*Why axiom*) Lemma length_nil :
  forall (A1:Set), (length_list (@Nil A1)) = 0.
Admitted.

(*Why axiom*) Lemma length_cons :
  forall (A1:Set),
  (forall (a:A1),
   (forall (l:(list A1)), (length_list (Cons a l)) = (1 + (length_list l)))).
Admitted.

(*Why type*) Definition map: Set -> Set ->Set.
Admitted.

(*Why logic*) Definition upd_map :
  forall (A1:Set), forall (A2:Set), (map A1 A2) -> A1 -> A2 -> (map A1 A2).
Admitted.
Implicit Arguments upd_map.

(*Why logic*) Definition get_map :
  forall (A1:Set), forall (A2:Set), (map A2 A1) -> A2 -> A1.
Admitted.
Implicit Arguments get_map.

(*Why logic*) Definition in_dom_map :
  forall (A1:Set), forall (A2:Set), A1 -> (map A1 A2) -> bool.
Admitted.
Implicit Arguments in_dom_map.

(*Why logic*) Definition in_rng_map :
  forall (A1:Set), forall (A2:Set), A1 -> (map A2 A1) -> bool.
Admitted.
Implicit Arguments in_rng_map.

(*Why logic*) Definition empty_map :
  forall (A1:Set), forall (A2:Set), (map A1 A2).
Admitted.
Set Contextual Implicit.
Implicit Arguments empty_map.
Unset Contextual Implicit.

(*Why axiom*) Lemma in_dom_in_range :
  forall (A1:Set), forall (A2:Set),
  (forall (m:(map A1 A2)),
   (forall (a:A1),
    ((in_dom_map a m) = true -> (in_rng_map (get_map m a) m) = true))).
Admitted.

(*Why axiom*) Lemma get_upd_map_same :
  forall (A1:Set), forall (A2:Set),
  (forall (m:(map A1 A2)),
   (forall (a:A1), (forall (b:A2), (get_map (upd_map m a b) a) = b))).
Admitted.

(*Why axiom*) Lemma get_upd_map_diff :
  forall (A1:Set), forall (A2:Set),
  (forall (m:(map A1 A2)),
   (forall (a:A1),
    (forall (a':A1),
     (forall (b:A2),
      (~(a = a') -> (get_map (upd_map m a b) a') = (get_map m a')))))).
Admitted.

(*Why axiom*) Lemma upd_map_com :
  forall (A1:Set), forall (A2:Set),
  (forall (m:(map A1 A2)),
   (forall (a:A1),
    (forall (a':A1),
     (forall (b:A2),
      (forall (b':A2),
       (~(a = a') ->
        (upd_map (upd_map m a b) a' b') = (upd_map (upd_map m a' b') a b))))))).
Admitted.

(*Why axiom*) Lemma upd_map_dom_same :
  forall (A1:Set), forall (A2:Set),
  (forall (m:(map A1 A2)),
   (forall (a:A1), (forall (b:A2), (in_dom_map a (upd_map m a b)) = true))).
Admitted.

(*Why axiom*) Lemma upd_map_dom_diff :
  forall (A1:Set), forall (A2:Set),
  (forall (m:(map A1 A2)),
   (forall (a:A1),
    (forall (a':A1),
     (forall (b:A2),
      (~(a = a') -> (in_dom_map a' (upd_map m a b)) = (in_dom_map a' m)))))).
Admitted.

(*Why axiom*) Lemma in_dom_upd_map :
  forall (A1:Set), forall (A2:Set),
  (forall (m:(map A1 A2)),
   (forall (a:A1),
    (forall (a':A1),
     (forall (b:A2),
      ((in_dom_map a' (upd_map m a b)) = true <-> a = a' \/
       (in_dom_map a' m) = true))))).
Admitted.

(*Why axiom*) Lemma in_dom_upd_map_bool :
  forall (A1:Set), forall (A2:Set),
  (forall (m:(map A1 A2)),
   (forall (a:A1),
    (forall (a':A1),
     (forall (b:A2),
      (in_dom_map a' (upd_map m a b)) =
      (bool_or (poly_eq a a') (in_dom_map a' m)))))).
Admitted.

(*Why axiom*) Lemma upd_map_in_rng_same :
  forall (A1:Set), forall (A2:Set),
  (forall (m:(map A1 A2)),
   (forall (a:A1), (forall (b:A2), (in_rng_map b (upd_map m a b)) = true))).
Admitted.

(*Why axiom*) Lemma upd_map_in_rng_diff :
  forall (A1:Set), forall (A2:Set),
  (forall (m:(map A1 A2)),
   (forall (a:A1),
    (forall (b:A2),
     (forall (b':A2), (in_rng_map b' (upd_map m a b)) = (in_rng_map b' m))))).
Admitted.

(*Why axiom*) Lemma empty_in_dom_map :
  forall (A1:Set), forall (A2:Set),
  (forall (a:A1), (in_dom_map a (@empty_map A1 A2)) = false).
Admitted.

(*Why axiom*) Lemma empty_in_rng_map :
  forall (A1:Set), forall (A2:Set),
  (forall (b:A1), (in_rng_map b (@empty_map A2 A1)) = false).
Admitted.

(*Why type*) Definition bitstring: Set.
Admitted.

(*Why logic*) Definition length_bitstring : bitstring -> Z.
Admitted.

(*Why axiom*) Lemma triangle_equality :
  (forall (x:R),
   (forall (y:R),
    (forall (z:R),
     (Rle (Rabs (Rminus x z)) (Rplus (Rabs (Rminus x y)) (Rabs (Rminus y z))))))).
Admitted.

(*Why logic*) Definition real_of_bool : bool -> R.
Admitted.

(*Why axiom*) Lemma real_of_bool_true :
  (forall (b:bool), (b = true -> (eq (real_of_bool b) (1)%R))).
Admitted.

(*Why axiom*) Lemma real_of_bool_false :
  (forall (b:bool), (b = false -> (eq (real_of_bool b) (0)%R))).
Admitted.

(*Why type*) Definition group: Set.
Admitted.

(*Why logic*) Definition group_pow : group -> Z -> group.
Admitted.

(*Why logic*) Definition group_mul : group -> group -> group.
Admitted.

(*Why logic*) Definition inv_int_mod_q : Z -> Z.
Admitted.

(*Why logic*) Definition dl_g : group -> Z.
Admitted.

(*Why logic*) Definition q : Z.
Admitted.

(*Why logic*) Definition g : group.
Admitted.

(*Why axiom*) Lemma q_pos : 0 < q.
Admitted.

(*Why axiom*) Lemma group_pow_mod :
  (forall (g1_4:group),
   (forall (x_3:Z), (group_pow g1_4 x_3) = (group_pow g1_4 (math_mod x_3 q)))).
Admitted.

(*Why axiom*) Lemma group_pow_mult :
  (forall (g1_10:group),
   (forall (x_9:Z),
    (forall (y_8:Z),
     (group_pow (group_pow g1_10 x_9) y_8) = (group_pow g1_10 (x_9 * y_8))))).
Admitted.

(*Why axiom*) Lemma group_pow_com :
  (forall (g1_16:group),
   (forall (x_15:Z),
    (forall (y_14:Z),
     (group_pow (group_pow g1_16 x_15) y_14) =
     (group_pow (group_pow g1_16 y_14) x_15)))).
Admitted.

(*Why axiom*) Lemma group_pow_mult_distr :
  (forall (g1_22:group),
   (forall (x_21:Z),
    (forall (y_20:Z),
     (group_mul (group_pow g1_22 x_21) (group_pow g1_22 y_20)) =
     (group_pow g1_22 (x_21 + y_20))))).
Admitted.

(*Why axiom*) Lemma group_mult_assoc :
  (forall (g1_28:group),
   (forall (g2_27:group),
    (forall (g3_26:group),
     (group_mul g1_28 (group_mul g2_27 g3_26)) =
     (group_mul (group_mul g1_28 g2_27) g3_26)))).
Admitted.

(*Why axiom*) Lemma group_mul_pow_distr :
  (forall (g1_34:group),
   (forall (g2_33:group),
    (forall (x_32:Z),
     (group_pow (group_mul g1_34 g2_33) x_32) =
     (group_mul (group_pow g1_34 x_32) (group_pow g2_33 x_32))))).
Admitted.

(*Why axiom*) Lemma group_mult_com :
  (forall (g1_38:group),
   (forall (g2_37:group), (group_mul g1_38 g2_37) = (group_mul g2_37 g1_38))).
Admitted.

(*Why axiom*) Lemma plus_mod_idemp_l :
  (forall (a_44:Z),
   (forall (b_43:Z),
    (forall (n_42:Z), (math_mod (a_44 + b_43) n_42) =
     (math_mod ((math_mod a_44 n_42) + b_43) n_42)))).
Admitted.

(*Why axiom*) Lemma plus_mod_idemp_r :
  (forall (a_50:Z),
   (forall (b_49:Z),
    (forall (n_48:Z), (math_mod (a_50 + b_49) n_48) =
     (math_mod (a_50 + (math_mod b_49 n_48)) n_48)))).
Admitted.

(*Why axiom*) Lemma plus_mod :
  (forall (a_56:Z),
   (forall (b_55:Z),
    (forall (n_54:Z), (math_mod (a_56 + b_55) n_54) =
     (math_mod ((math_mod a_56 n_54) + (math_mod b_55 n_54)) n_54)))).
Admitted.

(*Why axiom*) Lemma minus_mod_idemp_l :
  (forall (a_62:Z),
   (forall (b_61:Z),
    (forall (n_60:Z), (math_mod (a_62 - b_61) n_60) =
     (math_mod ((math_mod a_62 n_60) - b_61) n_60)))).
Admitted.

(*Why axiom*) Lemma minus_mod_idemp_r :
  (forall (a_68:Z),
   (forall (b_67:Z),
    (forall (n_66:Z), (math_mod (a_68 - b_67) n_66) =
     (math_mod (a_68 - (math_mod b_67 n_66)) n_66)))).
Admitted.

(*Why axiom*) Lemma minus_mod :
  (forall (a_74:Z),
   (forall (b_73:Z),
    (forall (n_72:Z), (math_mod (a_74 - b_73) n_72) =
     (math_mod ((math_mod a_74 n_72) - (math_mod b_73 n_72)) n_72)))).
Admitted.

(*Why axiom*) Lemma mult_mod_idemp_l :
  (forall (a_80:Z),
   (forall (b_79:Z),
    (forall (n_78:Z), (math_mod (a_80 * b_79) n_78) =
     (math_mod ((math_mod a_80 n_78) * b_79) n_78)))).
Admitted.

(*Why axiom*) Lemma mult_mod_idemp_r :
  (forall (a_86:Z),
   (forall (b_85:Z),
    (forall (n_84:Z), (math_mod (a_86 * b_85) n_84) =
     (math_mod (a_86 * (math_mod b_85 n_84)) n_84)))).
Admitted.

(*Why axiom*) Lemma mult_mod :
  (forall (a_92:Z),
   (forall (b_91:Z),
    (forall (n_90:Z), (math_mod (a_92 * b_91) n_90) =
     (math_mod ((math_mod a_92 n_90) * (math_mod b_91 n_90)) n_90)))).
Admitted.

(*Why axiom*) Lemma mod_small :
  (forall (a_96:Z),
   (forall (n_95:Z),
    (0 <= a_96 -> (a_96 < n_95 -> (math_mod a_96 n_95) = a_96)))).
Admitted.

(*Why axiom*) Lemma mod_mod :
  (forall (a_100:Z),
   (forall (n_99:Z), (math_mod (math_mod a_100 n_99) n_99) =
    (math_mod a_100 n_99))).
Admitted.

(*Why axiom*) Lemma mod_zero_opp :
  (forall (a_104:Z),
   (forall (b_103:Z),
    (0 < b_103 ->
     ((math_mod a_104 b_103) = 0 -> (math_mod (Zopp a_104) b_103) = 0)))).
Admitted.

(*Why axiom*) Lemma mult_mod_q_integral :
  (forall (a_108:Z),
   (forall (b_107:Z),
    ((math_mod (a_108 * b_107) q) = 0 -> (math_mod a_108 q) = 0 \/
     (math_mod b_107 q) = 0))).
Admitted.

(*Why axiom*) Lemma minus_mod_diff :
  (forall (u_112:Z),
   (forall (u'_111:Z),
    (0 <= u_112 ->
     (u_112 <= (q - 1) ->
      (0 <= u'_111 ->
       (u'_111 <= (q - 1) ->
        (~u_112 = u'_111 -> ~(math_mod (u'_111 - u_112) q) = 0))))))).
Admitted.

(*Why axiom*) Lemma minus_mult_mod_0 :
  (forall (u_118:Z),
   (forall (u'_117:Z),
    (forall (pg_116:Z),
     (0 <= u_118 ->
      (u_118 <= (q - 1) ->
       (0 <= u'_117 ->
        (u'_117 <= (q - 1) ->
         (1 <= pg_116 ->
          (pg_116 <= (q - 1) ->
           (~u_118 = u'_117 -> ~(math_mod ((u'_117 - u_118) * pg_116) q) = 0)))))))))).
Admitted.

(*Why axiom*) Lemma aux1 :
  (forall (x_122:Z),
   (forall (z_121:Z),
    (0 <= z_121 ->
     (z_121 <= (q - 1) ->
      (math_mod ((math_mod (z_121 - x_122) q) + x_122) q) = z_121)))).
Admitted.

(*Why axiom*) Lemma aux2 :
  (forall (x_126:Z),
   (forall (z_125:Z),
    (0 <= z_125 ->
     (z_125 <= (q - 1) ->
      (math_mod ((math_mod (z_125 + x_126) q) - x_126) q) = z_125)))).
Admitted.

(*Why axiom*) Lemma inv_correct :
  (forall (x_128:Z),
   (~0 = (math_mod x_128 q) -> (math_mod ((inv_int_mod_q x_128) * x_128) q) =
    1)).
Admitted.

(*Why axiom*) Lemma dl_g_pow :
  (forall (g1_130:group), (group_pow g (dl_g g1_130)) = g1_130).
Admitted.

(*Why axiom*) Lemma pow_dl_g :
  (forall (x_132:Z), (dl_g (group_pow g x_132)) = (math_mod x_132 q)).
Admitted.

(*Why axiom*) Lemma dl_g_bound :
  (forall (g1_134:group), 0 <= (dl_g g1_134) /\ (dl_g g1_134) <= (q - 1)).
Admitted.

(*Why axiom*) Lemma todo_in_coq :
  (forall (U_146:Z),
   (forall (U'_145:Z),
    (forall (z_144:Z),
     (forall (pg_143:Z),
      (forall (Rc_142:Z),
       (forall (aux_141:Z),
        (0 <= U_146 ->
         (U_146 <= (q - 1) ->
          (0 <= U'_145 ->
           (U'_145 <= (q - 1) ->
            (1 <= pg_143 ->
             (pg_143 <= (q - 1) ->
              (~U_146 = U'_145 ->
               (0 <= Rc_142 ->
                (Rc_142 <= (q - 1) ->
                 (math_mod
                  (((math_mod
                     (U_146 * (z_144 - pg_143 * Rc_142) + pg_143 * U'_145 *
                     Rc_142 + aux_141) q) -
                   U_146 * z_144 - aux_141) *
                  (inv_int_mod_q ((U'_145 - U_146) * pg_143))) q) =
                 Rc_142 /\
                 (math_mod
                  (U_146 *
                  (z_144 - pg_143 *
                  (math_mod
                   ((Rc_142 - U_146 * z_144 - aux_141) *
                   (inv_int_mod_q ((U'_145 - U_146) * pg_143))) q)) +
                  pg_143 * U'_145 *
                  (math_mod
                   ((Rc_142 - U_146 * z_144 - aux_141) *
                   (inv_int_mod_q ((U'_145 - U_146) * pg_143))) q) +
                  aux_141) q) =
                 Rc_142))))))))))))))).
Admitted.

(*Why axiom*) Lemma todo_in_coq2_1 :
  (forall (Rap_150:Z),
   (forall (pg_149:Z),
    (0 <= Rap_150 ->
     (Rap_150 <= (q - 1) ->
      (1 <= pg_149 ->
       (pg_149 <= (q - 1) ->
        (math_mod
         ((math_mod (pg_149 * Rap_150) q) * (inv_int_mod_q pg_149)) q) =
        Rap_150)))))).
Admitted.

(*Why axiom*) Lemma todo_in_coq2_2 :
  (forall (Rap_154:Z),
   (forall (pg_153:Z),
    (0 <= Rap_154 ->
     (Rap_154 <= (q - 1) ->
      (1 <= pg_153 ->
       (pg_153 <= (q - 1) ->
        (math_mod
         (pg_153 * (math_mod (Rap_154 * (inv_int_mod_q pg_153)) q)) q) =
        Rap_154)))))).
Admitted.

Ltac push_mod t :=
 match t with
 | (?x + ?y)%Z => rewrite (plus_mod x y q); push_mod x;push_mod y
 | (?x * ?y)%Z => rewrite (mult_mod x y q); push_mod x;push_mod y
 | (?x - ?y)%Z => rewrite (minus_mod x y q); push_mod x;push_mod y
 | _ => idtac 
 end. 

Ltac remove_mod t :=
  match t with
  | math_mod (math_mod ?x q) q => rewrite (mod_mod x)
  | math_mod (math_mod ?x q + math_mod ?y q)%Z q => 
     (remove_mod (math_mod x q) || remove_mod (math_mod y q) || rewrite <- (plus_mod x y q))
  | math_mod (math_mod ?x q - math_mod ?y q)%Z q =>
     (remove_mod (math_mod x q) || remove_mod (math_mod y q) || rewrite <- (minus_mod x y q))
  | math_mod (math_mod ?x q * math_mod ?y q)%Z q => 
     (remove_mod (math_mod x q) || remove_mod (math_mod y q) || rewrite <- (mult_mod x y q)) 
  end.

Ltac rremove_mod :=
 repeat match goal with
 |- ?x = _ =>  match x with math_mod _ _ => remove_mod x end
 end.

Ltac simpl_mod := 
   match goal with
   |- math_mod ?x _ = _ => 
     push_mod x;
     rremove_mod
   end.

(* Why obligation from file "easycrypt2a3a01.why", line 488, characters 0-4631: *)
(*Why goal*) Lemma todo_in_coq3 : 
  (forall (U_172:Z),
   (forall (U'_171:Z),
    (forall (x_170:Z),
     (forall (y_169:Z),
      (forall (y1_168:Z),
       (forall (y2_167:Z),
        (forall (v_166:Z),
         (forall (pg_165:Z),
          (forall (Rd_164:Z),
           (0 <= U_172 ->
            (U_172 <= (q - 1) ->
             (0 <= U'_171 ->
              (U'_171 <= (q - 1) ->
               (0 <= Rd_164 ->
                (Rd_164 <= (q - 1) ->
                 (1 <= pg_165 ->
                  (pg_165 <= (q - 1) ->
                   (~U_172 = U'_171 ->
                    (math_mod
                     (((math_mod
                        (U_172 *
                        ((math_mod (x_170 - pg_165 * Rd_164) q) + v_166 *
                        (math_mod (y_169 - pg_165 * y2_167) q)) + pg_165 *
                        U'_171 * (Rd_164 + v_166 * y2_167)) q) -
                      U_172 * (x_170 + v_166 * y_169)) *
                     (inv_int_mod_q ((U'_171 - U_172) * pg_165)) - v_166 *
                     y2_167) q) =
                    Rd_164 /\
                    (math_mod
                     (U_172 *
                     ((math_mod
                       (x_170 - pg_165 *
                       (math_mod
                        ((Rd_164 - U_172 * (x_170 + v_166 * y_169)) *
                        (inv_int_mod_q ((U'_171 - U_172) * pg_165)) - v_166 *
                        y2_167) q)) q) +
                     v_166 * (math_mod (y_169 - pg_165 * y2_167) q)) +
                     pg_165 * U'_171 *
                     ((math_mod
                       ((Rd_164 - U_172 * (x_170 + v_166 * y_169)) *
                       (inv_int_mod_q ((U'_171 - U_172) * pg_165)) - v_166 *
                       y2_167) q) +
                     v_166 * y2_167)) q) =
                    Rd_164)))))))))))))))))).
Proof.
 intros.
 assert (W:= minus_mult_mod_0 _ _ _ H H0 H1 H2 H5 H6 H7).
 set (uu := ((U'_171 - U_172) * pg_165)).
 split;simpl_mod;simpl_mod.
 match goal with |- math_mod ?x _ = _ => 
   replace x with ((Rd_164 + v_166 * y2_167)*(inv_int_mod_q uu * uu) - v_166 * y2_167);
   [ | unfold uu;ring] end.
 rewrite minus_mod_idemp_l, mult_mod_idemp_r, inv_correct;auto.
 simpl_mod.
 match goal with |- math_mod ?x _ = _ => ring_simplify x end.
 auto using mod_small with zarith.
 set (ux:= (U_172 * (x_170 + v_166 * y_169))).
 match goal with |- math_mod ?x _ = _ => 
  replace x with ((Rd_164 - ux)*(inv_int_mod_q uu * uu) + ux);
  [ | unfold uu, ux;ring] end.
 rewrite plus_mod_idemp_l, mult_mod_idemp_r, inv_correct;auto.
 simpl_mod.
 match goal with |- math_mod ?x _ = _ => ring_simplify x end.
 auto using mod_small with zarith.
Save.

