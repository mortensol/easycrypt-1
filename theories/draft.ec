(* Below is an "implementation" of an algebraic hierarchy. This seeks to illustrate
 what we would want to be able to achieve with type-classes in EasyCrypt
*)

require import Int.
  (* We want to allow for the application of axioms on generic type-classes*)
type class 'a SemiGroup = {
  op combine: 'a -> 'a -> 'a;
  axiom SemiGroupCombine(x y z: 'a):  combine x (combine y z) =  combine (combine x  y) z;
}.

lemma assocaddition(x y z: int): x + (y + z) = (x + y) + z.
    proof.
      simplify.
      
    qed.
instance intsg with int SemiGroup = {
  op combine = Int.(+);
  realize SemiGroupCombine = assocaddition;
}.


    (*TODO: Need to implement a one-to-one mapping of type class parameters i.e. 'a -> int*)
lemma semigroupAssociation (x y z: int): combine x (combine y z) = combine (combine x y) z.
    proof.
     apply SemiGroupCombine. (* Shouldn't this work? *)
    qed.
      (* Instance declaration of semi-group *)
(*op intSemiGroup: int SemiGroup = {|combine = Int.(+)|}.*)

(* A monoid can be considered a semigroup with an identity *)
(* We can consider extends to essentially copy the definition of semigroup into the target type-class,
 * to do so we need two assurances
 * - type parameters for the extendee are inferred from the target type-class parameters
 * - axioms and lemmas on the the extendee type-class hold for the target type-class (we inherit axioms and lemmas)
 * if done we have allowed for the instantiation of typeclasses through record types, and also for
 * inheritance of type-classes to build a hierarchy.
  *)

type class 'a Monoid extends 'a SemiGroup = {
  op id: 'a;
  axiom RightId: forall (x), combine x id = x;
  axiom LeftId: forall (x), combine id x = x;
}.

(* We would also like allow for the compositionality of type-classes. i.e. a type-class
 * can inherit from two different typeclasses. I illustrate this expected behaviour with the
 * commutative monoid
  *)
    (* TODO: multiple typeclass inheritance *)
type class 'a CommutativeSemiGroup extends 'a SemiGroup = {}.

(*axiom CommutativeSemiGroupAdd ['a] (cs: 'a CommutativeSemiGroup) (x y: 'a): cs.`combine x y = cs.`combine y x.*)

(*op intCommutativeSemiGroup: int CommutativeSemiGroup.*)
type class 'a CommutativeMonoid extends 'a CommutativeSemiGroup <+> 'a Monoid = {}.


(*op intCommutativeMonoid: int CommutativeMonoid = {|id = Int.zero; s=intCommutativeSemiGroup|}.*)

(* The following proof seeks tllustrate how type classes may be used in proofs *)
(*lemma IntCommutativeId:
    forall (x: int), intCommutativeMonoid.`s.`combine intCommutativeMonoid.`id x =  intCommutativeMonoid.`s.`combine x intCommutativeMonoid.`id.
    proof.
    move => x.
      rewrite MonoidAdd0L MonoidAdd0R.
      reflexivity.
  qed.*)

 
