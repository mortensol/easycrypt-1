(* Below is an "implementation" of an algebraic hierarchy. This seeks to illustrate
 what we would want to be able to achieve with type-classes in EasyCrypt
*)

require import Int.
  (* We want to allow for the application of axioms on generic type-classes*)
type class 'a SemiGroup = {
  op combine: 'a -> 'a -> 'a;
  axiom combineassoc(x y z: 'a):  combine x (combine y z) =  combine (combine x  y) z;
}.

axiom assocaddition(x y z: int):  x + ( y + z) =  x + y + z.
instance intsg with int SemiGroup = {
  op combine = Int.(+);
  lemma combineassoc SemiGroup by apply assocaddition
}.

lemma semigroupAssociation (x y z: int): combine x (combine y z) = combine (combine x y) z.
    proof.
      apply intsg_combineassoc. 
    qed.

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
  axiom rightid(x: 'a): combine x id = x;
  axiom leftid(x: 'a) : combine id x = x;
}.

lemma intidr(x: int): x + 0 = x by simplify.
lemma intidl(x: int): 0 + x = x by simplify.
instance intmonoid with int monoid = {
  op id = Int.zero;
  lemma rightid Monoid by apply intidr 
  lemma leftid Monoid by apply intidl
}

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

 
