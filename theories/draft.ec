(* Below is an "implementation" of an algebraic hierarchy. This seeks to illustrate
 what we would want to be able to achieve with type-classes in EasyCrypt
*)



(* A semigroup is a set A which supports a associative operation combine: A x A -> A *)
(* We want to allow for the application of axioms on generic type-classes*)
type 'a SemiGroup = {
  combine: 'a -> 'a -> 'a;
  (*law SemiGroupCombine (x y z: 'a) : combine( x (combine y z)) = combine(combine(x y) z)*)
}.
axiom nosmt SemiGroupCombine ['a] (s: 'a SemiGroup)(x y z: 'a): s.` combine x (s.`combine y z) = s.` combine (s.` combine x y) z.
(* A monoid can be considered a semigroup with an identity *)
(* We can consider extends to essentially copy the definition of semigroup into the target type-class,
 * to do so we need two assurances
 * - type parameters for the extendee are inferred from the target type-class parameters
 * - axioms and lemmas on the the extendee type-class hold for the target type-class (we inherit axioms and lemmas)
 * if done we have allowed for the instantiation of typeclasses through record types, and also for
 * inheritance of type-classes to build a hierarchy.
  *)
type 'a Monoid <: SemiGroup= {
  id: 'a;
  (*law MonoidAdd0L  (x: 'a) : combine(id x) = x.*)
  (*law MonoidAdd0R  (x: 'a) : combine(x id) = x.*)
}.

(*TODO: inheritance between typeclasses to allow this to compile*)
axiom nosmt MonoidAdd0L ['a] (m: 'a Monoid)(x: 'a) : m.` combine (m.` id) x = x.

(* TODO: instantiations of typeclasses*)
(* To instantiate a typeclass instance we need to be able to
 * specify operations of the type-class, and also the type parameters.
 *)
implicit type int Monoid where.
combine = (+).
id = 0.

lemma add0Comm (x:int) (m: int Monoid): m.` combine(x m.` id) = m.` combine (m.` id x).

(* We would also like allow for the compositionality of type-classes. i.e. a type-class
 * can inherit from two different typeclasses. I illustrate this expected behaviour with the
 * commutative monoid
  *)
(* TODO: multiple typeclass inheritance *)
type 'a CommutativeSemiGroup <: SemiGroup {
  law CommutativeAdd (x y: 'a): combine x y = combine y x;
}

type 'a CommutativeMonoid <: Monoid :+: CommutativeSemiGroup {
  (*law CommutativeId (x: 'a): combine x id = combine id x*)
  (*trivially the above law shouldn't need to be stated as it arises from the law of identity and commutative add *)
}.

(* We would also like there to be no conflicts between inheriting from different classes,
 * i.e the following shouldn't compile illustrating the diamond problem
 *)
(* TODO: conflict checking in inheritance *)
type 'a DummyGroup {
  combine: 'a -> 'a
}.

type 'a DummyGroup2 <: DummyGroup :+: SemiGroup {
  (* In scope there are two definitions of combine but they behave differently 
   * we don't want this to compile as we wouldn't be able to distinguish
   * between the partial application of a semigroup combine
   * and the application of a dummy-group combine
   *)
}.
