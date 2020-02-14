(* Below is an "implementation" of an algebraic hierarchy. This seeks to illustrate
 what we would want to be able to achieve with type-classes in EasyCrypt
 *)

(* A semigroup is a set A which supports a associative operation combine: A x A -> A *)
type 'a semigroup = {
  combine: 'a -> 'a -> 'a;
  law SemiGroupCombine (x y z: 'a) : Self.combine( x (Self.combine y z)) = Self.combine(Self.combine(x y) z).
}.

(* We want to allow for the application of axioms on generic type-classes*)

(* A monoid can be considered a semigroup with an identity *)
(* We can consider extends to essentially copy the definition of semigroup into the target type-class,
 * to do so we need two assurances
 * - type parameters for the extendee are inferred from the target type-class parameters
 * - axioms and lemmas on the the extendee type-class hold for the target type-class (we inherit axioms and lemmas)
 * if done we have allowed for the instantiation of typeclasses through record types, and also for
 * inheritance of type-classes to build a hierarchy.
 *)
type 'a monoid <: semigroup{
  id: 'a;
  law MonoidAdd0L  (x: 'a) : Self.combine(Self.id x) = x.
  law MonoidAdd0R  (x: 'a) : Self.combine(x Self.id) = x.
}.

(* To instantiate a typeclass instance we need to be able to
 * specify operations of the type-class, and also the type parameters.
  *)
type int monoid where.
combine = (+).
id = 0.
