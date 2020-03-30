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
type class 'a Monoid = {
  op id: 'a;
  axiom rightid(x: 'a): combine x id = x;
  axiom leftid(x: 'a) : combine id x = x;
}.

lemma intidr(x: int): x + 0 = x by simplify.
lemma intidl(x: int): 0 + x = x by simplify.
instance intm with int Monoid = {
  op id = Int.zero;
  lemma rightid Monoid by apply intidr
  lemma leftid Monoid by apply intidl
}.

lemma idcomm (x: int): combine id x = combine x id.
    proof.
      rewrite intm_rightid.
      rewrite intm_leftid.
      reflexivity.
    qed.
