(* -------------------------------------------------------------------- *)
require import AllCore List IntMin IntDiv.
require import FinType FSet.
require (*--*) Ring Number StdOrder ZModP.

import Ring.IntID StdOrder.IntOrder.

(* -------------------------------------------------------------------- *)

op injective_on (A : 'a fset) (f : 'a -> 'b) : bool =
  forall (x y : 'a), x \in A => y \in A => f x = f y => x = y.

abstract theory NominalGroup.

type G.
type Z.

clone include FinType
  with type t <- G
  rename "card" as "order"
  rename "enum" as "elems".

op g     : G.
op ( ^ ) : G -> Z -> G.

op ( * ) : Z -> Z -> Z.
op inv   : Z -> Z.

op f : Z.
op exp (a, x) = a ^ (x * inv f).

op EU : Z fset.
op dZ : Z distr.

axiom mulA       : associative ( * ).
axiom mulC       : commutative ( * ).

axiom powM       : forall a x y, a ^ (x * y) = (a ^ x) ^ y.
axiom pow_inv    : forall x, x \in EU => g ^ (x * inv x) = g.
axiom pow_inv_f  : forall a, a ^ (f * inv f) = a.

axiom exp_inj    : injective_on EU (exp g).
axiom exp_inj'   : forall x, injective_on EU (fun z => exp g (x * z)).

axiom img_exp    : forall x, x \in EU =>
                             image (fun z => exp g (x * z)) EU =
                             image (exp g) EU.

lemma expM a x y : exp a (x * y) = (exp a x) ^ y.
proof. by rewrite /exp -!powM -!mulA (mulC y). qed.

lemma exp_inv x y : x \in EU => exp g (x * inv x * y) = exp g y.
proof.
move => x_EU; rewrite /exp.
have -> : x * inv x * y * inv f = (x * inv x) * (y * inv f) by smt(mulA mulC).
by rewrite powM pow_inv.
qed.

(* to remove *)
axiom Emult x y  : x \in EU => y \in EU => x * y \in EU.
axiom Einv x     : x \in EU => inv x \in EU.

lemma invK a x   : a \in EU => x \in EU => a * x * inv x = a.
proof.
move => aE bE; apply: exp_inj => //; last smt(mulA mulC powM pow_inv).
apply: Emult => //; [by apply: Emult | by exact: Einv].
qed.

lemma invK' a x   : a \in EU => x \in EU => a * inv x * x = a.
proof. by rewrite -mulA (mulC _ x) mulA; exact: invK. qed.


end NominalGroup.
