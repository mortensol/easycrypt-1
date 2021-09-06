require import AllCore List FSet Distr DProd StdBigop.
(*---*) import Bigreal Bigreal.BRM MUnit.

op sdist : 'a distr -> 'a distr -> real.

axiom sdist_sup : forall (d1 d2 : 'a distr) E, 
  `|mu d1 E - mu d2 E| <= sdist d1 d2.

axiom sdist_max : forall (d1 d2 : 'a distr) r,  
  (forall E, `|mu d1 E - mu d2 E| <= r) => sdist d1 d2 <= r .


lemma sdist_ge0 (d1 d2 : 'a distr) : 0%r <= sdist d1 d2.
admitted.

lemma sdist_dlet (d1 d2 : 'a distr) (F : 'a -> 'b distr) : 
 sdist (dlet d1 F) (dlet d2 F) <= sdist d1 d2.
proof.
apply sdist_max => E. (* what to do here? *)
admitted.

theory T.

type a.
op d1, d2 : a distr.

module type Distinguisher = { 
  proc guess (x : a) : bool
}.

module Sample (A : Distinguisher) = { 
  proc main(b : bool) = {
    var x,r;
    x <- witness;
    if (!b) { x <$ d1; }
    if (b)  { x <$ d2; }
    r <@ A.guess(x);
    return r;
  }
}.

(* Justified by semantic argument using sdist_dlet *)
axiom foo (A <: Distinguisher) &m : 
  `| Pr[Sample(A).main(false) @ &m : res] - Pr[Sample(A).main(true) @ &m : res] | <=  sdist d1 d2.


