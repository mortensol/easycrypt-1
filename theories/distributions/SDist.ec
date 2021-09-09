require import AllCore List FSet Distr DProd StdBigop StdOrder.
(*---*) import Bigreal RealSeries RealOrder.

op sdist : 'a distr -> 'a distr -> real.

axiom sdist_sup : forall (d1 d2 : 'a distr) E, 
  `|mu d1 E - mu d2 E| <= sdist d1 d2.

axiom sdist_max : forall (d1 d2 : 'a distr) r,  
  (forall E, `|mu d1 E - mu d2 E| <= r) => sdist d1 d2 <= r .

lemma sdist_sumE (d1 d2 : 'a distr) : 
    sdist d1 d2 = 1%r/2%r * sum (fun x => `| mu1 d1 x - mu1 d2 x |).
admitted.

lemma sdist_ge0 (d1 d2 : 'a distr) : 0%r <= sdist d1 d2.
admitted.

lemma sum_swap' (s : 'a -> 'b -> real) :
  summable (fun p : 'a * 'b => s p.`1 p.`2) => 
  sum (fun (a : 'a) => sum (fun (b : 'b) => s a b)) = 
  sum (fun (b : 'b) => sum (fun (a : 'a) => s a b)).
admitted.

lemma summable_pswap (s : 'a * 'b -> real) : summable s <=> summable (s \o pswap).
proof.
split => [|H]; 1: exact summable_pswap.
have -> : s = (s \o pswap) \o pswap by apply/fun_ext => -[].
exact summable_pswap.
qed.

lemma dletE (d : 'a distr) (F : 'a -> 'b distr) (E : 'b -> bool) : 
  mu (dlet d F) E = sum (fun x => mu1 d x * mu (F x) E).
proof.
rewrite dletE sum_swap' /=. 
  apply summable_cond; apply summable_pswap.
  rewrite (eq_summable _ 
     (fun (ab : 'a * 'b) => mass d ab.`1 * mass (F ab.`1) ab.`2)) //.
  apply summable_dlet. 
apply eq_sum => a /=; rewrite (muE _ E) -sumZ /= !massE.
apply eq_sum => b /=; smt().
qed.

lemma sdist_dlet (d1 d2 : 'a distr) (F : 'a -> 'b distr) : 
   sdist (dlet d1 F) (dlet d2 F) <= sdist d1 d2.
proof.
have s_dlet : forall E d, summable (fun (x : 'a) => mu1 d x * mu (F x) E).
  admit.
apply sdist_max => E; rewrite !dletE -sumB /=; 1,2: exact s_dlet. 
rewrite (eq_sum _ (fun (x : 'a) => (mu1 d1 x - mu1 d2 x) * mu (F x) E)) 1:/#.
apply (ler_trans `|sum (fun (x : 'a) => mu1 d1 x - mu1 d2 x) |).
  (* 0 <= mu (F x) E <= 1 *) admit.
rewrite sumB; 1,2: exact summable_mu1.
rewrite (eq_sum _ (fun x => if predT x then mass d1 x else 0%r)) -?muE.
  by move => x /=; rewrite massE /predT.
rewrite (eq_sum _ (fun x => if predT x then mass d2 x else 0%r)) -?muE.
  by move => x /=; rewrite massE /predT.
exact sdist_sup.
qed.

lemma sdist_dprod2r (d1 d2 d : 'a distr) : 
 sdist (d1 `*` d) (d2 `*` d) = sdist d1 d2 * weight d.
proof.
rewrite !dprod_dlet. 
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
