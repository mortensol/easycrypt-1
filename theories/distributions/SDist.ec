require import AllCore List FSet Distr DProd StdBigop StdOrder.
(*---*) import Bigreal RealSeries RealOrder.

(* op sdist : 'a distr -> 'a distr -> real. *)

op flub (F : 'a -> real) : real = lub (fun r => exists a, F a = r).

lemma flub_sup r (F : 'a -> real) x : 
    (forall x, F x <= r) => F x <= flub F.
proof.
move => H. apply lub_upper_bound; 2: by exists x.
split; [by exists (F x) x|exists r => y [a] <-; exact H].
qed.

lemma ler_flub (F : 'a -> real) r :
    (forall x, F x <= r) => flub F <= r.
proof.
move => H. 
have ub_r : ub (fun (x : real) => exists (a : 'a), F a = x) r. 
  move => y [a] <-; exact H.
apply RealLub.lub_le_ub => //. 
split; [by exists (F witness) witness| by exists r].
qed.

op sdist (d1 d2 : 'a distr) = flub (fun E => `|mu d1 E - mu d2 E|).

lemma sdist_sup (d1 d2 : 'a distr) E : 
  `|mu d1 E - mu d2 E| <= sdist d1 d2.
proof.
apply (flub_sup 1%r (fun E => `|mu d1 E - mu d2 E|)).
move => {E} E /=; smt(mu_bounded).
qed.
 
lemma sdist_max (d1 d2 : 'a distr) r :
  (forall E, `|mu d1 E - mu d2 E| <= r) => sdist d1 d2 <= r .
proof. exact ler_flub. qed. 

lemma summable_cond p (s : 'a -> real) : 
  summable s => summable (fun x => if p x then s x else 0%r).
proof. 
case => r Hr; exists r => J uniJ; apply (ler_trans _ _ _ _ (Hr J uniJ)).
by apply ler_sum_seq => /=; smt().
qed.

lemma summableN (s : 'a -> real) : summable s => summable (fun x => - s x).
proof.
by move => sum_s; apply (summable_le _ _ sum_s) => /= a; rewrite normrN.
qed.

lemma norm_summable (s : 'a -> real) : summable (fun x => `|s x|) => summable s.
proof. 
move => sum_s; apply (summable_le _ _ sum_s) => /= a. 
by rewrite (ger0_norm `|s a|) ?normr_ge0.
qed.

lemma summable_mu1 (d : 'a distr) : summable (fun x => mu1 d x).
proof. 
rewrite (eq_summable _ (mass d)) /= => [x|]; 1: by rewrite massE.
exact summable_mass.
qed.

lemma summable_mu1_cond p (d : 'a distr) : 
  summable (fun x => if p x then mu1 d x else 0%r).
proof. exact/summable_cond/summable_mu1. qed.

lemma summable_sdist (d1 d2 : 'a distr) : 
  summable (fun x => `| mu1 d1 x - mu1 d2 x |).
proof. 
apply/summable_norm/summableD; 1: exact/summable_mu1. 
exact/summableN/summable_mu1.
qed.

lemma muE1 (d : 'a distr) E : mu d E = sum (fun x => if E x then mu1 d x else 0%r).
proof. by rewrite muE; apply eq_sum => x /=; rewrite massE. qed.

lemma weightE (d : 'a distr) : weight d = sum (fun x => mu1 d x).
proof. by rewrite muE1. qed.

lemma sdist_sumE (d1 d2 : 'a distr) : 
    weight d1 = weight d2 =>
    sdist d1 d2 = 1%r/2%r * sum (fun x => `| mu1 d1 x - mu1 d2 x |).
proof.
rewrite /sdist => w_d1_d2.
pose F E := `|mu d1 E - mu d2 E|; pose f x := `|mu1 d1 x - mu1 d2 x|.
have sum_f : summable f by apply summable_sdist.
pose pos x := mu1 d1 x >= mu1 d2 x.
pose Sp := sum (fun x => if pos x then f x else 0%r).
pose Sn := sum (fun x => if !pos x then f x else 0%r).
rewrite (sum_split _ pos) // -/Sp -/Sn.
have eq_p_n : Sp = Sn. 
  rewrite /Sp /Sn /f.
  rewrite (eq_sum _ (fun x => (if pos x then mu1 d1 x else 0%r) - (if pos x then mu1 d2 x else 0%r))).
    smt().
  rewrite sumB; 1,2 : exact summable_mu1_cond.
  rewrite (eq_sum (fun x => if !pos x then `|mu1 d1 x - mu1 d2 x| else 0%r) 
                  (fun x => (if ! pos x then mu1 d2 x else 0%r) - (if !pos x then mu1 d1 x else 0%r))).
    smt().
  rewrite sumB /=; 1,2: exact summable_mu1_cond.
  rewrite RField.eqr_sub -!sum_split; 1,2: exact summable_mu1.
  by rewrite -!weightE.
suff : flub F = Sp by smt().
apply ler_anti; split => [|_]; last first. 
- apply (ler_trans (F pos)); 2: by apply (flub_sup 1%r); smt(mu_bounded).
  rewrite /Sp /F /f !muE1 -sumB /=; 1,2: exact summable_mu1_cond.
  apply (ler_trans _ _ _ _ (ler_norm _)). 
  apply ler_sum; [smt()|apply/summable_cond/summable_sdist|].
  by apply/summableD;[|apply/summableN]; apply/summable_mu1_cond.
apply sdist_max => E.
rewrite (mu_split d1 E pos) (mu_split d2 E pos). 
have -> : mu d1 (predI E pos) + mu d1 (predI E (predC pos)) - 
          (mu d2 (predI E pos) + mu d2 (predI E (predC pos))) = 
          (mu d1 (predI E pos) - (mu d2 (predI E pos))) + 
          (mu d1 (predI E (predC pos)) - (mu d2 (predI E (predC pos)))) by smt().
rewrite !muE1 -!sumB /=; 1..4: exact: summable_mu1_cond.
rewrite (eq_sum _ (fun x => if predI E pos x then mu1 d1 x - mu1 d2 x else 0%r)); 1: smt().
rewrite (eq_sum 
  (fun (x : 'a) => (if predI E (predC pos) x then mu1 d1 x else 0%r) - 
                   if predI E (predC pos) x then mu1 d2 x else 0%r)
  (fun x => if predI E (predC pos) x then mu1 d1 x - mu1 d2 x else 0%r)); 1: smt().
pose SEp := sum (fun (x : 'a) => if predI E pos x then mu1 d1 x - mu1 d2 x else 0%r).
pose SEn := sum (fun (x : 'a) => if predI E (predC pos) x then mu1 d1 x - mu1 d2 x else 0%r).
have ? : 0%r <= SEp /\ SEn <= 0%r. 
  split; 1: by apply ge0_sum; smt().
  apply/oppr_ge0. rewrite -sumN /=. by apply ge0_sum; smt().
suff : maxr SEp (-SEn) <= Sp by smt().
apply/ler_maxrP; split. 
- (apply ler_sum; 1: smt()); 2: exact/summable_cond.
  exact/summable_cond/norm_summable/summable_sdist.
rewrite eq_p_n -sumN; (apply ler_sum; 1: smt()); 2: exact/summable_cond.
exact/summableN/summable_cond/norm_summable/summable_sdist.
qed.

lemma sdist_ge0 (d1 d2 : 'a distr) : 0%r <= sdist d1 d2.
admitted.

lemma sum_swap' (s : 'a -> 'b -> real) :
  summable (fun p : 'a * 'b => s p.`1 p.`2) => 
  sum (fun (a : 'a) => sum (fun (b : 'b) => s a b)) = 
  sum (fun (b : 'b) => sum (fun (a : 'a) => s a b)).
proof. exact (sum_swap (fun (ab : 'a * 'b) => s ab.`1 ab.`2)). qed.

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
