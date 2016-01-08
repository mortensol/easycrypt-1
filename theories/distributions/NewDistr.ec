(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Option Pred Fun List Int IntExtra Real RealExtra.
require import StdRing StdOrder StdBigop Discrete RealSeq RealSeries.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField NewLogic.
require (*--*) FinType.

pragma +implicits.

(* -------------------------------------------------------------------- *)
(* We currently bind old distr/mu_x et al to the new constructs         *)
require export Distr.

type 'a distr = 'a Pervasive.distr.

axiom muE ['a] (d : 'a distr) (E : 'a -> bool):
  mu d E = sum (fun x => if E x then mu_x d x else 0%r).

(* -------------------------------------------------------------------- *)
op mk : ('a -> real) -> 'a distr.

op isdistr (m : 'a -> real) =
     (forall x, 0%r <= m x)
  /\ (forall s, uniq s => big predT m s <= 1%r).

axiom distrW (P : 'a distr -> bool):
  (forall m, isdistr m => P (mk m)) => forall d, P d.

axiom muK (m : 'a -> real): isdistr m => mu_x (mk m) = m.
axiom mkK (d : 'a distr): mk (mu_x d) = d.

lemma ge0_mu_x ['a] (d : 'a distr) (x : 'a):
  0%r <= mu_x d x.
proof. by elim/distrW: d x => m dm; rewrite muK //; case: dm. qed.

lemma le1_mu_x ['a] (d : 'a distr) :
  forall (s : 'a list), uniq s => big predT (mu_x d) s <= 1%r.
proof. by elim/distrW: d => m dm; rewrite muK //; case: dm. qed.

lemma summable_mu_x ['a] (d : 'a distr) : summable (mu_x d).
proof.
exists 1%r=> s eq_s; rewrite (@eq_bigr _ _ (mu_x d)) => /=.
  by move=> i _; rewrite ger0_norm // ge0_mu_x.
by apply/le1_mu_x.
qed.

lemma ge0_weight ['a] (d : 'a distr) : 0%r <= weight d.
proof. admit. qed.

lemma countable_mu ['a] (d : 'a distr):
  countable (fun x => mu_x d x <> 0%r).
proof. by apply/sbl_countable/summable_mu_x. qed.

lemma eq_distr (d1 d2 : 'a distr):
  (d1 = d2) <=> (forall x, mu_x d1 x = mu_x d2 x).
proof.
split=> [->//|eq_mu]; rewrite -(@mkK d1) -(@mkK d2).
by congr; apply/fun_ext.
qed.

(* -------------------------------------------------------------------- *)
op mnull ['a] = fun  (x : 'a) => 0%r.
op dnull ['a] = mk mnull<:'a>.

lemma isdistr_mnull ['a] : isdistr mnull<:'a>.
proof. by split=> //= s _; rewrite Bigreal.sumr_const mulr0. qed.

lemma dnull1E ['a] : forall x, mu_x dnull<:'a> x = 0%r.
proof. by move=> x; rewrite muK //; apply/isdistr_mnull. qed.

lemma dnullE ['a] (E : 'a -> bool) : mu dnull<:'a> E = 0%r.
proof.
rewrite muE -(@eq_sum (fun x=> 0%r) _ _).
+ by move=> x /=; rewrite dnull1E if_same.
admit.
qed.

lemma weight_dnumm ['a] : weight dnull<:'a> = 0%r.
proof. by apply/dnullE. qed.

lemma supnullE ['a] : support dnull<:'a> = pred0.
proof. by apply/fun_ext=> x; rewrite /support /in_supp dnull1E. qed.

(* -------------------------------------------------------------------- *)
theory MRat.
op mrat ['a] (s : 'a list) =
  fun x => (count (pred1 x) s)%r / (size s)%r.

lemma isdistr_drat (s : 'a list) : isdistr (mrat s).
proof.
rewrite /mrat; split=> /= [x|J uq_J].
  by rewrite divr_ge0 // from_intMle ?(count_ge0, size_ge0).
rewrite -divr_suml -sumr_ofint. admit.
qed.

op drat ['a] (s : 'a list) = mk (mrat s).

lemma dratE ['a] (s : 'a list) (x : 'a):
  mu_x (drat s) x = (count (pred1 x) s)%r / (size s)%r.
proof. by rewrite muK // isdistr_drat. qed.

lemma prratE ['a] (s : 'a list) (E : 'a -> bool) :
  mu (drat s) E = (count E s)%r / (size s)%r.
proof.
rewrite muE (@sumE_fin _ (undup s)) ?undup_uniq //=.
  move=> x; case: (E x)=> _ //; rewrite dratE.
  rewrite divrE mulf_eq0 -nor mem_undup from_intMeq => -[+ _].
  by rewrite -lt0n ?count_ge0 // -has_count has_pred1.
pose F := fun x => (count (pred1 x) s)%r / (size s)%r.
rewrite -big_mkcond (@eq_bigr _ _ F) /F /= => {F}.
  by move=> i _; rewrite dratE.
by rewrite -size_filter -divr_suml -sumr_ofint big_count.
qed.

lemma support_drat ['a] (s : 'a list) : support (drat s) = mem s.
proof.
apply/fun_ext=> x; rewrite /support /in_supp dratE.
rewrite divrE eq_iff -has_pred1 has_count.
case: (count (pred1 x) s <= 0); [smt w=count_ge0|].
move=> /IntOrder.ltrNge ^ + -> /=; rewrite -from_intM; case: s=> //=.
move=> ? s /(@mulr_gt0 _ (inv (1 + size s)%r)) -> //.
by rewrite invr_gt0 from_intM [smt w=size_ge0].
qed.

lemma eq_dratP ['a] (s1 s2 : 'a list) :
  (perm_eq s1 s2) <=> (drat s1 = drat s2).
proof. admit. qed.

lemma drat_ll ['a] (s : 'a list) :
  s <> [] => mu (drat s) predT = 1%r.
proof.
move=> nz_s; rewrite prratE count_predT divrr //.
by rewrite from_intMeq size_eq0.
qed.
end MRat.

(* --------------------------------------------------------------------- *)
theory MUnit.
op dunit ['a] (x : 'a) = MRat.drat [x].

lemma dunit1E ['a] (x y : 'a):
  mu_x (dunit x) y = if x = y then 1%r else 0%r.
proof. by rewrite MRat.dratE /= /pred1; case: (x = y). qed.

lemma dunit1xx ['a] (x : 'a): mu_x (dunit x) x = 1%r.
proof. by rewrite dunit1E. qed.

lemma dunitE ['a] (E : 'a -> bool) (x : 'a):
  mu (dunit x) E = if E x then 1%r else 0%r.
proof. by rewrite MRat.prratE /=; case: (E x). qed.

lemma dunit_ll ['a] (x : 'a): mu (dunit x) predT = 1%r.
proof. by apply/MRat.drat_ll. qed.

lemma support_dunit ['a] (x : 'a): support (dunit x) = pred1 x.
proof. by apply/fun_ext=> x'; rewrite MRat.support_drat. qed.
end MUnit.

(* -------------------------------------------------------------------- *)
theory MUniform.
op duniform ['a] (s : 'a list) = MRat.drat (undup s).

lemma duniform1E ['a] (s : 'a list) x :
  mu_x (duniform s) x = if mem s x then 1%r / (size (undup s))%r else 0%r.
proof.
rewrite MRat.dratE count_uniq_mem ?undup_uniq // mem_undup.
by case: (mem s x)=> //=; rewrite divrE mul0r.
qed.

lemma eq_duniformP ['a] (s1 s2 : 'a list) :
     (forall x, mem s1 x <=> mem s2 x)
 <=> (duniform s1 = duniform s2).
proof.
rewrite -MRat.eq_dratP; split=> h.
  apply/uniq_perm_eq; rewrite ?undup_uniq=> //.
  by move=> x; rewrite !mem_undup; apply/h.
move=> x; rewrite -(@mem_undup s1) -(@mem_undup s2).
by apply/perm_eq_mem.
qed.

lemma duniformE ['a] (E : 'a -> bool) (s : 'a list) :
  mu (duniform s) E = (count E (undup s))%r / (size (undup s))%r.
proof. by apply/MRat.prratE. qed.

lemma support_duniform ['a] (s : 'a list): support (duniform s) = mem s.
proof. by rewrite MRat.support_drat pred_ext=>x; rewrite mem_undup. qed.

lemma duniform_ll (s : 'a list) :
  s <> [] => is_lossless (duniform s).
proof. by move=> nz_s; apply/MRat.drat_ll; rewrite undup_nilp. qed.

lemma duniform_uf (s : 'a list) :
  s <> [] => is_uniform (duniform s).
proof.
move=> s_ne0; rewrite /is_uniform duniform_ll //=.
by move=> x y; rewrite 2!duniform1E support_duniform=> !->.
qed.
end MUniform.

(* -------------------------------------------------------------------- *)
theory MIntUniform.
op drange (m n : int) = MUniform.duniform (range m n).

lemma drange1E (m n x : int):
  mu_x (drange m n) x = if m <= x < n then 1%r / (n - m)%r else 0%r.
proof.
rewrite MUniform.duniform1E mem_range undup_id 1:range_uniq //.
rewrite size_range; case: (m <= x < n) => // -[le_mx lt_xn].
rewrite max_ler // IntOrder.subr_ge0 IntOrder.ltrW //.
by apply (IntOrder.ler_lt_trans _ le_mx).
qed.

lemma drangeE (E : int -> bool) (m n : int) :
  mu (drange m n) E = (count E (range m n))%r / (n - m)%r.
proof.
rewrite MUniform.duniformE undup_id 1:range_uniq //.
rewrite size_range; case: (lezWP n m) => [le_nm|le_mn].
  by rewrite max_lel // 1:subr_le0 // range_geq // !divrE.
by rewrite max_ler // subr_ge0 ltrW // ltzNge.
qed.

lemma support_drange (m n i : int): support (drange m n) i <=> m <= i < n.
proof. by rewrite MRat.support_drat undup_id ?range_uniq mem_range. qed.
end MIntUniform.

(* -------------------------------------------------------------------- *)
op mlet ['a 'b] (f : 'a -> 'b distr) (d : 'a distr) =
  fun (y : 'b) => sum<:'a> (fun x => mu_x d x * mu_x (f x) y).

op dlet ['a 'b] (f : 'a -> 'b distr) (d : 'a distr) =
  mk (mlet f d).

lemma isdisrtr_mlet ['a 'b] (f : 'a -> 'b distr) (d : 'a distr) :
  isdistr (mlet f d).
proof. admit. qed.

(* -------------------------------------------------------------------- *)
op dprod ['a 'b] (d1 : 'a distr) (d2 : 'b distr) =
  dlet (fun x => d2) d1.

(* -------------------------------------------------------------------- *)
op mscale ['a] (d : 'a distr) =
  fun x => mu_x d x / weight d.

op dscale ['a] (d : 'a distr) =
  mk (mscale d).

lemma isdistr_mscale (d : 'a distr) : isdistr (mscale d).
proof.
split=> @/mscale [x|s uqs].
  by rewrite divr_ge0 1:ge0_mu_x // ge0_weight.
rewrite -divr_suml; apply/(@ler_trans (weight d / weight d)).
  rewrite 2!divrE ler_wpmul2r // ?invr_ge0 ?ge0_weight //.
  admit.
have := ge0_weight d; rewrite ler_eqVlt => -[<-|gt0_iw].
  by rewrite divr0. by rewrite divrr // gtr_eqF.
qed.

(* -------------------------------------------------------------------- *)
abstract theory MFinite.
type t.

clone import FinType as Support with type t <- t.

op duniform : t distr = MUniform.duniform enum.

lemma duniform1E (x : t) : mu_x duniform x = 1%r / (size enum)%r.
proof. by rewrite MUniform.duniform1E enumP /= undup_id // enum_uniq. qed.

lemma duniformE (E : t -> bool) :
  mu duniform E = (count E enum)%r / (size enum)%r.
proof. by rewrite MUniform.duniformE ?undup_id // enum_uniq. qed.

lemma support_duniform: support duniform = predT.
proof.
by rewrite MUniform.support_duniform pred_ext=> x; rewrite enumP.
qed.
end MFinite.
