require import AllCore List Distr DBool DInterval DList.
require import FinType FSet SmtMap NominalGroup.

import Distr.MRat.
import DBool.Biased.
import StdOrder.RealOrder.
import RField.

(* preliminaries , move elsewhere *)

lemma inj_card_image (f : 'a -> 'b) (A : 'a fset) :
    injective f => card (image f A) = card A.
proof.
move => inj_f.
have/oflist_uniq uniq_f : uniq (map f (elems A)).
  apply map_inj_in_uniq; 2: exact uniq_elems; move => x y _ _; exact inj_f.
by rewrite /image /card -(perm_eq_size _ _ uniq_f) size_map.
qed.

(** theory of [mapi] *)
op mapi_rec (f : int -> 'a -> 'b) (xs : 'a list) (i : int) =
 with xs = [] => []
 with xs = x::xs => f i x :: mapi_rec f xs (i+1).

op mapi (f : int -> 'a -> 'b) (xs : 'a list) = mapi_rec f xs 0.

lemma mapiK (f : int -> 'a -> 'b) (g : int -> 'b -> 'a) :
    (forall i, cancel (g i) (f i)) => cancel (mapi g) (mapi f).
proof. move => can_f xs; rewrite /mapi; elim: xs 0 => //=; smt(). qed.

lemma in_mapiK (f : int -> 'a -> 'b) (g : int -> 'b -> 'a) (xs : 'a list) :
    (forall i x, x \in xs => 0 <= i && i < size xs => g i (f i x) = x) => mapi g (mapi f xs) = xs.
proof.
move => H.
have {H} : forall i x, x \in xs => 0 <= i && i < (0 + size xs) => g (i) (f (i) x) = x; 1: by [].
rewrite /mapi; move: (0) => k. elim: xs k => //= x xs IHxs k Hk.
split; 1: by rewrite Hk; smt(size_ge0).
apply IHxs; smt(size_ge0).
qed.

lemma size_mapi (f : int -> 'a -> 'b) (xs : 'a list) : size (mapi f xs) = size xs.
proof. rewrite /mapi. elim: xs 0 => //= xs IHxs n. by rewrite IHxs. qed.

lemma nth_mapi_rec x1 (s : 'a list) x2 (f : int -> 'a -> 'b) n m :
    0 <= n && n < size s =>
    nth x2 (mapi_rec f s m) n = f (m + n) (nth x1 s n).
proof. by elim: s n m => /= [|x s IHs]; smt(). qed.

lemma nth_mapi x1 (s : 'a list) x2 (f : int -> 'a -> 'b) n : 0 <= n && n < size s =>
    nth x2 (mapi f s) n = f n (nth x1 s n).
proof. exact: nth_mapi_rec. qed.

lemma mapi_recP x0 (f : int -> 'a -> 'b) (s : 'a list) y m :
    y \in mapi_rec f s m <=> exists n, (0 <= n && n < size s) /\ y = f (n+m) (nth x0 s n).
proof. elim: s m; smt(size_ge0). qed.

lemma mapiP x0 (f : int -> 'a -> 'b) (s : 'a list) y :
    y \in mapi f s <=> exists n, (0 <= n && n < size s) /\ y = f n (nth x0 s n).
proof. exact: mapi_recP. qed.

(* variant of [dlist_fu] whose conclusion is a linear pattern *)
lemma dlist_fu_eq (d : 'a distr) (xs : 'a list) n :
   n = size xs => (forall (x : 'a), x \in xs => x \in d) => xs \in dlist d n.
proof. move => ->. exact: dlist_fu. qed.


lemma muT (d : 'a distr) (p : 'a -> bool) : p == predT => mu d p = weight d.
proof. by move/fun_ext => ->. qed.

require import StdBigop.
(*---*) import IterOp Bigint Bigreal Bigreal.BRM.

(* local copy of new DList lemma: remove *)
lemma dlistSr (d : 'a distr) (n : int) : 0 <= n =>
  dlist d (n + 1) = dapply (fun (xy : 'a list * 'a) => rcons xy.`1 xy.`2) (dlist d n `*` d).
admitted.

lemma dlistE x0 (d : 'a distr) (p : int -> 'a -> bool) n :
    mu (dlist d n) (fun xs : 'a list => forall i, (0 <= i) && (i < n) => (p i (nth x0 xs i)))
  = bigi (fun _ => true) (fun i => mu d (p i)) 0 n.
proof.
elim/natind : n p => [n n_le0|n n_ge0 IHn] p.
- rewrite dlist0 // dunitE range_geq //= big_nil; smt().
rewrite rangeSr // -cats1 big_cat big_seq1.
rewrite dlistSr //= dmapE.
pose P1 xs := forall i, 0 <= i && i < n => p i (nth x0 xs i).
pose P2 x := p n x.
pose P (a : 'a list * 'a) := P1 a.`1 /\ P2 a.`2.
rewrite (mu_eq_support _ _ P); 2: by rewrite dprodE IHn.
case => xs x /=. rewrite supp_dprod /= supp_dlist // => -[[? ?] ?].
rewrite /(\o) /P /P1 /P2 /= eq_iff; subst n; split; 2: smt(nth_rcons).
move => H; split => [i|];[have := (H i)|have := H (size xs)]; smt(nth_rcons).
qed.

(* 0 <= n could be removed, but applying the lemma is pointless in that case *)
lemma dlist_set2E x0 (d : 'a distr) (p : 'a -> bool) n (I J : int fset) :
  is_lossless d => 0 <= n =>
  (forall i, i \in I => 0 <= i && i < n) =>
  (forall j, j \in J => 0 <= j && j < n) =>
  (forall k, !(k \in I /\ k \in J)) =>
  mu (dlist d n)
     (fun xs => (forall i, i \in I => p (nth x0 xs i)) /\
                (forall j, j \in J => !p (nth x0 xs j)))
  = (mu d p)^(card I) * (mu d (predC p))^(card J).
proof.
move => d_ll n_ge0 I_range J_range disjIJ.
pose q i x := (i \in I => p x) /\ (i \in J => !p x).
rewrite (mu_eq_support _ _
  (fun xs => forall i, (0 <= i) && (i < n) => q i (nth x0 xs i))); 1: smt(supp_dlist).
rewrite dlistE (bigEM (mem (I `|` J))).
rewrite (big1 (predC (mem (I `|` J)))) ?mulr1.
  move => i; rewrite /predC in_fsetU negb_or /= /q => -[iNI iNJ].
  rewrite (mu_eq _ _ predT) 1:/# //.
rewrite -big_filter (eq_big_perm _ _ _ (elems I ++ elems J)) ?big_cat.
- apply uniq_perm_eq => [| |x].
  + by rewrite filter_uniq range_uniq.
  + rewrite cat_uniq !uniq_elems => />; apply/hasPn; smt().
  + by rewrite mem_filter mem_range mem_cat -!memE in_fsetU /#.
rewrite big_seq_cond (eq_bigr _ _ (fun _ => mu d p)) -?big_seq_cond.
  move => i; rewrite /= /q -memE => -[iI _]; apply mu_eq => /#.
rewrite mulr_const big_seq_cond (eq_bigr _ _ (fun _ => mu d (predC p))) -?big_seq_cond.
  move => i; rewrite /= /q -memE => -[iI _]; apply mu_eq => /#.
by rewrite mulr_const /card.
qed.

lemma dlist_setE x0 (d : 'a distr) (p : 'a -> bool) n (I : int fset) :
  is_lossless d => 0 <= n => (forall i, i \in I => 0 <= i && i < n) =>
  mu (dlist d n) (fun xs => forall i, i \in I => p (nth x0 xs i)) = (mu d p)^(card I).
proof.
move => d_ll n_ge0 hI.
have := dlist_set2E x0 d p n I fset0 d_ll n_ge0 hI _ _; 1,2 : smt(in_fset0).
rewrite fcards0 expr0 mulr1 => <-.
apply: mu_eq_support => xs; rewrite supp_dlist //= => -[? ?]; smt(in_fset0).
qed.

lemma dlist_nthE x0 (d : 'a distr) (p : 'a -> bool) i n :
  is_lossless d => 0 <= i && i < n =>
  mu (dlist d n) (fun xs => p (nth x0 xs i)) = mu d p.
proof.
move => d_ll Hn.
have E := dlist_setE x0 d p n (fset1 i) d_ll _ _; 1,2: smt(in_fset1).
rewrite (mu_eq _ _ (fun (xs : 'a list) => forall (i0 : int), i0 \in fset1 i => p (nth x0 xs i0))).
  smt(in_fset1).
by rewrite E fcard1 expr1.
qed.

clone import NominalGroup.NominalGroup as N.

lemma dlist_EU n x xs : xs \in dlist (duniform (elems EU)) n => x \in xs => x \in EU.
proof.
move => xs_d x_xs. rewrite memE -supp_duniform.
move: xs_d; case (0 <= n) => Hn; last by rewrite supp_dlist0; smt().
rewrite supp_dlist // => -[? /allP H]; exact: H.
qed.

theory NCDH.

module type Adversary = {
  proc solve(gx gy: G): G
}.

module Game (A:Adversary) = {
  proc main(): bool = {
  var x, y, r;

  x <$ duniform (elems EU);
  y <$ duniform (elems EU);
  r <@ A.solve(exp g x, exp g y);
    return (r = exp g (x * y));
  }
}.

module Game' (A:Adversary) = {
  proc main(): bool = {
  var x, y, r;

  x <$ duniform (elems EU);
  y <$ duniform (elems EU);
  r <@ A.solve(g^x, g^y);
    return (r = g^(x * y));
  }
}.

module B (A : Adversary) = {
  proc solve (gx gy: G) : G = {
    var r;

    r <@ A.solve(gx^inv f,gy^inv f);
    return (r^f);
  }
}.

(* If A wins against the "factor game", B(A) wins against the game w/o factors *)
lemma unfactor (A <: Adversary) :
  equiv[ Game(A).main ~ Game'(B(A)).main : ={glob A} ==> res{1} => res{2}].
proof.
proc; inline *; auto.
call (:true) => //. auto; rewrite /exp => />; smt(expM exp_inv_f mulA mulC).
qed.

end NCDH.

op na,nb,q_oa,q_ob,q_ddh : int.
axiom na_ge0 : 0 <= na.
axiom nb_ge0 : 0 <= nb.
axiom q_oa_ge0 : 0 <= q_oa.
axiom q_ob_ge0 : 0 <= q_ob.
axiom q_ddh_ge0 : 0 <= q_ddh.

module type CDH_RSR_Oracles = {
  proc oA(i : int) : G
  proc oB(j : int) : G
  proc oa(j : int) : Z
  proc ob(j : int) : Z
  proc ddh(g:G,i:int,j:int) : bool
}.

module type CDH_RSR_Oracles_i = {
  include CDH_RSR_Oracles
  proc init () : unit
}.

module type Adversary (O : CDH_RSR_Oracles) = {
  proc guess() : bool
}.

(* Counting wrapper for CDH_RSR Oracles *)
module Count (O : CDH_RSR_Oracles) = {
  var ca, cb, cddh : int

  proc init () = {
    ca <- 0;
    cb <- 0;
    cddh <- 0;
  }

  proc oA = O.oA
  proc oB = O.oB

  proc oa(i : int) = {
    var r;

    ca <- ca + 1;
    r <@ O.oa(i);
    return r;
  }

  proc ob(i : int) = {
    var r;

    cb <- cb + 1;
    r <@ O.ob(i);
    return r;
  }

  proc ddh (m : G, i,j : int) = {
    var r;

    cddh <- cddh + 1;
    r <@ O.ddh(m,i,j);
    return r;
  }
}.

op e : Z.
axiom e_EU : e \in EU.
op nth' (zs : Z list) = nth e zs.

(* The acutal CDH_RSR game: initialize oracles and counters and
dispatach to adversary *)
module Game (O : CDH_RSR_Oracles_i ) (A : Adversary) = {
  module O' = Count(O)

  proc main() = {
    var r;
    O.init();
    O'.init();
    r <@ A(O').guess();
    return r;
  }
}.

(* The games G1 and G2 are the "real" and the "ideal" game defined in
cryptoprim.pdf *)

module G1 : CDH_RSR_Oracles = {
  var a,b : Z list

  proc init () = {
    a <$ dlist dZ na;
    b <$ dlist dZ nb;
  }

  proc oA (i : int) = { return exp g (nth' a i); }
  proc oB (i : int) = { return exp g (nth' b i); }
  proc oa (i : int) = { return nth' a i; }
  proc ob (i : int) = { return nth' b i; }

  proc ddh(m, i, j) = {
    return
      if 0 <= i && i < na /\ 0 <= j && j < nb
      then m = exp g (nth' a i * nth' b j)
      else false;
  }
}.

module G2 : CDH_RSR_Oracles = {
  import var G1
  var ca,cb : int list

  proc init () = {
    G1.init();
    ca <- [];
    cb <- [];
  }

  proc oA = G1.oA
  proc oB = G1.oB
  proc oa (i : int) = { ca <- i::ca ; return nth' a i; }
  proc ob (j : int) = { cb <- j::cb ; return nth' b j; }

  proc ddh(m, i, j) = {
    return
      if 0 <= i && i < na /\ 0 <= j && j < nb
      then
        if i \in ca || j \in cb
        then m = exp g (nth' a i * nth' b j)
        else false
      else false;
   }
}.

(* Intermediate games:
- G sets "bad" where G1 and G2 differ
- G' behaves like G, but samples invertible exponents (i.e. from EU *)

module G = {
  import var G1
  include var G2 [-ddh,init,oa,ob]
  var bad : bool

  proc init () = {
    G2.init();
    bad <- false;
  }

  proc oa (i : int) = {
    if (!bad) { ca <- i::ca ; }
    return nth' a i;
  }

  proc ob (j : int) = {
    if (!bad) { cb <- j::cb ; }
    return nth' b j;
  }

  proc ddh(m : G, i,j : int) = {
    var t;
    t <- m = exp g (nth' a i * nth' b j);

    (* execute bad if neither was leaked and "false" is not the right answer *)
    if (0 <= i && i < na /\ 0 <= j && j < nb
      /\ !(i \in ca || j \in cb) /\ t)
    { bad <- true; }

    return
      if 0 <= i && i < na /\ 0 <= j && j < nb
      then
        (* answer honestly if a[i] or b[j] was leaked *)
        if i \in ca || j \in cb
        then t
        else false
      else false;
   }
}.

module G' = {
  import var G1 G2
  include var G [-init]

  proc init () = {
    a <$ dlist (duniform (elems EU)) na;
    b <$ dlist (duniform (elems EU)) nb;
    ca <- [];
    cb <- [];
    bad <- false;
  }
}.

(* Same behavior as G1, but defining a bad event equivalent to G *)
module G1b = {
  import var G1 G2
  include var G [-ddh]

  proc ddh(m : G, i,j : int) = {
    var t;

    t <- m = exp g (nth' a i * nth' b j);

    (* execute bad if neither was leaked and "false" is not the right answer *)
    if (0 <= i && i < na /\ 0 <= j && j < nb
      /\ !(i \in ca || j \in cb) /\ t)
    { bad <- true; }

    return
      if 0 <= i && i < na /\ 0 <= j && j < nb
      then t
      else false;
  }
}.

(* Same behavior as G2, but defining a bad event equivalent to G *)
module G2b = {
  import var G1 G2
  include var G [-oa,ob]

  proc oa = G2.oa
  proc ob = G2.ob
}.

op pa,pb : real.

(* the "simulation", called "A" in cryptoprim.pdf *)
(* we have an event "stop" that corresponds to the simulation stoping,
   i.e., oa(i) is queried but ia[i] is true, meaning we cannot actually
   compute the correct return value *)
module S = {
  import var G1 (* var a, b : Z list *)
  var ia, ib : bool list (* inject a/b *)
  import var G2 (* var ca, cb : int list / call logs *)
  var gx,gy : G
  var m_crit : G
  var cddh, k : int

  proc init (gx' : G, gy' : G) = {
    ia <$ dlist (dbiased pa) na;
    ib <$ dlist (dbiased pb) nb;
    a <$ dlist (duniform (elems EU)) na;
    b <$ dlist (duniform (elems EU)) nb;
    ca <- [];
    cb <- [];
    gx <- gx';
    gy <- gy';
    k <$ [1..q_ddh];
    cddh <- 0;
  }

  proc oa (i : int) = {
    if (cddh < k) { ca <- i :: ca; }
    return (nth' a i);
  }

  proc ob (j : int) = {
    if (cddh < k) { cb <- j :: cb; }
    return (nth' b j);
  }

  proc oA (i : int) = {
    return (if nth false ia i then gx^(nth' a i) else exp g (nth' a i));
  }

  proc oB (j : int) = {
    return (if nth false ib j then gy^(nth' b j) else exp g (nth' b j));
  }

  proc ddh (m:G,i:int,j:int) = {
    var r : bool;

    cddh <- cddh + 1;
    r <- false;

    if (i \in ca) {
      r <- m = (if nth false ib j then gy^(nth' b j) else exp g (nth' b j))^nth' a i;
    }
    if (j \in cb) {
      r <- m = (if nth false ia i then gx^(nth' a i) else exp g (nth' a i))^nth' b j;
    }

    (* record k-th query *)
    if (0 <= i && i < na /\ 0 <= j && j < nb /\ !(i \in ca) /\ !(j \in cb) /\ cddh = k) {
      m_crit <- m^(inv (nth' G1.a i) * inv(nth' G1.b j));
    }

    if (!(0 <= i && i < na /\ 0 <= j && j < nb)) { r <- false; }
    return r;
  }
}.

(* Proof outline:

1. |G1 - G2| <= G[bad]
2. G[bad] <= G'[bad] + "prob. of distinguishing dZ and duniform EU"
3. Define simulation S and an adversary B against the NCDH games
3. G'[bad] <= P * NCDH.Game(B(A)).

*)

module type S_i = {
  include CDH_RSR_Oracles
  proc init (gx : G, gy : G) : unit
}.

(* the simulation game *)
module GameS (A : Adversary) = {
  module O' = Count(S)

  proc main(gx:G, gy:G) = {
    var r;
    S.init(gx,gy);
    O'.init();
    r <@ A(O').guess();
    return r;
  }
}.

(* adversary against CDH problem for nominal groups *)
module B (A : Adversary) : NCDH.Adversary = {
  proc solve(gx gy : G) : G = {
    GameS(A).main(gx,gy);
    return S.m_crit;
  }
}.

op DELTA : real. (* TODO specify *)
op p : real.     (* TODO specify *)

section.

declare module A : Adversary {G1,G2,G,Count,S}.

axiom A_ll : forall (O <: CDH_RSR_Oracles{A}),
  islossless O.oA =>
  islossless O.oB =>
  islossless O.oa =>
  islossless O.ob =>
  islossless O.ddh =>
  islossless A(O).guess.

axiom A_bound : forall (O <: CDH_RSR_Oracles{A}),
  hoare [ A(Count(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.cddh = 0 ==>
    Count.ca <= q_oa /\ Count.cb <= q_ob /\ Count.cddh <= q_ddh].

local module Gk : CDH_RSR_Oracles_i = {
  import var G1 G2 G
  include var G' [-init,ddh]
  var k, k_bad, i_k, j_k, cddh : int
  var ia,ib : bool list

  proc init() = {
    ia <$ dlist (dbiased pa) na;
    ib <$ dlist (dbiased pb) nb;
    G'.init();
    cddh <- 0;
    k_bad <- -1;
    i_k <- -1;
    j_k <- -1;
    k <$ [1..q_ddh];
  }

  proc ddh(m : G, i,j : int) = {
    var t;
    cddh <- cddh + 1;
    t <- m = exp g (nth' a i * nth' b j);

    (* execute bad if neither was leaked and "false" is not the right answer *)
    if (0 <= i && i < na /\ 0 <= j && j < nb
      /\ !(i \in ca || j \in cb) /\ t /\ !bad) {
      bad <- true;
      k_bad <- cddh;
      i_k <- i;
      j_k <- j;
    }

    return
      if 0 <= i && i < na /\ 0 <= j && j < nb
      then
        (* answer honestly if a[i] or b[j] was leaked *)
        if i \in ca || j \in cb
        then t
        else false
      else false;
   }
}.

local module Gk_bad : CDH_RSR_Oracles_i = {
  import var G1 G2 G
  include var Gk [-init]
  (* var k_bad, i_k, j_k, cddh : int *)

  proc init() = {
    G'.init();
    cddh <- 0;
    k_bad <- -1;
    i_k <- -1;
    j_k <- -1;
  }
}.

(* Variant of Game, where the samling for Gk is done at the end *)
module Game' (O : CDH_RSR_Oracles_i ) (A : Adversary) = {
  var k : int
  var ia,ib : bool list

  proc main() = {
    Game(O, A).main();
    k <$ [1..q_ddh];
    ia <$ dlist (dbiased pa) na;
    ib <$ dlist (dbiased pb) nb;
  }
}.

op nstop (ia ib : bool list) (ca cb : int list) =
  (forall i, i \in ca => nth false ia i = false) /\
  (forall j, j \in cb => nth false ib j = false).

local lemma Game_Game' &m :
  Pr[Game(Gk,A).main() @ &m :
     G.bad /\ Gk.k = Gk.k_bad /\ nstop Gk.ia Gk.ib G2.ca G2.cb /\
     nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k] =
  Pr[Game'(Gk_bad,A).main() @ &m :
     G.bad /\ Game'.k = Gk.k_bad /\ nstop Game'.ia Game'.ib G2.ca G2.cb /\
     nth false Game'.ia Gk.i_k /\ nth false Game'.ib Gk.j_k].
proof.
byequiv => //; proc; inline *; swap{1} [1..2] 14; swap{1} 10 4.
seq 12 12 : (={glob A, glob G1, glob G2, glob Count, G.bad} /\
             ={cddh,k_bad,i_k,j_k}(Gk,Gk)); 1: by auto.
auto; auto.
call (: ={glob G1, G2.ca, G2.cb, G.bad} /\ ={cddh,k_bad,i_k,j_k}(Gk,Gk)).
- by proc.
- by proc.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by auto => />.
qed.

local lemma Gk_bound :
  hoare [Game(Gk_bad, A).main :
         true ==>
         card (oflist G2.ca) <= q_oa /\ card (oflist G2.cb) <= q_ob /\
         Gk.cddh <= q_ddh].
proof.
conseq (: _ ==> card (oflist G2.ca) <= Count.ca /\
                card (oflist G2.cb) <= Count.cb /\ Count.cddh = Gk.cddh)
       (: _ ==> Count.ca <= q_oa /\ Count.cb <= q_ob /\ Count.cddh <= q_ddh);
  1: smt().
- proc.
  seq 2 : (Count.ca = 0 /\ Count.cb = 0 /\ Count.cddh = 0); 1: by inline *; auto.
  by call (A_bound Gk_bad).
- proc; inline *.
  seq 12 : (card (oflist G2.ca) <= Count.ca /\
            card (oflist G2.cb) <= Count.cb /\ Count.cddh = Gk.cddh);
    1: by auto; smt(fcards0).
  call (: card (oflist G2.ca) <= Count.ca /\
          card (oflist G2.cb) <= Count.cb /\ Count.cddh = Gk.cddh).
  + by proc.
  + by proc.
  + proc; inline *; auto.
    smt(fcard1 fcard_ge0 fcardU oflist_cons subsetIl subset_leq_fcard).
  + proc; inline *; auto.
    smt(fcard1 fcard_ge0 fcardU oflist_cons subsetIl subset_leq_fcard).
  + by proc; inline *; auto.
  * by auto.
qed.

(* TODO: maintain i_k \notin ca and same for j_k/cb *)
local lemma guess_bound &m :
  1%r/q_ddh%r * (1%r-clamp pa)^q_oa * (1%r- clamp pb)^q_ob * clamp pa * clamp pb *
  Pr [Game(G',A).main() @ &m : G.bad] <=
  Pr [Game(Gk,A).main() @ &m :
      G.bad /\ Gk.k = Gk.k_bad /\ nstop Gk.ia Gk.ib G2.ca G2.cb /\
      nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k].
proof.
pose p := Pr[Game(G', A).main() @ &m : G.bad].
pose c := (1%r-clamp pa)^q_oa * clamp pa * (1%r- clamp pb)^q_ob * clamp pb.
rewrite Game_Game'; byphoare (_ : glob A = (glob A){m} ==> _) => //; proc.
conseq (: _ ==>
          G.bad /\ 1 <= Gk.k_bad /\ Gk.k_bad < q_ddh + 1 /\
          card (oflist G2.ca) <= q_oa /\ card (oflist G2.cb) <= q_ob /\
          ! (Gk.i_k \in G2.ca) /\ ! (Gk.j_k \in G2.cb) /\
          Gk.i_k \in oflist (range 0 na) /\ Gk.j_k \in oflist (range 0 nb) /\
          Game'.k = Gk.k_bad /\ nstop Game'.ia Game'.ib G2.ca G2.cb /\
          nth false Game'.ia Gk.i_k /\ nth false Game'.ib Gk.j_k) => //.
seq 1 : (G.bad /\ 1 <= Gk.k_bad /\ Gk.k_bad < q_ddh + 1 /\
         card (oflist G2.ca) <= q_oa /\ card (oflist G2.cb) <= q_ob /\
         !(Gk.i_k \in G2.ca) /\ !(Gk.j_k \in G2.cb) /\
          Gk.i_k \in oflist (range 0 na) /\ Gk.j_k \in oflist (range 0 nb))
        p (c / q_ddh%r) (1%r - p) 0%r; [by auto| | |hoare; auto; smt()|smt()].
- call (: glob A = (glob A){m} ==>
          G.bad /\ 1 <= Gk.k_bad /\ Gk.k_bad < q_ddh + 1 /\
          card (oflist G2.ca) <= q_oa /\ card (oflist G2.cb) <= q_ob /\
          Gk.i_k \in oflist (range 0 na) /\ Gk.j_k \in oflist (range 0 nb) /\
          ! (Gk.i_k \in G2.ca) /\ ! (Gk.j_k \in G2.cb)); 2: by auto.
  conseq (: _ ==> G.bad /\ ! (Gk.i_k \in G2.ca) /\ ! (Gk.j_k \in G2.cb) /\
                  Gk.i_k \in oflist (range 0 na) /\
                  Gk.j_k \in oflist (range 0 nb) : >= p)
         (: _ ==> G.bad => 1 <= Gk.k_bad /\ Gk.k_bad < q_ddh + 1 /\
                  card (oflist G2.ca) <= q_oa /\ card (oflist G2.cb) <= q_ob).
  + by auto.
  + smt().
  + conseq (: _ ==> card (oflist G2.ca) <= q_oa /\ card (oflist G2.cb) <= q_ob)
           (: _ ==> G.bad => 1 <= Gk.k_bad /\ Gk.k_bad < q_ddh + 1);
    [by []|smt()| |by conseq Gk_bound].
    conseq (: _ ==> G.bad => 1 <= Gk.k_bad /\ Gk.k_bad <= Gk.cddh /\
                             Gk.cddh <= q_ddh) => //; 1: smt().
    conseq (: _ ==> G.bad => 1 <= Gk.k_bad /\ Gk.k_bad <= Gk.cddh)
           Gk_bound => //; 1: smt().
    proc; inline *.
    seq 12 : (G.bad = false /\ Gk.cddh = 0 /\ Gk.k_bad = -1); auto.
    call (: 0 <= Gk.cddh /\ (G.bad => 1 <= Gk.k_bad /\ Gk.k_bad <= Gk.cddh)).
    * by proc.
    * by proc.
    * by proc; inline *; auto.
    * by proc; inline *; auto.
    * by proc; inline *; auto; smt().
    * by auto.
  + bypr => &m' gA; rewrite /p; byequiv => //; proc; inline *.
    call (: ={glob G1, glob G2, glob Count, G.bad} /\
            (G.bad{1} =>
             G.bad{2} /\ ! (Gk.i_k{2} \in G2.ca{2}) /\
                         ! (Gk.j_k{2} \in G2.cb{2}) /\
             Gk.i_k{2} \in oflist (range 0 na) /\
             Gk.j_k{2} \in oflist (range 0 nb))).
    * by proc.
    * by proc.
    * by proc; inline *; auto.
    * by proc; inline *; auto.
    * by proc; inline *; auto; smt(mem_oflist mem_range).
    * by auto; smt().
- conseq (: 1 <= Gk.k_bad /\ Gk.k_bad < q_ddh + 1 /\
            card (oflist G2.ca) <= q_oa /\ card (oflist G2.cb) <= q_ob /\
            ! (Gk.i_k \in G2.ca) /\ ! (Gk.j_k \in G2.cb) /\
            Gk.i_k \in oflist (range 0 na) /\ Gk.j_k \in oflist (range 0 nb) ==>
            Game'.k = Gk.k_bad /\
            nth false Game'.ia Gk.i_k /\ nth false Game'.ib Gk.j_k /\
            nstop Game'.ia Game'.ib G2.ca G2.cb) => //.
  seq 1 : (Game'.k = Gk.k_bad /\
           card (oflist G2.ca) <= q_oa /\ card (oflist G2.cb) <= q_ob /\
           ! (Gk.i_k \in G2.ca) /\ ! (Gk.j_k \in G2.cb) /\
           Gk.i_k \in oflist (range 0 na) /\ Gk.j_k \in oflist (range 0 nb))
          (1%r / q_ddh%r) c (1%r - (1%r / q_ddh%r)) 0%r;
  [by auto| | |by auto|smt()].
  + rnd; auto => /> {&m p} &m *; rewrite drangeE.
    rewrite count_uniq_mem; 1: exact range_uniq.
    suff -> : Gk.k_bad{m} \in range 1 (q_ddh + 1) by smt().
    by rewrite mem_range.
  + conseq (: card (oflist G2.ca) <= q_oa /\ card (oflist G2.cb) <= q_ob /\
              ! (Gk.i_k \in G2.ca) /\ ! (Gk.j_k \in G2.cb) /\
              Gk.i_k \in oflist (range 0 na) /\
              Gk.j_k \in oflist (range 0 nb) ==>
              nth false Game'.ia Gk.i_k /\ nth false Game'.ib Gk.j_k /\
              nstop Game'.ia Game'.ib G2.ca G2.cb) => // {p}.
    pose p := (fun b => b = false); rewrite /c; move => {c}.
    seq 1 : (card (oflist G2.cb) <= q_ob /\ ! (Gk.j_k \in G2.cb) /\
             Gk.j_k \in oflist (range 0 nb) /\
             (forall i, i \in oflist G2.ca =>   p (nth false Game'.ia i)) /\
             (forall j, j \in fset1 Gk.i_k => ! p (nth false Game'.ia j)))
            ((1%r - clamp pa) ^ q_oa * clamp pa)
            ((1%r - clamp pb) ^ q_ob * clamp pb)
            (1%r - ((1%r - clamp pa) ^ q_oa * clamp pa)) 0%r;
    [by auto| | |by auto|smt()].
    * conseq (: _ ==>
                (forall (i : int),
                   i \in (oflist G2.ca `&`
                          oflist (range 0 (size Game'.ia))) =>
                     p (nth false Game'.ia i)) /\
                (forall (j : int),
                   j \in (fset1 Gk.i_k `&` oflist (range 0 na)) =>
                   ! p (nth false Game'.ia j)));
        1: smt (in_filter mem_oflist mem_range nth_default nth_neg).
      rnd; auto => {&m} &m ?.
      have -> : mu (dlist (dbiased pa) na)
                   (fun (x : bool list) =>
                     (forall (i : int),
                        i \in oflist G2.ca{m} `&` oflist (range 0 (size x)) =>
                          p (nth false x i)) /\
                     (forall (j : int),
                        j \in fset1 Gk.i_k{m} `&` oflist (range 0 na) =>
                        ! p (nth false x j))) =
                mu (dlist (dbiased pa) na)
                   (fun (x : bool list) =>
                     (forall (i : int),
                        i \in oflist G2.ca{m} `&` oflist (range 0 na) =>
                          p (nth false x i)) /\
                     (forall (j : int),
                        j \in fset1 Gk.i_k{m} `&` oflist (range 0 na) =>
                        ! p (nth false x j)))
        by smt (mu_eq_support na_ge0 supp_dlist_size).
      rewrite dlist_set2E;
      [exact dbiased_ll|exact na_ge0|
       smt(fsetIC mem_oflist mem_range subsetIl subsetP)|
       smt(fsetIC mem_oflist mem_range subsetIl subsetP)|
       smt(mem_oflist subsetIl subsetP)|].
      rewrite !dbiasedE /p /predC /= fset1I.
      smt(fcard1 fcard_ge0 expr1 ler_wiexpn2l subsetIl subset_leq_fcard).
    * conseq (: card (oflist G2.cb) <= q_ob /\ ! (Gk.j_k \in G2.cb) /\
                Gk.j_k \in oflist (range 0 nb) /\
                (forall (i : int), i \in oflist G2.ca =>
                                     p (nth false Game'.ia i)) /\
                (forall (j : int), j \in fset1 Gk.i_k =>
                                   ! p (nth false Game'.ia j)) ==>
                ((forall (i : int), i \in oflist G2.ca =>
                                      p (nth false Game'.ia i)) /\
                 (forall (j : int), j \in fset1 Gk.i_k =>
                                    ! p (nth false Game'.ia j))) /\
                ((forall (i : int), i \in oflist G2.cb `&`
                                          oflist (range 0 (size Game'.ib)) =>
                                      p (nth false Game'.ib i)) /\
                 (forall (j : int), j \in fset1 Gk.j_k `&`
                                          oflist (range 0 nb) =>
                                    ! p (nth false Game'.ib j)))) => //;
        1: smt (fset1I in_filter mem_oflist mem_range nth_default nth_neg).
      rnd; auto => /> {&m} &m 3? _ _.
      have -> : mu (dlist (dbiased pb) nb)
                   (fun (x : bool list) =>
                     (forall (i : int),
                        i \in oflist G2.cb{m} `&` oflist (range 0 (size x)) =>
                          p (nth false x i)) /\
                     (forall (j : int),
                        j \in fset1 Gk.j_k{m} `&` oflist (range 0 nb) =>
                        ! p (nth false x j))) =
                mu (dlist (dbiased pb) nb)
                   (fun (x : bool list) =>
                     (forall (i : int),
                        i \in oflist G2.cb{m} `&` oflist (range 0 nb) =>
                          p (nth false x i)) /\
                     (forall (j : int),
                        j \in fset1 Gk.j_k{m} `&` oflist (range 0 nb) =>
                        ! p (nth false x j)))
        by smt (mu_eq_support nb_ge0 supp_dlist_size).
      rewrite dlist_set2E;
      [exact dbiased_ll|exact nb_ge0|
       smt(fsetIC mem_oflist mem_range subsetIl subsetP)|
       smt(fsetIC mem_oflist mem_range subsetIl subsetP)|
       smt(mem_oflist subsetIl subsetP)|].
      rewrite !dbiasedE /p /predC /= fset1I.
      smt(fcard1 fcard_ge0 expr1 ler_wiexpn2l subsetIl subset_leq_fcard).
qed.

(* Same as Gk, but bad is set only at the k-th dhh call (if set at all) *)
local module Gk' : CDH_RSR_Oracles_i = {
  import var G1 G2 G
  include var Gk [-init,ddh]

  proc init() = {
    ia <$ dlist (dbiased pa) na;
    ib <$ dlist (dbiased pb) nb;
    G'.init();
    cddh <- 0;
    i_k <- -1;
    j_k <- -1;
    k <$ [1..q_ddh];
  }

  proc ddh(m : G, i,j : int) = {
    var t;
    cddh <- cddh + 1;
    t <- m = exp g (nth' a i * nth' b j);

    (* execute bad if neither was leaked and "false" is not the right answer *)
    if (0 <= i && i < na /\ 0 <= j && j < nb
      /\ !(i \in ca || j \in cb) /\ t /\ cddh = k /\ !bad) {
      bad <- true;
      i_k <- i;
      j_k <- j;
    }

    return
      if 0 <= i && i < na /\ 0 <= j && j < nb
      then
        (* answer honestly if a[i] or b[j] was leaked *)
        if i \in ca || j \in cb
        then t
        else false
      else false;
  }
}.

(* should be an equality, but this should suffice *)
local lemma Gk_Gk' &m :
    Pr [ Game(Gk,A).main() @ &m :
      G.bad /\ Gk.k = Gk.k_bad /\ nstop Gk.ia Gk.ib G2.ca G2.cb /\
      nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k ] <=
    Pr [ Game(Gk',A).main() @ &m :
      G.bad /\ nstop Gk.ia Gk.ib G2.ca G2.cb /\
      nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k ].
proof.
byequiv => //. proc; inline *. symmetry.
call (: G.bad /\ Gk.k <> Gk.k_bad,
  ={glob G1,glob G2,G.bad} /\ ={cddh,k,ia,ib,i_k,j_k}(Gk,Gk)
  /\ (G.bad <=> Gk.k = Gk.k_bad){2});
  try by move => *; proc; inline *; auto => />.
- exact A_ll.
- move => *; proc; inline *; auto => /> /#.
- auto => />; smt(supp_dinter).
qed.

local lemma guess_S &m x y : x \in EU => y \in EU =>
  Pr [ Game(Gk',A).main() @ &m :
    G.bad /\ nstop Gk.ia Gk.ib G2.ca G2.cb /\
    nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k ] <=
  Pr [GameS(A).main(exp g x,exp g y) @ &m : S.m_crit = exp g (x * y) ].
proof.
move => x_EU y_EU.
byequiv => //; proc; inline *. sp.
symmetry.
call (: !nstop Gk.ia Gk.ib G2.ca G2.cb \/
        !(G.bad => nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k) \/
        Gk.k <= Gk.cddh
         ,
  ={glob Count,G2.ca,G2.cb} /\ ={ia,ib,cddh,k}(S,Gk) /\
  (S.gx = exp g x /\ S.gy = exp g y){1} /\
  (forall i,
    nth' G1.a{2} i = if nth false S.ia{1} i then nth' G1.a{1} i * x else nth' G1.a{1} i) /\
  (forall j,
    nth' G1.b{2} j = if nth false S.ib{1} j then nth' G1.b{1} j * y else nth' G1.b{1} j) /\
  (G.bad{2} => S.m_crit{1} = exp g (x * y)) /\
  (G.bad <=> Gk.k <= Gk.cddh){2} /\
  (forall i, nth' G1.a{1} i \in EU /\ nth' G1.b{1} i \in EU)
  ,
  !(nstop Gk.ia Gk.ib G2.ca G2.cb){2} \/
  !(G.bad => nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k){2} \/
  (S.k <= S.cddh /\ S.m_crit{1} = exp g (x * y)){1} \/
  (Gk.k <= Gk.cddh /\ !G.bad){2}
  ); try by move => *; proc; inline*; auto. (* 11 goals left *)
- exact A_ll.
- proc; inline *; auto => /> &1 &2. smt(mulA mulC expM).
- proc; inline *; auto => /> &1 &2. smt(mulA mulC expM).
- proc; inline *; auto => /> &1 &2. smt().
- move => &1; proc; inline *; auto => />. smt().
- proc; inline *; auto => /> &1 &2.
  rewrite !negb_or !negbK. smt().
- move => &1; proc; inline *; auto => />. smt().
- proc; inline *; auto => /> &1 &2. rewrite !negb_or !negbK => />.
  move => Hca Hcb Hbad G1 G2.
  have {G1 G2} G1 : Gk.cddh{2} < Gk.k{2} by smt().
  case (0 <= i{2} && i{2} < na /\ 0 <= j{2} && j{2} < nb); 2: smt().
  move => /> 4? => Ha Hb _ HEU. split; 2: smt(expM mulA mulC).
  rewrite oraE negb_or => -[iNca jNcb]. rewrite iNca jNcb /=.
  move => G2 _ _. rewrite -implybE => -[Hia Hib].
  rewrite Ha Hb Hia Hib /= -expM'. smt(mulA mulC invK Emult).
- move => *; proc; inline *; auto => />. smt().
- move => *; proc; inline *; auto => />. smt().
(* main goal: establishing the invariant *)
wp. rnd. wp.
rnd (mapi (fun j z => if nth false S.ib{1} j then z * y else z))
    (mapi (fun j z => if nth false S.ib{1} j then z * inv y else z)).
rnd (mapi (fun i z => if nth false S.ia{1} i then z * x else z))
    (mapi (fun i z => if nth false S.ia{1} i then z * inv x else z)).
rnd; rnd; auto => /> ia d_ia ib d_ib.
have [? ?] : 0 <= na /\ 0 <= nb. smt(na_ge0 nb_ge0).
have Hmapi : forall a' b' na' x', 0 <= na' => x' \in EU => a' \in dlist (duniform (elems EU)) na' =>
    mapi (fun (i : int) (z : Z) => if b' i then z * x' else z) a' \in dlist (duniform (elems EU)) na'.
  move => a' b' na' x' na'_ge0 x'_EU. rewrite supp_dlist ?na'_ge0 => -[size_a' /allP supp_a'].
  apply: dlist_fu_eq; 1: by rewrite size_mapi size_a'.
  move => z /mapiP /(_ e) [n] /= [Hn Hz].
  have ? : nth' a' n \in EU. rewrite memE -supp_duniform. exact/supp_a'/mem_nth.
  rewrite supp_duniform -memE. smt(Emult).

split => [a d_a | ? ].
  rewrite in_mapiK => //= i z z_a _. case (nth false ia i) => // _.
  rewrite invK' //. exact: dlist_EU d_a z_a.
split => [a d_a | _ ].
  apply: dlist_uni => //; 1: exact: duniform_uni.
  apply Hmapi => //. exact: Einv.
move => a a_d; split => [| _].
  exact Hmapi.
split => [|_].
  rewrite in_mapiK => //= i z z_a _. case (nth false ia i) => // _.
  rewrite invK //. exact: dlist_EU a_d z_a.
split => [b b_d | _ ].
  rewrite in_mapiK => //= j z z_b _. case (nth false ib j) => // _.
  rewrite invK' //. exact: dlist_EU b_d z_b.
split => [b b_d | _].
  apply: dlist_uni => //; 1: exact: duniform_uni.
  apply Hmapi => //. exact: Einv.
move => b b_d; split => [| _].
  exact Hmapi.
split => [|_].
  rewrite in_mapiK => //= j z z_b _. case (nth false ib j) => // _.
  rewrite invK //. exact: dlist_EU b_d z_b.
move => k supp_k. split; 2: smt(). split; 1: smt().
move => _; split; last split.
+ move => i. case (0 <= i && i < size a) => [i_in|i_out].
    rewrite /nth' (nth_mapi e a) //=.
  rewrite /nth' !(nth_out false) //= ?(nth_out e) //.
    smt(supp_dlist_size).
  by rewrite size_mapi.
+ move => j. case (0 <= j && j < size b) => [j_in|j_out].
    rewrite /nth' (nth_mapi e b) //=.
  rewrite /nth' !(nth_out false) //= ?(nth_out e) //.
    smt(supp_dlist_size).
  by rewrite size_mapi.
+ move => i; split.
  * case (0 <= i && i < size a) => [i_in|i_out].
      move: a_d. rewrite supp_dlist // => -[? /allP /(_ (nth' a i))].
      rewrite supp_duniform -memE. apply. exact mem_nth.
    by rewrite /nth' nth_out // e_EU.
  * case (0 <= i && i < size b) => [i_in|i_out].
      move: b_d. rewrite supp_dlist // => -[? /allP /(_ (nth' b i))].
      rewrite supp_duniform -memE. apply. exact mem_nth.
    by rewrite /nth' nth_out // e_EU.
qed.

local lemma A_B &m :
  Pr [ Game(Gk',A).main() @ &m :
    G.bad /\ nstop Gk.ia Gk.ib G2.ca G2.cb /\
    nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k ] <=
  Pr [ NCDH.Game(B(A)).main() @ &m : res ].
proof.
pose p := Pr[Game(Gk', A).main() @ &m :
   G.bad /\ nstop Gk.ia Gk.ib G2.ca G2.cb /\ nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k].
byphoare (: (glob A,Gk.i_k,Gk.j_k) = (glob A,Gk.i_k,Gk.j_k){m} ==> _) => //.
proc; inline B(A).solve. wp.
seq 4 : true 1%r p 0%r _
  (x \in EU /\ y \in EU /\ gx = exp g x /\ gy = exp g y
  /\ (glob A,Gk.i_k,Gk.j_k) = (glob A,Gk.i_k,Gk.j_k){m}) => //.
- auto => />; smt( supp_duniform memE).
- islossless; apply duniform_ll; smt(e_EU).
exlim x, y => x' y'.
call (: (x' \in EU) /\ (y' \in EU) /\ gx = exp g x' /\ gy = exp g y'
    /\ (glob A,Gk.i_k,Gk.j_k) = (glob A,Gk.i_k,Gk.j_k){m}
  ==> S.m_crit = exp g (x' * y')); 2: by auto.
bypr => &m' /> ? ? -> -> *.
suff -> : p = Pr[Game(Gk', A).main() @ &m' :
    G.bad /\ nstop Gk.ia Gk.ib G2.ca G2.cb /\ nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k]
  by apply guess_S.
rewrite /p; byequiv => //. sim => /> /#.
qed.

lemma G1G2_Gbad &m :
    `| Pr[ Game(G1,A).main() @ &m : res ] - Pr[ Game(G2,A).main() @ &m : res ] | <=
       Pr[ Game(G,A).main() @ &m : G.bad ].
proof.
(* Introduce bad events into G1 and G2 *)
have -> : Pr[ Game(G2,A).main() @ &m : res ] = Pr[ Game(G2b,A).main() @ &m : res ].
  byequiv => //. proc; inline *.
  call (_ : ={glob G2}) => //; 1..4: (by sim); last by auto => />.
  by proc; inline *; auto.
have -> : Pr[ Game(G1,A).main() @ &m : res ] = Pr[ Game(G1b,A).main() @ &m : res ].
  byequiv => //; proc; inline *.
  call (_ : ={glob G1}); 1..4: (by sim); last by auto => />.
  by proc; inline *; auto.
(* we can continue logging oa/ob queries once bad happens *)
have -> : Pr[Game(G, A).main() @ &m : G.bad] = Pr[Game(G2b, A).main() @ &m : G.bad].
  byequiv => //; proc; inline *.
  call (: G.bad, ={G.bad,glob G1,glob G2,glob Count}, ={G.bad});
    try by move => *; proc; inline *; auto => /> /#.
  exact: A_ll.
  by auto => /> /#.
byequiv (_ : ={glob A} ==> ={G.bad} /\ (!G.bad{2} => ={res})) : G.bad => //; 2: smt().
proc; inline *.
call (_ : G.bad, ={G.bad,glob G2,glob Count}, ={G.bad});
  try by move => *; by proc; inline *; auto => /> /#.
exact: A_ll.
by auto => /> /#.
qed.

(* what about res, do we care? *)
lemma G_G' &m :
    `| Pr[ Game(G,A).main() @ &m : G.bad ] - Pr[ Game(G',A).main() @ &m : G.bad ] | <= DELTA.
admitted.

lemma nth_dlist b i n p :
  0%r <= p => p <= 1%r => 0 <= i => i < n =>
  mu (dlist (dbiased p) n) (transpose (nth b) i) = p.
proof.
move => *; rewrite (dlist_nthE b _ (fun x => x)) ?dbiasedE /=;
  smt(clamp_id dlist_ll dbiased_ll).
qed.

lemma badG'_cdh &m : 1 <= q_ddh => 0%r < pa && pa < 1%r => 0%r < pb && pb < 1%r =>
    Pr[ Game(G',A).main() @ &m : G.bad ] <=
    q_ddh%r / ((1%r-clamp pa)^q_oa * (1%r- clamp pb)^q_ob * clamp pa * clamp pb)
    * Pr [ NCDH.Game(B(A)).main() @ &m : res ].
proof.
move => Bq Bpa Bpb.
have H1 := guess_bound &m; have H2 := Gk_Gk' &m; have H3 := A_B &m.
have {H2 H3} H4 := ler_trans _ _ _ H2 H3.
have {H1 H4} := ler_trans _ _ _ H1 H4.
rewrite !clamp_id; 1,2: smt(). move => H5.
rewrite -ler_pdivr_mull. smt(divr_gt0 mulr_gt0 expr_gt0).
rewrite invf_div. smt().
qed.

end section.
