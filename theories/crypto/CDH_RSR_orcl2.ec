require import AllCore List Distr DBool DInterval DList SmtMap.
require import FinType FSet NominalGroup PROM SplitRO2.

import Distr.MRat.
import DBool.Biased.
import StdOrder.RealOrder.
import RField.

(* Statistical distance - merge with SDist.ec *)

op sdist : 'a distr -> 'a distr -> real.

theory D.
type a.
op n : { int | 0 <= n } as n_ge0.
op d1, d2 : a distr.

module type Distinguisher = {
  proc guess (x : a list) : bool
}.

module SampleDlist (A : Distinguisher) = {
  proc main(b : bool) = {
    var x, r;

    x <- witness;
    if (! b) { x <$ dlist d1 n; }
    if (  b) { x <$ dlist d2 n; }
    r <@ A.guess(x);
    return r;
  }
}.

axiom sdist_dlist &m (A <: Distinguisher) :
  `| Pr[SampleDlist(A).main(false) @ &m : res] -
     Pr[SampleDlist(A).main(true ) @ &m : res] | <=
  n%r * sdist d1 d2.

end D.

clone import NominalGroup.NominalGroup as N.

op e : Z.
axiom e_EU : e \in EU.
op nth' (zs : Z list) = nth e zs.

op elog (x : G) = choiceb (fun a => a \in EU /\ x = exp g a) e.

op elogr (y : Z) (b : G) = choiceb (fun x => x \in EU /\ b = exp g (y * x)) e.

lemma exprK (x y : Z) : x \in EU => y \in EU => elogr y (exp g (y * x)) = x.
proof.
move => x_EU y_EU; rewrite /elogr /=.
have := choicebP (fun a : Z => a \in EU /\ exp g (y * x) = exp g (y * a)) e _;
[by exists x | move => [E1 E2]].
by apply (exp_inj' y) => //; rewrite -E2.
qed.

(* we only get one cancelation law *)
lemma expK (x : Z) : x \in EU => elog (exp g x) = x.
proof.
move => x_EU; rewrite /elog /=.
have [E1 E2] := choicebP (fun a : Z => a \in EU /\ exp g x = exp g a) e _;
[by exists x | by apply exp_inj => //; rewrite -E2].
qed.

lemma elog_EU x : elog x \in EU.
proof.
rewrite /elog; case (exists a, a \in EU /\ x = exp g a) => [E | nE].
- by have /= := choicebP (fun a => a \in EU /\ x = exp g a) e E.
by rewrite choiceb_dfl ?e_EU // /#.
qed.

lemma dlist_EU n x xs :
  xs \in dlist (duniform (elems EU)) n => x \in xs => x \in EU.
proof.
move => xs_d x_xs; rewrite memE -supp_duniform.
move: xs_d; case (0 <= n) => Hn; 2: by rewrite supp_dlist0; smt().
by rewrite supp_dlist // => -[? /allP H]; exact: H.
qed.

lemma fcard_oflist (s : 'a list) : card (oflist s) <= size s.
proof.
elim: s => [|x s IHs]; 1: by rewrite -set0E fcards0.
by rewrite oflist_cons fcardU fcard1 /=; smt(fcard_ge0).
qed.

(* The CDH Game for Nominal Groups, with and without the factor for exponentiation *)
theory NCDH.

module type Adversary = {
  proc solve (gx gy : G) : G
}.

module Game (A:Adversary) = {
  proc main () : bool = {
  var x, y, r;

  x <$ duniform (elems EU);
  y <$ duniform (elems EU);
  r <@ A.solve(exp g x, exp g y);
  return (r = exp g (x * y));
  }
}.

module Game' (A:Adversary) = {
  proc main () : bool = {
  var x, y, r;

  x <$ duniform (elems EU);
  y <$ duniform (elems EU);
  r <@ A.solve(g ^ x, g ^ y);
  return (r = g ^ (x * y));
  }
}.

module B (A : Adversary) = {
  proc solve (gx gy : G) : G = {
    var r;

    r <@ A.solve(gx ^ inv f, gy ^ inv f);
    return (r ^ f);
  }
}.

(* If A wins against the "factor game", B(A) wins against the game w/o factors *)
lemma unfactor (A <: Adversary) :
  equiv[Game(A).main ~ Game'(B(A)).main : ={glob A} ==> res{1} => res{2}].
proof.
proc; inline *; auto.
by call (: true) => //; auto; rewrite /exp => />; smt(mulA mulC powM pow_inv_f).
qed.

end NCDH.

op na :    {int | 0 <= na}    as na_ge0.
op nb :    {int | 0 <= nb}    as nb_ge0.
op q_oa :  {int | 0 <= q_oa}  as q_oa_ge0.
op q_ob :  {int | 0 <= q_ob}  as q_ob_ge0.
op q_ddh : {int | 1 <= q_ddh} as q_ddh_ge1.

clone D as Da with
  type a      <- Z,
  op n        <- na,
  op d1       <- dZ,
  op d2       <- duniform (elems EU),
  axiom n_ge0 <- na_ge0.

clone D as Db with
  type a      <- Z,
  op n        <- nb,
  op d1       <- dZ,
  op d2       <- duniform (elems EU),
  axiom n_ge0 <- nb_ge0.

module type CDH_RSR_Oracles = {
  proc oA  (i : int) : G
  proc oB  (j : int) : G
  proc oa  (j : int) : Z
  proc ob  (j : int) : Z
  proc ddh (g : G, i : int, j : int) : bool
}.

module type CDH_RSR_Oracles_i = {
  include CDH_RSR_Oracles
  proc init () : unit
}.

module type Adversary (O : CDH_RSR_Oracles) = {
  proc guess () : bool
}.

(* Counting wrapper for CDH_RSR Oracles *)
module Count (O : CDH_RSR_Oracles) = {
  var ca, cb, cddh : int

  proc init () = {
    ca <- 0;
    cb <- 0;
    cddh <- 0;
  }

  proc oa (i : int) = {
    var r;

    ca <- ca + 1;
    r <@ O.oa(i);
    return r;
  }

  proc ob (i : int) = {
    var r;

    cb <- cb + 1;
    r <@ O.ob(i);
    return r;
  }

  proc oA = O.oA
  proc oB = O.oB

  proc ddh (m, i, j) = {
    var r;

    cddh <- cddh + 1;
    r <@ O.ddh(m, i, j);
    return r;
  }
}.

(* The actual CDH_RSR game: initialize oracles and counters and
dispatach to adversary *)
module Game (O : CDH_RSR_Oracles_i) (A : Adversary) = {
  module O' = Count(O)

  proc main () = {
    var r;

    O.init();
    O'.init();
    r <@ A(O').guess();
    return r;
  }
}.

(* The games G1 and G2 are the "real" and the "ideal" game defined in
cryptoprim.pdf *)
clone import FullRO as FROZ with
  type in_t    <- int,
  type out_t   <- Z,
  op dout      <- fun _ => dZ,
  type d_in_t  <- unit,
  type d_out_t <- bool.

clone FROZ.MkRO as RAZ.
clone FROZ.MkRO as RBZ.
module OAZ = RAZ.RO.
module OBZ = RBZ.RO.

module G1 : CDH_RSR_Oracles  = {
  proc init () = {
    OAZ.init();
    OBZ.init();
  }

  proc oa (i : int) = {
    var a;

    a <- e;
    if (0 <= i < na) a <@ OAZ.get(i);
    return a;
  }

  proc ob (j : int) = {
    var b;

    b <- e;
    if (0 <= j < nb) b <@ OBZ.get(j);
    return b;
  }

  proc oA (i : int) = {
    var a;

    a <- e;
    if (0 <= i < na) a <@ OAZ.get(i);
    return exp g a;
  }

  proc oB (j : int) = {
    var b;

    b <- e;
    if (0 <= j < nb) b <@ OBZ.get(j);
    return exp g b;
  }

  proc ddh (m, i, j) = {
    var a, b, r;

    a <- e;
    b <- e;
    r <- false;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <- OAZ.get(i);
      b <- OBZ.get(j);
      r <- m = exp g (a * b);
    }
    return r;
  }
}.

module G2 : CDH_RSR_Oracles = {
  include G1 [oA, oB]
  var ca, cb : int list

  proc init () = {
    G1.init();
    ca <- [];
    cb <- [];
  }

  proc oa (i : int) = {
    var a;

    a <- e;
    if (0 <= i < na) { 
      ca <- i :: ca;
      a <@ OAZ.get(i);
    }
    return a;
  }

  proc ob (j : int) = {
    var b;

    b <- e;
    if (0 <= j < nb) { 
      cb <- j :: cb;
      b <@ OBZ.get(j);
    }
    return b;
  }

  proc ddh (m, i, j) = {
    var a, b, r;

    a <- e;
    b <- e;
    r <- false;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <- OAZ.get(i);
      b <- OBZ.get(j);
      if (i \in ca \/ j \in cb) {
        r <- m = exp g (a * b);
      }
    }
    return r;
  }
}.

(* Intermediate games:
- G sets "bad" where G1 and G2 differ
- once "bad" has been set, G no longer logs queries to oa/ob *)
module G (OA : FROZ.RO, OB : FROZ.RO) : CDH_RSR_Oracles = {
  import var G2
  var bad : bool

  proc init () = {
    OA.init();
    OB.init();
    ca  <- [];
    cb  <- [];
    bad <- false;
  }

  proc oa (i : int) = {
    var a;

    a <- e;
    if (0 <= i < na) { 
      ca <- i :: ca;
      a <@ OA.get(i);
    }
    return a;
  }

  proc ob (j : int) = {
    var b;

    b <- e;
    if (0 <= j < nb) { 
      cb <- j :: cb;
      b <@ OB.get(j);
    }
    return b;
  }

  proc oA (i : int) = {
    var a;

    a <- e;
    if (0 <= i < na) a <@ OA.get(i);
    return exp g a;
  }

  proc oB (j : int) = {
    var b;

    b <- e;
    if (0 <= j < nb) b <@ OB.get(j);
    return exp g b;
  }

  proc ddh (m, i, j) = {
    var a, b, r, t;

    a <- e;
    b <- e;
    r <- false;
    t <- false;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OA.get(i);
      b <@ OB.get(j);
      t <- m = exp g (a * b);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
        bad <- bad \/ t;
      }
    }
    return r;
  }
}.

(* G' behaves like G, but samples invertible exponents (i.e. from EU *)
clone import FullRO as FROEU with
  type in_t   <- int,
  type out_t  <- Z,
  op dout     <- fun _ => duniform (elems EU),
  type d_in_t <- unit,
  type d_out_t <- bool.

clone FROEU.MkRO as RAEU.
clone FROEU.MkRO as RBEU.
module OAEU = RAEU.RO.
module OBEU = RBEU.RO.

module G' = G(OAEU, OBEU).

clone import Split as FROEU_S with
  type in_t   <- int,
  type out_t  <- Z,
  op dout     <- fun _ => duniform (elems EU),
  type d_in_t <- unit,
  type d_out_t <- bool.

clone import FROEU_S.SplitDomT as FROEUt.

clone FROEUt.MkROt as RAEUt.
clone FROEUt.MkROt as RBEUt.
module OAEUt = RAEUt.RO.
module OBEUt = RBEUt.RO.

(* We could do with only 2 oracles for sampling A in EU for our proofs but,
   with a view of having more meaningful names we do it with 3 oracles. *)
clone FROEU.MkRO as RA0EU.
clone FROEU.MkRO as RA1EU.
clone FROEU.MkRO as RB0EU.
clone FROEU.MkRO as RB1EU.
module OA0EU = RA0EU.RO.
module OA1EU = RA1EU.RO.
module OB0EU = RB0EU.RO.
module OB1EU = RB1EU.RO.

(* Proof outline:

1. |G1 - G2| = |G1b - G2b| <= G[bad]
2. G[bad] <= G'[bad] + "prob. of distinguishing dZ and duniform EU"
3. Define a game Gk that samples ia/ib and k \in [1..q_ddh] and show
   Stop if oa(i) or ob(j) gets logged where ia[i]/ib[j] is true
   G'[bad] <= q_ddh / ((1-pa)^q_oa * pa * (1 - pb)^q_ob * pb) Gk[ bad set at k-th call /\ !stop]
4. Define simulation S and an adversary B against the NCDH games
   Gk[ bad set at k-th call /\ !stop] <= S receives critical ddh call <= B wins NCDH game.
*)

(* Inner theory, parametric in the probability of inserting the NCDH problem *)
abstract theory Inner.

op pa, pb : real.
axiom pa_bound : 0%r < pa && if q_oa = 0 then pa <= 1%r else pa < 1%r.
axiom pb_bound : 0%r < pb && if q_ob = 0 then pb <= 1%r else pb < 1%r.

(* the "simulation", called "A" in cryptoprim.pdf :

We take gx and gy as parameters and use gx (rather than g) for
oA(i) when ia[i] = true. In order for the simulation to remain in sync
with the game G' (more precisely the intermediate game Gk' below), we
need to align the randomness for a and b by multiplying/dividing by x
(resp y) whenever ia[i] (resp ib[j]) is true. *)
module S = {
  import var G2
  var cddh, k : int
  var ia, ib  : bool list
  var gx, gy  : G
  var m_crit  : G

  proc init (gx' : G, gy' : G) = {
    ca   <- [];
    cb   <- [];
    cddh <- 0;
    k    <$ [1..q_ddh];
    ia   <$ dlist (dbiased pa) na;
    ib   <$ dlist (dbiased pb) nb;
    gx   <- gx';
    gy   <- gy';
    OAEU.init();
    OBEU.init();
  }

  proc oa (i : int) = {
    var a;

    a <- e;
    if (0 <= i < na) {
      if (!nth false ia i){
        ca <- i :: ca;
        a <@ OAEU.get(i);
      }
    }
    return a;
  }

  proc ob (j : int) = {
    var b;

    b <- e;
    if (0 <= j < nb) {
      if (!nth false ib j){
        cb <- j :: cb;
        b <@ OBEU.get(j);
      }
    }
    return b;
  }

  proc oA (i : int) = {
    var a;

    a <- e;
    if (0 <= i < na) a <@ OAEU.get(i);
    return (if nth false ia i then gx ^ a else exp g a);
  }

  proc oB (j : int) = {
    var b;

    b <- e;
    if (0 <= j < nb) b <@ OBEU.get(j);
    return (if nth false ib j then gy ^ b else exp g b);
  }

  proc ddh (m, i, j) = {
    var a, b, r;

    a <- e;
    b <- e;
    r <- false;
    cddh <- cddh + 1;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OAEU.get(i);
      b <@ OBEU.get(j);
      if (i \in ca \/ j \in cb) {
        if (i \in ca) {
          r <- m = (if nth false ib j then gy ^ b else exp g b) ^ a;
        }
        if (j \in cb) {
          r <- m = (if nth false ia i then gx ^ a else exp g a) ^ b;
        }
      } else {
          if (cddh = k) {
            m_crit <- m ^ (inv a * inv b);
        }
      }
    }
    return r;
  }
}.

(*
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

    if (0 <= i && i < na /\ 0 <= j && j < nb) {
      if (i \in ca) { (* i in ca => !nth false ia i *)
        if (nth false ib j) r <- m = gy^(nth' b j) ^ nth' a i;
                                 m = exp g (nth' b j * nth' a i);
        else                r <- m = exp g (nth' b j * nth' a i);
      } else if (j \in cb) { (* j in cb => !nth false ib j *)
        if (nth false ia i) r <- m = gx^(nth' a i) ^ nth' b j;
                                 m = exp g (nth' b j * nth' a i);
        else                r <- m = exp g (nth' b j * nth' a i);
      } else { (* !(i \in ca) /\ !(j \in cb) *)
        if (cddh = k) { m_crit <- m^(inv (nth' a i) * inv(nth' b j));
                        bad <- m^(inv (nth' a i) * inv(nth' b j)) = exp g (x * y);
                               m = exp g (y * nth' b j) ^ (x * nth' a i)
                               m = gy^(nth' b j) ^ (x * nth' a i) (* rnd rule to replace gy^(nth' b j) by exp g (nth' b j) *)
                               m = (exp g (nth' b j)) ^ (x * nth' a i)
                               m = (exp g ( x * nth' a i)) ^ (nth' b j)   (* rnd rule to replace gx^(nth' a i) by exp g (nth' a i) *)
                               m = exp g ((nth' a i) * (nth' b j)
      }
    }
    return r;
  }

 if (0 <= i && i < na /\ 0 <= j && j < nb) {
      if (i \in ca) { (* i in ca => !nth false ia i *)
                         r <- m = exp g (nth' b j * nth' a i);
      } else if (j \in cb) { (* j in cb => !nth false ib j *)
              r <- m = exp g (nth' b j * nth' a i);
      } else { (* !(i \in ca) /\ !(j \in cb) *)
        if (cddh = k) { m_crit <- m^(inv (nth' a i) * inv(nth' b j));
                        bad <- m^(inv (nth' a i) * inv(nth' b j)) = exp g (x * y);
                               m = exp g (y * nth' b j) ^ (x * nth' a i)
                               m = gy^(nth' b j) ^ (x * nth' a i) (* rnd rule to replace gy^(nth' b j) by exp g (nth' b j) *)
                               m = (exp g (nth' b j)) ^ (x * nth' a i)
                               m = (exp g (nth' a i)) ^ (nth' b j)   (* rnd rule to replace gy^(nth' b j) by exp g (nth' b j) *)
                               m = exp g ((nth' a i) * (nth' b j)
      }
    }
}.
*)

(*
module S = {
  import var G2
  var cddh, k : int
  var ia, ib : bool list (* inject a/b *)
  var gx, gy : G
  var m_crit : G

  proc init (gx' : G, gy' : G) = {
    OAEU.init();
    OBEU.init();
    ca   <- [];
    cb   <- [];
    cddh <- 0;
    k    <$ [1..q_ddh];
    ia   <$ dlist (dbiased pa) na;
    ib   <$ dlist (dbiased pb) nb;
    gx   <- gx';
    gy   <- gy';
  }

  proc oa (i : int) = {
    var a;

    if (cddh < k) ca <- i :: ca;
    a <@ OAEU.get(i);
    return a;
  }

  proc ob (j : int) = {
    var b;

    if (cddh < k) cb <- j :: cb;
    b <@ OBEU.get(j);
    return b;
  }

  proc oA (i : int) = {
    var a;

    a <@ OAEU.get(i);
    return (if nth false ia i then gx ^ a else exp g a);
  }

  proc oB (j : int) = {
    var b;

    b <@ OBEU.get(j);
    return (if nth false ib j then gy ^ b else exp g b);
  }

  proc ddh (m, i, j) = {
    var a, b, r;

    a <- e;
    b <- e;
    r <- false;
    cddh <- cddh + 1;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OAEU.get(i);
      b <@ OBEU.get(j);
      if (i \in ca \/ j \in cb) {
        if (i \in ca) {
          r <- m = (if nth false ib j then gy ^ b else exp g b ^ a);
        }
        if (j \in cb) {
          r <- m = (if nth false ia i then gx ^ a else exp g a ^ b);
        }
      } else {
        (* record k-th query *)
        if (cddh = k) {
          m_crit <- m ^ (inv a * inv b);
        }
      }
    }
    return r;
  }
}.
*)

module GameS (A : Adversary) = {
  module O' = Count(S)

  proc main(gx : G, gy : G) = {
    var r;

    S.init(gx, gy);
    O'.init();
    r <@ A(O').guess();
    return r;
  }
}.

(* adversary against CDH problem for nominal groups *)
module B (A : Adversary) : NCDH.Adversary = {
  proc solve(gx gy : G) : G = {
    GameS(A).main(gx, gy);
    return S.m_crit;
  }
}.

clone import FullRO as FROG with
  type in_t   <- int,
  type out_t  <- G,
  op dout     <- fun _ => dmap (duniform (elems EU)) (exp g),
  type d_in_t <- unit,
  type d_out_t <- bool.

clone FROG.MkRO as RAG.
clone FROG.MkRO as RBG.
module OAG = RAG.RO.
module OBG = RBG.RO.

(*
module Sx = {
  import var G2
  var cddh, k : int
  var ia, ib : bool list (* inject a/b *)
  var gx, gy : G
  var m_crit : G

  proc init (x' : Z, y' : Z) = {
    OAG.init();
    OBG.init();
    ca   <- [];
    cb   <- [];
    cddh <- 0;
    k    <$ [1..q_ddh];
    ia   <$ dlist (dbiased pa) na;
    ib   <$ dlist (dbiased pb) nb;
    gx   <- exp g x';
    gy   <- exp g y';
  }

  proc oa (i : int) = {
    var a;

    if (cddh < k) ca <- i :: ca;
    a <@ OAG.get(i);
    return (elog a);
  }

  proc ob (j : int) = {
    var b;

    if (cddh < k) cb <- j :: cb;
    b <@ OBG.get(j);
    return (elog b);
  }

  proc oA (i : int) = {
    var a;

    a <@ OAG.get(i);
    return (if nth false ia i then a ^ (elog gx) else a);
  }

  proc oB (j : int) = {
    var b;

    b <@ OBG.get(j);
    return (if nth false ib j then b ^ (elog gy) else b);
  }

  proc ddh (m, i, j) = {
    var a, b, r;

    a <- g;
    b <- g;
    r <- false;
    cddh <- cddh + 1;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OAG.get(i);
      b <@ OBG.get(j);
      if (i \in ca \/ j \in cb) {
        if (i \in ca) {
          r <- m = (if nth false ib j then b ^ (elog gy) else b) ^ (elog a);
        }
        if (j \in cb) {
          r <- m = (if nth false ia i then a ^ (elog gx) else a) ^ (elog b);
        }
      } else {
        (* record k-th query *)
        if (cddh = k) {
          m_crit <- m ^ (inv (elog a) * inv (elog b));
        }
      }
    }
    return r;
  }
}.

(* the simulation game *)

module GameSx (A : Adversary) = {
  module O' = Count(Sx)

  proc main(x : Z, y : Z) = {
    var r;
    Sx.init(x, y);
    O'.init();
    r <@ A(O').guess();
    return r;
  }
}.
*)

op DELTA = (na + nb)%r * sdist dZ (duniform (elems EU)).

axiom dZ_ll : is_lossless dZ.
hint exact random : dZ_ll.

lemma dEU_ll : is_lossless (duniform (elems EU)).
proof. by smt(duniform_ll e_EU). qed.
hint exact random : dEU_ll.

lemma dG_ll : is_lossless (dmap (duniform (elems EU)) (exp g)).
proof. by smt(dEU_ll dmap_ll). qed.

section.

declare module A : Adversary {G1, G2, G, S, Count,
                              OAEU, OBEU, OAEUt, OBEUt,
                              OA0EU, OA1EU, OB0EU, OB1EU,
                              RO, RO_DOMt, ROT.RO, ROF.RO, FROEUt.RO,
                              OAG, OBG}.

axiom A_ll : forall (O <: CDH_RSR_Oracles{A}),
  islossless O.oA =>
  islossless O.oB =>
  islossless O.oa =>
  islossless O.ob =>
  islossless O.ddh =>
  islossless A(O).guess.

axiom A_bound : forall (O <: CDH_RSR_Oracles{A}),
  hoare [A(Count(O)).guess :
         Count.ca = 0 /\ Count.cb = 0 /\ Count.cddh = 0 ==>
         Count.ca <= q_oa /\ Count.cb <= q_ob /\ Count.cddh <= q_ddh].

local module G1b = {
  import var G2
  include var G(OAZ, OBZ) [-ddh]

  proc ddh (m, i, j) = {
    var a, b, r;

    a <- e;
    b <- e;
    r <- false;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <- OAZ.get(i);
      b <- OBZ.get(j);
      r <- m = exp g (a * b);
      bad <- bad \/ (r /\ !(i \in ca \/ j \in cb));
    }
    return r;
  }
}.

local module G2b = {
  include G(OAZ, OBZ) [-oa, ob]
  include G2          [ oa, ob]
}.

local lemma G1G2_Gbad &m :
  `| Pr[Game(G1, A).main() @ &m : res] - Pr[Game(G2, A).main() @ &m : res] | <=
  Pr[Game(G(OAZ, OBZ), A).main() @ &m : G.bad].
proof.
(* Introduce bad events into G1 and G2 *)
have -> : Pr[Game(G1,  A).main() @ &m : res] =
          Pr[Game(G1b, A).main() @ &m : res].
- by byequiv => //; proc; inline *; sim.
have -> : Pr[Game(G2,  A).main() @ &m : res] =
          Pr[Game(G2b, A).main() @ &m : res].
- byequiv => //; proc; inline *.
  call (: ={OAZ.m, OBZ.m, G2.ca, G2.cb}); 1..4: (by sim); 2: by auto.
  by proc; inline *; sp; if; auto.
(* we can continue logging oa/ob queries once bad happens *)
have -> : Pr[Game(G(OAZ, OBZ), A).main() @ &m : G.bad] =
          Pr[Game(G2b,         A).main() @ &m : G.bad].
- byequiv => //; proc; inline *.
  call (: G.bad, ={OAZ.m, OBZ.m, G2.ca, G2.cb, G.bad}, ={G.bad});
    2..7, 9, 10, 12, 13: by (sim /> || (move => *; conseq />; islossless)).
  + by exact: A_ll.
  + by proc; inline *; sp; if;1:smt(); auto.
  + by proc; inline *; sp; if;1:smt(); auto.
  + by conseq (: _ ==> ={OAZ.m, OBZ.m, G2.ca, G2.cb, G.bad, res}) => //; sim.
  + move=> *; proc.
    inline G(OAZ, OBZ).ddh; sp; if; auto.
    by conseq (: true); [smt() | islossless].
  + move=> *; proc.
    inline G2b.ddh; sp; if; auto.
    by conseq (: true); [smt() | islossless].
  + by auto => /> /#.
byequiv (_ : ={glob A} ==> ={G.bad} /\ (! G.bad{2} => ={res})) : G.bad => //;
[proc; inline * | smt()].
call (_ : G.bad, ={OAZ.m, OBZ.m, G2.ca, G2.cb, G.bad}, ={G.bad});
  2..7, 9, 10, 12, 13: by (sim /> || (move => *; conseq />; islossless)).
- by exact: A_ll.
- by proc; inline *; sp; if;1:smt(); auto. 
- by proc; inline *; sp; if;1:smt(); auto.
- proc; inline G1b.ddh G2b.ddh; sp.
  if => //; 2: by auto.
  wp; call(: ={OBZ.m}); 1: by sim.
  call(: ={OAZ.m}); 1: by sim.
  by auto => /> /#.
- move=> *; proc.
  inline G1b.ddh; sp; if; auto.
  by conseq (: true); 1: smt(); islossless.
- move=> *; proc.
  inline G2b.ddh; sp; if; auto.
  by conseq (: true); 1: smt(); islossless.
- by auto => /> /#.
qed.

(** Expressing the games G, G' and G'' as distinguishers for statistical distance *)
(*
local module Ba : Da.Distinguisher = {
  import var G1 G2 G

  module O' = Count(G)

  proc guess (a' : Z list) = {
    a <- a';
    b <$ dlist dZ nb;
    ca <- [];
    cb <- [];
    bad <- false;
    O'.init();
    A(O').guess();
    return G.bad;
  }
}.

local module Bb : Db.Distinguisher = {
  import var G1 G2 G

  module O' = Count(G)

  proc guess (b' : Z list) = {
    a <$ dlist (duniform (elems EU)) na;
    b <- b';
    ca <- [];
    cb <- [];
    bad <- false;
    O'.init();
    A(O').guess();
    return G.bad;
  }
}.
*)

(* what about res, do we care? *)
local lemma G_G' &m :
  `| Pr[Game(G(OAZ, OBZ), A).main() @ &m : G.bad] -
     Pr[Game(G',         A).main() @ &m : G.bad] | <=
  DELTA.
proof.
admitted.
(*
rewrite /DELTA.
have H1 : `| Pr[ Game(G,A).main() @ &m : G.bad ] - Pr[ Game(G'',A).main() @ &m : G.bad ] |
          <= na%r * sdist dZ (duniform (elems EU)).
  have -> : Pr[ Game(G,A).main() @ &m : G.bad ] = Pr[ Da.SampleDlist(Ba).main(false) @ &m : res ].
    byequiv => //; proc; inline *.
    rcondt {2} 2; 1: (by auto); rcondf {2} 3; 1: by auto.
    wp; call(: ={glob G, glob G1, glob G2}); 1..5: by sim.
    by auto.
  have -> : Pr[ Game(G'',A).main() @ &m : G.bad ] = Pr[ Da.SampleDlist(Ba).main(true) @ &m : res ].
    byequiv => //; proc; inline *.
    rcondf {2} 2; 1: (by auto); rcondt {2} 2; 1: by auto.
    wp; call(: ={glob G, glob G1, glob G2}); 1..5: by sim.
    by auto.
  exact (Da.sdist_dlist &m Ba).
have H2 : `| Pr[ Game(G'',A).main() @ &m : G.bad ] - Pr[ Game(G',A).main() @ &m : G.bad ] |
          <= nb%r * sdist dZ (duniform (elems EU)).
  have -> : Pr[ Game(G'',A).main() @ &m : G.bad ] = Pr[ Db.SampleDlist(Bb).main(false) @ &m : res ].
    byequiv => //; proc; inline *.
    rcondt {2} 2; 1: (by auto); rcondf {2} 3; 1: by auto.
    wp; call(: ={glob G, glob G1, glob G2}); 1..5: by sim.
    by swap {2} 4 -3; auto.
  have -> :  Pr[ Game(G',A).main() @ &m : G.bad ] = Pr[ Db.SampleDlist(Bb).main(true) @ &m : res ].
    byequiv => //; proc; inline *.
    rcondf {2} 2; 1: (by auto); rcondt {2} 2; 1: by auto.
    wp; call(: ={glob G, glob G1, glob G2}); 1..5: by sim.
    by swap {2} 4 -3; auto.
  exact (Db.sdist_dlist &m Bb).
smt().
qed.
*)

local module Gk (OA : FROEU.RO, OB : FROEU.RO) : CDH_RSR_Oracles_i = {
  import var G2 G
  include var G(OA, OB) [oA, oB]
  var cddh, i_k, j_k, k : int
  var ia, ib            : bool list

  proc init () = {
    G(OA, OB).init();
    cddh  <- 0;
    i_k   <- -1;
    j_k   <- -1;
    k     <$ [1..q_ddh];
    ia    <$ dlist (dbiased pa) na;
    ib    <$ dlist (dbiased pb) nb;
  }

  proc oa (i : int) = {
    var a;

    a <- e;
    if (0 <= i < na) {
      if (i <> i_k) {
        ca <- i :: ca;
        a <@ OA.get(i);
      }
    }
    return a;
  }

  proc ob (j : int) = {
    var b;

    b <- e;
    if (0 <= j < nb) {
      if (j <> j_k) {
        cb <- j :: cb;
        b <@ OB.get(j);
      }
    }
    return b;
  }

  proc ddh (m, i, j) = {
    var a, b, r, t;

    a <- e;
    b <- e;
    r <- false;
    t <- false;
    cddh <- cddh + 1;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OA.get(i);
      b <@ OB.get(j);
      t <- m = exp g (a * b);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ cddh = k /\ ! bad) {
            bad <- true;
            i_k <- i;
            j_k <- j;
        }
      }
    }
    return r;
  }
}.

(* Same as Gk, but record number of ddh query that sets bad. *)
local module Gk_bad (OA : FROEU.RO, OB : FROEU.RO) : CDH_RSR_Oracles_i = {
  import var G2 G
  include var Gk(OA, OB) [oA, oB]
  var k_bad   : int
  var query_k : bool

  proc init () = {
    Gk(OA, OB).init();
    k_bad   <- -1;
    query_k <- false;
  }

  proc oa (i : int) = {
    var a;

    a <- e;
    if (0 <= i < na) {
      if (i <> i_k) {
        ca <- i :: ca;
        a <@ OA.get(i);
      } else {
        query_k <- true;
      }
    }
    return a;
  }

  proc ob (j : int) = {
    var b;

    b <- e;
    if (0 <= j < nb) {
      if (j <> j_k) {
        cb <- j :: cb;
        b <@ OB.get(j);
      } else {
        query_k <- true;
      }
    }
    return b;
  }

  proc ddh(m, i, j) = {
    var a, b, r, t;

    a <- e;
    b <- e;
    r <- false;
    t <- false;
    cddh <- cddh + 1;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OA.get(i);
      b <@ OB.get(j);
      t <- m = exp g (a * b);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ ! bad) {
            bad <- true;
            k_bad <- cddh;
            i_k <- i;
            j_k <- j;
        }
      }
    }
    return r;
  }
}.

op nstop (bs : bool list) (is : int list) (i : int) =
  (forall i, i \in is => ! nth false bs i) /\ nth false bs i.

(* should be an equality, but this suffices *)
local lemma Gk_Gk_bad &m :
  Pr[Game(Gk_bad(OAEU, OBEU), A).main() @ &m :
     G.bad /\ Gk.k = Gk_bad.k_bad /\
     nstop Gk.ia G2.ca Gk.i_k /\ nstop Gk.ib G2.cb Gk.j_k] <=
  Pr[Game(Gk(OAEU, OBEU), A).main() @ &m :
     G.bad /\ nstop Gk.ia G2.ca Gk.i_k /\ nstop Gk.ib G2.cb Gk.j_k].
proof.
byequiv => //; proc; inline *; symmetry.
call (: G.bad /\ Gk.k <> Gk_bad.k_bad,
        ={OAEU.m, OBEU.m, G2.ca, G2.cb, G.bad} /\
        ={cddh, i_k, j_k, k}(Gk, Gk) /\
        (G.bad <=> Gk.k = Gk_bad.k_bad){2});
  try by (sim /> || (move => *; conseq />; islossless)).
- by exact A_ll.
- by proc; inline *; sp; if; auto => /#.
- move => {&m} &m; proc; inline *; sp; if; auto; smt(dEU_ll).
- by auto; smt(supp_dinter).
qed.

(* Variant of Game, where the samling for Gk is done at the end *)
(*
local module Game' (O : CDH_RSR_Oracles_i) (A : Adversary) = {
  var k : int
  var ia, ib : bool list

  proc main () = {
    Game(O, A).main();
    k  <$ [1..q_ddh];
    ia <$ dlist (dbiased pa) na;
    ib <$ dlist (dbiased pb) nb;
  }
}.

local module Gk_lazy (OA : FROEU.RO, OB : FROEU.RO) : CDH_RSR_Oracles_i = {
  import var G2 G
  include var Gk(OA, OB) [-init]

  proc init() = {
    G(OA, OB).init();
    k_bad <- -1;
    i_k   <- -1;
    j_k   <- -1;
    cddh  <- 0;
  }
}.
*)

(*
local lemma Game_Game' &m :
  Pr[Game(Gk(OAEU, OBEU), A).main() @ &m :
     G.bad /\ Gk.k = Gk.k_bad /\ nstop Gk.ia Gk.ib G2.ca G2.cb /\
     nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k] =
  Pr[Game'(Gk_lazy(OAEU, OBEU), A).main() @ &m :
     G.bad /\ Game'.k = Gk.k_bad /\ nstop Game'.ia Game'.ib G2.ca G2.cb /\
     nth false Game'.ia Gk.i_k /\ nth false Game'.ib Gk.j_k].
proof.
byequiv => //; proc; inline *; swap{2} 13 3.
call (: ={OAEU.m, OBEU.m, G2.ca, G2.cb, G.bad} /\
        ={cddh, i_k, j_k, k_bad}(Gk, Gk));
  3..5: by proc; inline *; sim.
- by proc; call (: ={OAEU.m}); [sim | auto].
- by proc; call (: ={OBEU.m}); [sim | auto].
- by auto.
qed.
*)

(* hoare logic properties of Gk *)
(*
local lemma Gk_hoare :
  hoare [Game(Gk(OAEU, OBEU), A).main :
         true ==>
         size G2.ca <= q_oa /\ size G2.cb <= q_ob /\ Gk.cddh <= q_ddh /\
         (G.bad => Gk.k_bad \in [1..q_ddh] /\
                  (0 <= Gk.i_k < na) /\ (0 <= Gk.j_k < nb))].
proof.
conseq (: _ ==> Count.cddh = Gk.cddh /\ 0 <= Gk.cddh /\
                (Gk.cddh <= q_ddh =>
                  (size G2.ca <= Count.ca /\ size G2.cb <= Count.cb /\
                  (G.bad => Gk.k_bad \in [1..q_ddh] /\
                            (0 <= Gk.i_k < na) /\ (0 <= Gk.j_k < nb)))))
       (: _ ==> Count.ca <= q_oa /\ Count.cb <= q_ob /\ Count.cddh <= q_ddh);
  2: (by proc; seq 2 : (Count.ca = 0 /\ Count.cb = 0 /\ Count.cddh = 0);
         [by inline *; auto|by call (A_bound (Gk(OAEU, OBEU)))]); 1: smt().
proc; inline *.
call (: Count.cddh = Gk.cddh /\ 0 <= Gk.cddh /\
        (Gk.cddh <= q_ddh =>
                (size G2.ca <= Count.ca /\ size G2.cb <= Count.cb /\
                (G.bad => Gk.k_bad \in [1..q_ddh] /\
                          (0 <= Gk.i_k < na) /\ (0 <= Gk.j_k < nb))))).
- by proc; call (: true); auto.
- by proc; call (: true); auto.
- proc; inline Gk_lazy(OAEU, OBEU).oa; sp; wp.
  by call (: true); auto => /#.
- proc; inline Gk_lazy(OAEU, OBEU).ob; sp; wp.
  by call (: true); auto => /#.
- proc; inline Gk_lazy(OAEU, OBEU).ddh; sp; if; auto; 2 :smt().
  call (: true); auto.
  by call (: true); auto; smt(supp_dinter).
- by auto.
qed.
*)

local lemma guess_bound &m :
  1%r / q_ddh%r * (1%r - pa) ^ q_oa * (1%r - pb) ^ q_ob * pa * pb *
  Pr[Game(G', A).main() @ &m : G.bad] <=
  Pr[Game(Gk(OAEU, OBEU), A).main() @ &m :
     G.bad /\ nstop Gk.ia G2.ca Gk.i_k /\ nstop Gk.ib G2.cb Gk.j_k].
proof.
pose p := Pr[Game(G', A).main() @ &m : G.bad].
pose c := (1%r - pa) ^ q_oa * pa * (1%r - pb) ^ q_ob * pb.
apply (ler_trans _ _ _ _ (Gk_Gk_bad &m)).
byphoare (_ : glob A = (glob A){m} ==> _) => //.
proc; inline *; swap [10..11] 6; swap 9 6.
seq 14 : G.bad p (1%r / q_ddh%r * c) _ 0%r
         (size G2.ca <= q_oa /\ size G2.cb <= q_ob /\
          (G.bad => Gk_bad.k_bad \in [1..q_ddh] /\
                    0 <= Gk.i_k < na /\ 0 <= Gk.j_k < nb) /\
         ! (Gk.i_k \in G2.ca) /\ ! (Gk.j_k \in G2.cb));
  4, 5: by auto; smt().
- conseq (: _ ==> Count.cddh = Gk.cddh /\  0 <= Gk.cddh /\
                  size G2.ca <= Count.ca /\ size G2.cb <= Count.cb /\
                  (G.bad => (Gk.cddh <= q_ddh => Gk_bad.k_bad \in [1..q_ddh]) /\
                            0 <= Gk.i_k < na /\ 0 <= Gk.j_k < nb) /\
                  ! (Gk.i_k \in G2.ca) /\ ! (Gk.j_k \in G2.cb))
         (: _ ==> Count.ca <= q_oa /\ Count.cb <= q_ob /\ Count.cddh <= q_ddh);
  [ | smt () | seq 13 : (Count.ca = 0 /\ Count.cb = 0 /\ Count.cddh = 0) | ];
  auto; 1: by call (A_bound (Gk_bad(OAEU, OBEU))).
  call (: Count.cddh = Gk.cddh /\ 0 <= Gk.cddh /\
          size G2.ca <= Count.ca /\ size G2.cb <= Count.cb /\
          (G.bad => (Gk.cddh <= q_ddh => Gk_bad.k_bad \in [1..q_ddh]) /\
                    0 <= Gk.i_k < na /\ 0 <= Gk.j_k < nb) /\
          ! (Gk.i_k \in G2.ca) /\ ! (Gk.j_k \in G2.cb)); 
    1,2 : (by proc; sp;if; 2: (by auto); call (: true)); 4: by inline *; auto.
  + proc; inline Gk_bad(OAEU, OBEU).oa; sp; wp. 
    if; 2: by auto; smt(). if; 2: by auto; smt().
    call (: true); auto => /> *; split => [/# | ].
    admit.
  + proc; inline Gk_bad(OAEU, OBEU).ob; sp; wp. 
    if; 2: by auto; smt(). if; 2: by auto; smt().
    call (: true); auto => /> *; split => [/# | ].
    admit.
  + proc; inline Gk_bad(OAEU, OBEU).ddh; sp; wp; if; 2: by auto; smt().
    by auto; call (: true) => //; call (: true) => //; auto; smt(supp_dinter).
- call (: (glob A) = (glob A){m} /\ OAEU.m = empty /\ OBEU.m = empty /\
          G2.ca = [] /\ G2.cb = [] /\ G.bad = false /\
          Gk_bad.query_k = false ==> G.bad); 2: by inline *; auto.
  bypr=> &m' gA; rewrite /p.
  byequiv (: ={glob A} /\ OAEU.m{2} = empty /\ OBEU.m{2} = empty /\
             G2.ca{2} = [] /\ G2.cb{2} = [] /\ G.bad{2} = false /\
             Gk_bad.query_k{2} = false ==> _) => //; 2: smt().
  proc *; inline *; wp.
  call (: Gk_bad.query_k,

          ={OAEU.m, OBEU.m, G2.ca, G2.cb, G.bad},

          G.bad{2});
    2..7, 9, 12: (by move => *; proc; inline *; sp; if; auto; smt(dEU_ll)).
  + by exact A_ll.
  + admit.
  + by move => *; proc; inline *; sp; if; 2: (by auto); if; auto; smt(dEU_ll).
  + admit.
  + by move => *; proc; inline *; sp; if; 2: (by auto); if; auto; smt(dEU_ll).
  + by proc; inline *; sp; if; 1,3: (by auto); auto; smt().
  + move => *; proc; inline *; sp; if; 2: (by auto); auto; smt(dEU_ll).
  + move => *; proc; inline *; sp; if; 2: (by auto); auto; smt(dEU_ll).  
  + auto; smt().
- seq 1 : (Gk.k = Gk_bad.k_bad) (1%r / q_ddh%r) c _ 0%r
          (G.bad /\ size G2.ca <= q_oa /\ size G2.cb <= q_ob /\
           0 <= Gk.i_k && Gk.i_k < na /\ 0 <= Gk.j_k && Gk.j_k < nb /\
           ! (Gk.i_k \in G2.ca) /\ ! (Gk.j_k \in G2.cb));
    1, 4, 5: by auto; smt().
  + rnd; skip => &m' /> *; rewrite (mu_eq _ _ (pred1 Gk_bad.k_bad{m'})) //.
    by rewrite dinter1E; smt (supp_dinter).
  + rewrite /c => {c p}; pose p := (fun b => b = false).
    pose IP := fun (cs : int list) (is : bool list) (n : int) =>
                 forall (i : int), i \in oflist cs `&` oflist (range 0 n) =>
                                     p (nth false is i).
    pose JP := fun (c : int) (is : bool list) (n : int) =>
                 forall (j : int), j \in fset1 c `&` oflist (range 0 n) =>
                                   ! p (nth false is j).
    have ? := pa_bound; have ? := pb_bound; have ? := na_ge0; have ? := nb_ge0.
    seq 1 : (nstop Gk.ia G2.ca Gk.i_k)
            ((1%r - pa) ^ q_oa * pa) ((1%r - pb) ^ q_ob * pb) _ 0%r
            (G.bad /\ Gk.k = Gk_bad.k_bad /\ size G2.cb <= q_ob /\
             0 <= Gk.j_k && Gk.j_k < nb /\ ! (Gk.j_k \in G2.cb));
      1, 4, 5: by auto; smt().
    * rnd; skip => {&m} &m /> _ s_ca _ ik_ge0 ik_ltna _ _ ik_nca _.
      rewrite (mu_eq_support _ _ (fun (x : bool list) =>
                                    IP G2.ca{m} x na /\ JP Gk.i_k{m} x na));
        1: by move => ia /= /(supp_dlist_size _ _ _ na_ge0) size_ia;
              smt (fset1I in_filter mem_oflist mem_range nth_default nth_neg).
      rewrite dlist_set2E //; 1: (by exact: dbiased_ll);
        1..3: smt(mem_oflist mem_range in_fsetI in_fset1).
      rewrite !dbiasedE /p /predC /= fset1I clamp_id 1: /#.
      rewrite mem_oflist mem_range ik_ge0 ik_ltna /= fcard1 expr1.
      apply ler_wpmul2r; 1: smt().
      apply ler_wiexpn2l; smt(fcard_ge0 fcard_oflist subsetIl subset_leq_fcard).
    * seq 1 : (nstop Gk.ib G2.cb Gk.j_k)
              ((1%r - pb) ^ q_ob * pb) 1%r _ 0%r
              (G.bad /\ Gk.k = Gk_bad.k_bad /\ nstop Gk.ia G2.ca Gk.i_k);
        1, 3..5: by auto; smt().
      rnd; skip => &m' /> _ s_cb jk_ge0 jk_ltnb jk_ncb _ _.
      rewrite (mu_eq_support _ _ (fun (x : bool list) =>
                                    IP G2.cb{m'} x nb /\ JP Gk.j_k{m'} x nb));
        1: by move => ia /= /(supp_dlist_size _ _ _ nb_ge0) size_ia;
              smt (fset1I in_filter mem_oflist mem_range nth_default nth_neg).
      rewrite dlist_set2E //; 1: (by exact: dbiased_ll);
        1..3: smt(mem_oflist mem_range in_fsetI in_fset1).
      rewrite !dbiasedE /p /predC /= fset1I clamp_id 1: /#.
      rewrite mem_oflist mem_range jk_ge0 jk_ltnb /= fcard1 expr1.
      apply ler_wpmul2r; 1: smt().
      apply ler_wiexpn2l; smt(fcard_ge0 fcard_oflist subsetIl subset_leq_fcard).
qed.

(*
local lemma guess_bound &m :
  1%r / q_ddh%r * (1%r - pa) ^ q_oa * (1%r - pb) ^ q_ob *
  Pr[Game(G', A).main() @ &m : G.bad] <=
  Pr[Game(Gk(OAEU, OBEU), A).main() @ &m :
     G.bad /\ Gk.k = Gk.k_bad /\ nstop Gk.ia Gk.ib G2.ca G2.cb].
proof.
pose p := Pr[Game(G', A).main() @ &m : G.bad].
pose c := (1%r - pa) ^ q_oa * (1%r - pb) ^ q_ob.
rewrite Game_Game'; byphoare (_ : glob A = (glob A){m} ==> _) => //; proc.
seq 1 : G.bad p (1%r / q_ddh%r * c) _ 0%r
        (size G2.ca <= q_oa /\ size G2.cb <= q_ob /\
        (G.bad => Gk.k_bad \in [1..q_ddh]));
  4, 5: by auto; smt().
- by call Gk_hoare; skip; smt().
- call (: (glob A) = (glob A){m} ==> G.bad); 2: by auto.
  bypr => &m' gA; rewrite /p; byequiv => //; proc; inline *.
  call (: ={OAEU.m, OBEU.m, G2.ca, G2.cb, G.bad}); 1..4: (by sim);
  [by proc; inline *; auto; sp; if; auto => /# | by auto; smt()].
- seq 1 : (Game'.k = Gk.k_bad) (1%r / q_ddh%r) c _ 0%r
          (G.bad /\ size G2.ca <= q_oa /\ size G2.cb <= q_ob);
    1, 4, 5: by auto; smt().
  + rnd; skip => &m' /> *.
    by rewrite (mu_eq _ _ (pred1 Gk.k_bad{m'})) // dinter1E; smt (supp_dinter).
  + rewrite /c => {c p}; pose p := (fun b => b = false).
    pose IP := fun (cs : int list) (is : bool list) (n : int) =>
                 forall (i : int), i \in oflist cs `&` oflist (range 0 n) =>
                                     p (nth false is i).
    have ? := pa_bound; have ? := pb_bound; have ? := na_ge0; have ? := nb_ge0.
    seq 1 : ((forall i, i \in G2.ca => nth false Game'.ia i = false))
            ((1%r - pa) ^ q_oa) ((1%r - pb) ^ q_ob) _ 0%r
            (G.bad /\ Game'.k = Gk.k_bad /\ size G2.cb <= q_ob);
      1, 4, 5: by auto; smt().
    * rnd; skip => {&m} &m /> _ s_ca _.
      rewrite (mu_eq_support _ _ (fun (x : bool list) => IP G2.ca{m} x na));
        1: by move => ia /(supp_dlist_size _ _ _ na_ge0) size_ia;
              smt (in_filter mem_oflist mem_range nth_default nth_neg).
      rewrite dlist_setE //; 1: (by exact: dbiased_ll);
        1: by smt(mem_oflist mem_range in_fsetI).
      rewrite dbiasedE /p /predC /= clamp_id 1: /#.
      apply ler_wiexpn2l; smt(fcard_oflist subsetIl subset_leq_fcard fcard_ge0).
    * seq 1 : ((forall j, j \in G2.cb => nth false Game'.ib j = false))
              ((1%r - pb) ^ q_ob) 1%r _ 0%r
              (G.bad /\ Game'.k = Gk.k_bad /\
               (forall (i : int), i \in G2.ca =>
                                  nth false Game'.ia i = false));
        1, 3..5: by auto; smt().
      rnd; skip => &m' /> _ s_cb _.
      rewrite (mu_eq_support _ _ (fun (x : bool list) => IP G2.cb{m'} x nb));
        1: by move => ib /(supp_dlist_size _ _ _ nb_ge0) size_ia;
              smt (in_filter mem_oflist mem_range nth_default nth_neg).
      rewrite dlist_setE //; 1: (by exact: dbiased_ll);
        1: smt(mem_oflist mem_range in_fsetI).
      rewrite !dbiasedE /p /predC /= clamp_id 1: /#.
      apply ler_wiexpn2l; smt(fcard_oflist subsetIl subset_leq_fcard fcard_ge0).
qed.
*)

local module Gkt (OA : FROEUt.ROt, OB : FROEUt.ROt) : CDH_RSR_Oracles_i = {
  import var G2 G Gk
(*
  var ca, cb : int list
  var bad : bool
  var cddh, i_k, j_k, k : int
  var ia, ib : bool list
*)

  proc init () = {
    ca    <- [];
    cb    <- [];
    bad   <- false;
    cddh  <- 0;
    i_k   <- -1;
    j_k   <- -1;
    k     <$ [1..q_ddh];
    ia    <$ dlist (dbiased pa) na;
    ib    <$ dlist (dbiased pb) nb;
    OA.init(nth false ia);
    OB.init(nth false ib);
  }

  proc oa (i : int) = {
    var a;

    if (! bad) ca <- i :: ca;
    a <@ OA.get(i);
    return a;
  }

  proc ob (j : int) = {
    var b;

    if (! bad) cb <- j :: cb;
    b <@ OB.get(j);
    return b;
  }

  proc oA (i : int) = {
    var a;

    a <@ OA.get(i);
    return exp g a;
  }

  proc oB (j : int) = {
    var b;

    b <@ OB.get(j);
    return exp g b;
  }

  proc ddh (m, i, j) = {
    var a, b, r, t;

    a <- e;
    b <- e;
    r <- false;
    t <- false;
    cddh <- cddh + 1;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OA.get(i);
      b <@ OB.get(j);
      t <- m = exp g (a * b);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ cddh = k /\ ! bad) {
            bad <- true;
            i_k <- i;
            j_k <- j;
        }
      }
    }
    return r;
  }
}.

local lemma Gk'_Gkt &m :
  Pr[Game(Gk(OAEU, OBEU), A).main() @ &m :
     G.bad /\ nstop Gk.ia G2.ca Gk.i_k /\ nstop Gk.ib G2.cb Gk.j_k] =
  Pr[Game(Gkt(OAEUt, OBEUt), A).main() @ &m :
     G.bad /\ nstop Gk.ia G2.ca Gk.i_k /\ nstop Gk.ib G2.cb Gk.j_k].
proof.
(*
byequiv => //; proc; inline *.
call (: ={m}(OAEU, OAEUt) /\ ={m}(OBEU, OBEUt) /\
        ={G2.ca, G2.cb, G.bad} /\ ={cddh, i_k, j_k, k}(Gk, Gk));
  1..5: by (proc; inline *; sim).
by auto. *) admit.
qed.

local module DA (OB : FROEUt.ROt, A : Adversary, OA : FROEUt.ROt) = {
  import var G2 G Gk
  module O = Count(Gkt(OA, OB))

  proc get_test() = {
    var test;

    ca    <- [];
    cb    <- [];
    bad   <- false;
    k     <$ [1..q_ddh];
    i_k   <- -1;
    j_k   <- -1;
    cddh  <- 0;
    ia    <$ dlist (dbiased pa) na;
    ib    <$ dlist (dbiased pb) nb;
    OB.init(nth false ib);
    test <- nth false ia;
    return test;
  }

  proc distinguish () = {
    O.init();
    A(O).guess();
    return (G.bad /\ nstop Gk.ia G2.ca Gk.i_k /\ nstop Gk.ib G2.cb Gk.j_k);
  }
}.

(* here RO is from SplitRO2 *)
local lemma Gkt_ROt &m :
  Pr[Game(Gkt(OAEUt, OBEUt), A).main() @ &m :
     G.bad /\ nstop Gk.ia G2.ca Gk.i_k /\ nstop Gk.ib G2.cb Gk.j_k] =
  Pr[MainDT(DA(OBEUt, A), FROEUt.RO).distinguish() @ &m : res].
proof.
byequiv => //; proc; inline *; wp.
call (: ={m}(OAEUt, FROEUt.RO) /\
        ={OBEUt.m, G2.ca, G2.cb, G.bad} /\ ={cddh, i_k, j_k, k}(Gk, Gk));
  1..5: (by proc; inline *; sim).
by auto.
qed.

local lemma ROt_RO_DOMt &m :
  Pr[MainDT(DA(OBEUt, A), FROEUt.RO).distinguish() @ &m : res] =
  Pr[MainDT(DA(OBEUt, A), RO_DOMt(ROT.RO, ROF.RO)).distinguish() @ &m : res].
proof. by byequiv (RO_split (DA(OBEUt, A))). qed.

local module Gk2A (OA0 : FROEU.RO, OA1 : FROEU.RO, OB : FROEUt.ROt) : CDH_RSR_Oracles_i = {
  import var G2 G Gk

  proc init () = {
    ca    <- [];
    cb    <- [];
    bad   <- false;
    k     <$ [1..q_ddh];
    i_k   <- -1;
    j_k   <- -1;
    cddh  <- 0;
    ia    <$ dlist (dbiased pa) na;
    ib    <$ dlist (dbiased pb) nb;
    OA0.init();
    OA1.init();
    OB.init(nth false ib);
  }

  proc oa (i : int) = {
    var a;

    if (cddh < k) ca <- i :: ca;
    a <@ OA0.get(i);
    return a;
  }

  proc ob (j : int) = {
    var b;

    if (cddh < k) cb <- j :: cb;
    b <@ OB.get(j);
    return b;
  }

  proc oA (i : int) = {
    var a;

    if (nth false ia i) a <@ OA1.get(i);
    else                a <@ OA0.get(i);
    return exp g a;
  }

  proc oB (j : int) = {
    var b;

    b <@ OB.get(j);
    return exp g b;
  }

  proc ddh (m, i, j) = {
    var a, b, r, t;

    a <- e;
    b <- e;
    r <- false;
    t <- false;
    cddh <- cddh + 1;
    if (0 <= i < na /\ 0 <= j < nb) {
      if (nth false ia i) a <@ OA1.get(i);
      else                a <@ OA0.get(i);
      b <@ OB.get(j);
      t <- m = exp g (a * b);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ cddh = k /\ ! bad) {
            bad <- true;
            i_k <- i;
            j_k <- j;
        }
      }
    }
    return r;
  }
}.

local lemma RO_DOMt_Gk2A &m :
  Pr[MainDT(DA(OBEUt, A), RO_DOMt(ROT.RO, ROF.RO)).distinguish() @ &m : res] <=
  Pr[Game(Gk2A(OA0EU, OA1EU, OBEUt), A).main() @ &m :
     G.bad /\ nstop Gk.ia G2.ca Gk.i_k /\ nstop Gk.ib G2.cb Gk.j_k].
proof.
byequiv => //; proc; inline *; wp; symmetry.
call (: ! (nstop Gk.ia G2.ca Gk.i_k \/ nstop Gk.ib G2.cb Gk.j_k),

        ={m}(OA1EU, ROT.RO) /\ ={m}(OA0EU, ROF.RO) /\
        ={OBEUt.m, G2.ca, G2.cb, G.bad} /\
        ={cddh, i_k, j_k, k, ia, ib}(Gk, Gk) /\
        nth false Gk.ia{1} = RO_DOMt.test{2} /\
        (G.bad <=> Gk.k <= Gk.cddh){1},

        ! (nstop Gk.ia G2.ca Gk.i_k /\ nstop Gk.ib G2.cb Gk.j_k){1}).
- by exact A_ll.
- proc; inline RO_DOMt(ROT.RO, ROF.RO).get; sp.
  by (if; 1: smt()); inline *; auto.
- by move => *; proc; inline *; sp; if; auto; smt(dEU_ll).
- by move => *; proc; inline *; sp; if; auto; smt(dEU_ll).
- by proc; inline *; auto; smt().
- by move => *; proc; inline *; auto; smt(dEU_ll).
- by move => *; proc; inline *; auto; smt(dEU_ll).
- proc; inline Gkt(RO_DOMt(ROT.RO, ROF.RO), RBEUt.RO).oa.
  inline Gk2A(RA0EU.RO, RA1EU.RO, RBEUt.RO).oa; wp.
  inline RO_DOMt(ROT.RO, ROF.RO).get; sp 2 2.
  if; 1: smt().
(*
  + sp 1 2; if{2}; 2: by inline *; auto.
    conseq (: _ ==> ! (nstop Gk.ia G2.ca Gk.i_k /\
                       nstop Gk.ib G2.cb Gk.j_k){2}); 1: smt().
    by inline *; auto => />; smt().
  + sp 0 1; if{2}; 2: by inline *; auto.
    conseq (: _ ==> G.bad{2}); 1: smt().
    by inline *; auto => />.
*) admit.
(*
- by move => *; proc; inline *; auto; smt(dEU_ll).
*) admit.
(*
- by move => *; proc; inline *; sp; if; auto; smt(dEU_ll).
*) admit.
(*
- by proc; inline *; auto => /> *.
*)
admit.
(*
- by move => *; proc; inline *; sp 2; if; auto; smt(dEU_ll).
*) admit.
- by move => *; proc; inline *; auto; smt(dEU_ll).
(*
- proc; inline Gkt(RO_DOMt(ROT.RO, ROF.RO), RBEUt.RO).ddh.
  inline Gk2A(RA0EU.RO, RA1EU.RO, RBEUt.RO).ddh; sp.
  if; [smt() | inline RO_DOMt(ROT.RO, ROF.RO).get; sp 1 0 | by auto; smt()].
*)
(*
  seq 3 4 : (={m}(OA1EU, ROT.RO) /\ ={m}(OA0EU, ROF.RO) /\
                ={OBEUt.m, G2.ca, G2.cb, G.bad, i0, j0, r0, t} /\
                ={cddh, i_k, j_k, k, ia, ib}(Gk, Gk) /\
                nth false Gk.ia{1} = RO_DOMt.test{2} /\
                (G.bad <=> Gk.k <= Gk.cddh){2}).
*) admit.
(*
- move => *; proc; inline *; sp; if; 2: by auto.
  by sp; if; auto; smt(dEU_ll).
*) admit.
(*
- move => *; proc; inline Gkt(RO_DOMt(ROT.RO, ROF.RO), RBEUt.RO).ddh.
  by sp; if; [inline *; sp; if; auto; smt(dEU_ll) | auto; smt()].
*) admit.
- auto => /> *.
admit.
admit.
qed.

local module GkX2A (OA0 : FROEU.RO, OA1 : FROG.RO, OB : FROEUt.ROt) : CDH_RSR_Oracles_i = {
  import var G2 G Gk

  proc init () = {
    ca    <- [];
    cb    <- [];
    bad   <- false;
    k     <$ [1..q_ddh];
    i_k   <- -1;
    j_k   <- -1;
    cddh  <- 0;
    ia    <$ dlist (dbiased pa) na;
    ib    <$ dlist (dbiased pb) nb;
    OA0.init();
    OA1.init();
    OB.init(nth false ib);
  }

  proc oa (i : int) = {
    var a;

    if (! bad) ca <- i :: ca;
    a <@ OA0.get(i);
    return a;
  }

  proc ob (j : int) = {
    var b;

    if (! bad) cb <- j :: cb;
    b <@ OB.get(j);
    return b;
  }

  proc oA (i : int) = {
    var a, ga;

    if (nth false ia i) { ga <@ OA1.get(i); }
    else                { a  <@ OA0.get(i); ga <- exp g a; }
    return ga;
  }

  proc oB (j : int) = {
    var b;

    b <@ OB.get(j);
    return exp g b;
  }

  proc ddh (m, i, j) = {
    var a, ga, b, r, t;

    a <- e;
    b <- e;
    ga <- g;
    r <- false;
    t <- false;
    cddh <- cddh + 1;
    if (0 <= i < na /\ 0 <= j < nb) {
      if (nth false ia i) { ga <@ OA1.get(i); }
      else                { a  <@ OA0.get(i); ga <- exp g a; }
      b <@ OB.get(j);
      t <- m = ga ^ b;
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ cddh = k /\ ! bad) {
            bad <- true;
            i_k <- i;
            j_k <- j;
        }
      }
    }
    return r;
  }
}.

lemma mu1_dmap_exp (a : G) :
  a \in dmap (duniform (elems EU)) (exp g) =>
  mu1 (dmap (duniform (elems EU)) (exp g)) a = mu1 (duniform (elems EU)) (elog a).
proof.
move => /supp_dmap [x [/supp_duniform x_EU ->]].
rewrite dmap1E /(\o) /= expK ?memE // (mu_eq_support _ _ (pred1 x)) //.
by rewrite /pred1 => y /supp_duniform y_EU /=; smt(exp_inj).
qed.

local lemma Gk2A_GkX2A &m :
  Pr[Game(Gk2A(OA0EU, OA1EU, OBEUt), A).main() @ &m :
     G.bad /\ nstop Gk.ia G2.ca Gk.i_k /\ nstop Gk.ib G2.cb Gk.j_k] =
  Pr[Game(GkX2A(OA0EU, OAG, OBEUt), A).main() @ &m :
     G.bad /\ nstop Gk.ia G2.ca Gk.i_k /\ nstop Gk.ib G2.cb Gk.j_k].
proof.
(*
byequiv => //; proc; inline *.
call (: ={G2.ca, G2.cb , G.bad, OBEUt.m, OA0EU.m} /\
        map (fun _ => exp g) OA1EU.m{1} = OAG.m{2} /\
        ={cddh, i_k, j_k, k,ia,ib}(Gk, Gk) /\
        (forall r, r \in OA1EU.m => oget (OA1EU.m.[r]) \in EU){1}).
- proc. if; 1:smt(); 2: by inline*; auto.
  inline *. sp.
  seq 1 1 : (={x} /\ exp g r{1} = r{2} /\ r{1} \in EU /\
            ={G2.ca, G2.cb , G.bad, OBEUt.m, OA0EU.m} /\
            map (fun _ => exp g) OA1EU.m{1} = OAG.m{2} /\
            ={cddh, i_k, j_k, k,ia,ib}(Gk, Gk) /\
            (forall r, r \in OA1EU.m => oget (OA1EU.m.[r]) \in EU){1});
    2: by if; auto => />; smt(get_setE get_set_sameE mapE map_set).
  rnd (exp g) elog; auto => /> *.
  split => [|_]; 1: smt(expK supp_dmap supp_duniform).
  split => [|_]; 1: exact mu1_dmap_exp.
  smt(expK supp_dmap supp_duniform).
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- proc. inline Gk2A(RA0EU.RO, RA1EU.RO, RBEUt.RO).ddh GkX2A(RA0EU.RO, RAG.RO, RBEUt.RO).ddh.
  sp 9 10; if; 1: smt(); 2: by auto.
  if; 1: smt().
  + inline RA1EU.RO.get RAG.RO.get ; sp.
    seq 1 1 : (={x} /\ exp g r1{1} = r1{2} /\ r1{1} \in EU /\
            ={G2.ca, G2.cb , G.bad, OBEUt.m, OA0EU.m} /\
            map (fun _ => exp g) OA1EU.m{1} = OAG.m{2} /\
            ={cddh, i_k, j_k, k,ia,ib}(Gk, Gk) /\
            (forall r, r \in OA1EU.m => oget (OA1EU.m.[r]) \in EU){1}).
    rnd (exp g) elog; auto => /> *.
    split => [|_]; 1: smt(expK supp_dmap supp_duniform).
    split => [|_]; 1: exact mu1_dmap_exp.
    smt(expK supp_dmap supp_duniform).
    if; 1: smt(mem_map).
    admit.
*)
admitted.

local module Gkxy (OA : FROEU.RO, OB : FROEU.RO) = {
  import var G2 G Gk
  var x, y : Z

  proc init (x' : Z, y' : Z) = {
    ca    <- [];
    cb    <- [];
    bad   <- false;
    k     <$ [1..q_ddh];
    i_k   <- -1;
    j_k   <- -1;
    cddh  <- 0;
    ia    <$ dlist (dbiased pa) na;
    ib    <$ dlist (dbiased pb) nb;
    x     <- x';
    y     <- y';
    OA.init();
    OB.init();
  }

  proc oa (i : int) = {
    var a;

    a <- e;
    if (0 <= i < na) {
      if (!nth false ia i) {
        ca <- i :: ca;
        a <@ OA.get(i);
      }
    }
    return a;
  }

  proc ob (j : int) = {
    var b;

    b <- e;
    if (0 <= j < nb) {
      if (!nth false ib j) {
        cb <- j :: cb;
        b <@ OB.get(j);
      }
    }
    return b;
  }

  proc oA (i : int) = {
    var a;

    a <- e;
    if (0 <= i < na) a <@ OA.get(i);
    return (exp g (if (nth false ia i) then x * a else a));
  }

  proc oB (j : int) = {
    var b;

    b <- e;
    if (0 <= j < nb) b <@ OB.get(j);
    return (exp g (if (nth false ib j) then y * b else b));
  }

  proc ddh (m, i, j) = {
    var a, b, r, t;

    a <- e;
    b <- e;
    r <- false;
    t <- false;
    cddh <- cddh + 1;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OA.get(i);
      b <@ OB.get(j);
      t <- m = exp g ((if (nth false ia i) then x * a else a) *
                      (if (nth false ib j) then y * b else b));
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ cddh = k /\ ! bad) {
            bad <- true;
            i_k <- i;
            j_k <- j;
        }
      }
    }
    return r;
  }
}.

local module GameGkxy (A : Adversary) = {
  module O' = Count(Gkxy(OAEU, OBEU))

  proc main(x : Z, y : Z) = {
    var r;

    Gkxy(OAEU, OBEU).init(x, y);
    O'.init();
    r <@ A(O').guess();
    return r;
  }
}.

local lemma GkX2A_Gkxy &m x y :
  x \in EU =>
  y \in EU =>
  Pr[Game(GkX2A(OA0EU, OAG, OBEUt), A).main() @ &m :
     G.bad /\ nstop Gk.ia G2.ca Gk.i_k /\ nstop Gk.ib G2.cb Gk.j_k] =
  Pr[GameGkxy(A).main(x, y) @ &m :
     G.bad /\ nstop Gk.ia G2.ca Gk.i_k /\ nstop Gk.ib G2.cb Gk.j_k].
proof.
admitted.

local lemma Gk'_Gkxy &m x y :
  x \in EU =>
  y \in EU =>
  Pr[Game(Gk(OAEU, OBEU), A).main() @ &m :
     G.bad /\ nstop Gk.ia G2.ca Gk.i_k /\ nstop Gk.ib G2.cb Gk.j_k] <=
  Pr[GameGkxy(A).main(x, y) @ &m :
     G.bad /\ nstop Gk.ia G2.ca Gk.i_k /\ nstop Gk.ib G2.cb Gk.j_k].
admitted.

local lemma Gkxy_S &m x y :
  x \in EU =>
  y \in EU =>
  Pr[GameGkxy(A).main(x, y) @ &m :
     G.bad /\ nstop Gk.ia G2.ca Gk.i_k /\ nstop Gk.ib G2.cb Gk.j_k] <=
  Pr[GameS(A).main(exp g x, exp g y) @ &m : S.m_crit = exp g (x * y)].
proof.
move => x_EU y_EU; byequiv => //; proc; inline *; symmetry.
call (: ! (nstop Gk.ia G2.ca Gk.i_k /\ nstop Gk.ib G2.cb Gk.j_k) \/
        ! (G.bad => nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k) \/
        Gk.k <= Gk.cddh,

        ={OAEU.m, OBEU.m, G2.ca, G2.cb} /\ ={cddh, k, ia, ib}(S, Gk) /\
        (S.gx = exp g x /\ S.gy = exp g y){1} /\
        (Gkxy.x = x /\ Gkxy.y = y){2} /\
        (G.bad{2} => S.m_crit{1} = exp g (x * y)) /\
        (G.bad <=> Gk.k <= Gk.cddh){2} /\
        (forall i, i \in OAEU.m => oget (OAEU.m.[i]) \in EU){2} /\
        (forall j, j \in OBEU.m => oget (OBEU.m.[j]) \in EU){2},

        ! (nstop Gk.ia G2.ca Gk.i_k /\ nstop Gk.ib G2.cb Gk.j_k){2} \/
        ! (G.bad => nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k){2} \/
        (S.k <= S.cddh /\ S.m_crit = exp g (x * y)){1} \/
        (Gk.k <= Gk.cddh /\ ! G.bad){2}); 
  
  2, 5 : by proc; inline *; sp; if; auto; smt(expM get_setE get_set_sameE supp_duniform memE).


     
(* (by proc; inline *; auto; *)
(*                    smt(expM get_setE get_set_sameE supp_duniform memE)). *)
  (* 2..9:  by move => *; proc; inline *; auto => />; smt(dEU_ll). *)
- by exact A_ll.
- by move => *; proc; inline *; sp; if; auto => />; smt(dEU_ll). 
- by move => *; proc; inline *; sp; if; auto => />; smt(dEU_ll). 
- by move => *; proc; inline *; sp; if; auto => />; smt(dEU_ll). 
- by move => *; proc; inline *; sp; if; auto => />; smt(dEU_ll). 
- by  proc; inline *; sp; if; [|if; auto|]; auto; smt(expM get_setE get_set_sameE supp_duniform memE).
- by move => *; proc; inline *; sp; if; auto; if; auto => />; smt(dEU_ll). 
- by move => *; proc; inline *; sp; if; auto; if; auto => />; smt(dEU_ll). 
- by  proc; inline *; sp; if; [|if; auto|]; auto; smt(expM get_setE get_set_sameE supp_duniform memE).
- by move => *; proc; inline *; sp; if; auto; if; auto => />; smt(dEU_ll). 
- by move => *; proc; inline *; sp; if; auto; if; auto => />; smt(dEU_ll). 
- proc; inline S.ddh Gkxy(RAEU.RO, RBEU.RO).ddh.
  sp 8 9; if; [smt() | | auto; smt()].
  seq 2 2 : (={m0, i0, j0, a, b, r0} /\ a{2} \in EU /\ b{2} \in EU /\
             (nstop Gk.ia G2.ca Gk.i_k /\ nstop Gk.ib G2.cb Gk.j_k){2} /\
             ={OAEU.m, OBEU.m, G2.ca, G2.cb} /\ ={cddh, k, ia, ib}(S, Gk) /\
             (S.gx = exp g x /\ S.gy = exp g y){1} /\
             (Gkxy.x = x /\ Gkxy.y = y){2} /\
             (! G.bad /\ Gk.cddh <= Gk.k){2} /\
             (forall i, i \in OAEU.m => oget (OAEU.m.[i]) \in EU){2} /\
             (forall j, j \in OBEU.m => oget (OBEU.m.[j]) \in EU){2});
    1: by inline *; auto; smt(get_setE get_set_sameE memE supp_duniform).
  auto => /> &2; move: (i0{2}) (j0{2}) (G2.ca{2}) (G2.cb{2}) => i j ca cb *.
  (case: (i \in ca) => [i_ca | iNca]); (case: (j \in cb) => [j_cb | jNcb] /=);
    1..3: smt(expM mulA mulC).
  rewrite -implybE -!expM /nstop => [cddh_k [[_ ->] [_ ->]] /=].
  have -> : x * a{2} * (y * b{2}) * (inv a{2} * inv b{2}) =
            (a{2} * inv a{2}) * (b{2} * inv b{2} * (x * y)) by smt(mulA mulC).
  by rewrite !exp_inv.
- move => &2 *.
  conseq (: _ ==> true) (: _ ==> _) => //; 2: by islossless.
  proc; inline S.ddh; sp; elim * => cddh Ccddh.
  if; 2: by auto; smt().
  by inline *; auto; smt(get_setE get_set_sameE memE supp_duniform).
- move => &1.
  conseq (: _ ==> true) (: _ ==> _) => //; 2: by islossless.
  proc; inline Gkxy(RAEU.RO, RBEU.RO).ddh; sp; elim * => cddh Ccddh.
  if; 2: by auto; smt().
(*
  by inline *; auto; smt(get_setE get_set_sameE memE supp_duniform).
*) admit.
- auto => />; smt(mem_empty supp_dinter).
qed.

local lemma A_B &m :
  Pr[Game(Gk(OAEU, OBEU), A).main() @ &m :
     G.bad /\ nstop Gk.ia G2.ca Gk.i_k /\ nstop Gk.ib G2.cb Gk.j_k] <=
  Pr[NCDH.Game(B(A)).main() @ &m : res].
proof.
pose p := Pr[Game(Gk(OAEU,OBEU), A).main() @ &m :
             G.bad /\ nstop Gk.ia G2.ca Gk.i_k /\ nstop Gk.ib G2.cb Gk.j_k].
byphoare (: (glob A, Gk.i_k, Gk.j_k) = (glob A, Gk.i_k, Gk.j_k){m} ==> _) => //.
proc; inline B(A).solve; wp.
seq 4 : true 1%r p 0%r _
        (x \in EU /\ y \in EU /\ gx = exp g x /\ gy = exp g y /\
        (glob A, Gk.i_k, Gk.j_k) = (glob A, Gk.i_k, Gk.j_k){m}) => //.
- by auto => />; smt(memE supp_duniform).
- by islossless; apply duniform_ll; smt(e_EU).
exlim x, y => x' y'.
call (: (x' \in EU) /\ (y' \in EU) /\ gx = exp g x' /\ gy = exp g y' /\
        (glob A, Gk.i_k, Gk.j_k) = (glob A, Gk.i_k, Gk.j_k){m} ==>
        S.m_crit = exp g (x' * y')); 2: by auto.
bypr => &m' /> 2? -> -> *.
have -> : p = Pr[Game(Gk(OAEU,OBEU), A).main() @ &m' :
                 G.bad /\ nstop Gk.ia G2.ca Gk.i_k /\ nstop Gk.ib G2.cb Gk.j_k].
  by rewrite /p; byequiv => //; sim => /> /#.
by apply (ler_trans _ _ _ _ (Gkxy_S &m' x' y' _ _)) => //; exact Gk'_Gkxy.
qed.

lemma G1G2_NCDH &m :
  `| Pr[ Game(G1, A).main() @ &m : res ] - Pr[ Game(G2, A).main() @ &m : res] | <=
  q_ddh%r / ((1%r - pa) ^ q_oa * (1%r - pb) ^ q_ob * pa * pb) *
  Pr[NCDH.Game(B(A)).main() @ &m : res] + DELTA.
proof.
apply (ler_trans _ _ _ (G1G2_Gbad &m) _).
suff: Pr[Game(G', A).main() @ &m : G.bad] <=
      q_ddh%r / ((1%r - pa) ^ q_oa * (1%r - pb) ^ q_ob * pa * pb) *
      Pr[NCDH.Game(B(A)).main() @ &m : res] by smt(G_G').
have H1 := guess_bound &m; have H2 := A_B &m.
have {H1 H2} H := ler_trans _ _ _ H1 H2.
rewrite -ler_pdivr_mull; 2: by rewrite invf_div; smt().
by smt(divr_gt0 expr0 expr_gt0 mulr_gt0 pa_bound pb_bound q_ddh_ge1).
qed.

(* FIXME ======


local module Gkx : CDH_RSR_Oracles_i = {
  import var G2 G Gk

  proc init () = {
    OAG.init();
    OBG.init();
    ca  <- [];
    cb  <- [];
    bad <- false;
    k     <$ [1..q_ddh];
    i_k   <- -1;
    j_k   <- -1;
    cddh  <- 0;
    ia    <$ dlist (dbiased pa) na;
    ib    <$ dlist (dbiased pb) nb;
  }

  proc oa (i : int) = {
    var a;

    if (!bad) ca <- i :: ca;
    a <@ OAG.get(i);
    return (elog a);
  }

  proc ob (j : int) = {
    var b;

    if (!bad) cb <- j :: cb;
    b <@ OBG.get(j);
    return (elog b);
  }

  proc oA (i : int) = {
    var a;

    a <@ OAG.get(i);
    return a;
  }

  proc oB (j : int) = {
    var b;

    b <@ OBG.get(j);
    return b;
  }

  proc ddh (m, i, j) = {
    var a, b, r, t;

    a <- g;
    b <- g;
    r <- false;
    t <- false;
    cddh <- cddh + 1;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ OAG.get(i);
      b <@ OBG.get(j);
      t <- m = a ^ (elog b);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ cddh = k /\ ! bad) {
            bad <- true;
            i_k <- i;
            j_k <- j;
        }
      }
    }
    return r;
  }
}.

local lemma Gk'_Gkx &m :
  Pr[Game(Gk', A).main() @ &m :
     G.bad /\ nstop Gk.ia Gk.ib G2.ca G2.cb /\
     nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k] <=
  Pr[Game(Gkx, A).main() @ &m :
     G.bad /\ nstop Gk.ia Gk.ib G2.ca G2.cb /\
     nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k].
proof.
byequiv => //; proc; inline *.
call (: map (fun _ => exp g) OAEU.m{1} = OAG.m{2} /\
        map (fun _ => exp g) OBEU.m{1} = OBG.m{2} /\
        (forall r, r \in OAEU.m => oget (OAEU.m.[r]) \in EU){1} /\
        (forall r, r \in OBEU.m => oget (OBEU.m.[r]) \in EU){1} /\
        ={G2.ca, G2.cb, G.bad} /\ ={cddh, i_k, j_k, k}(Gk, Gk)).
- proc; inline *; sp.
  seq 1 1 : (={x} /\ exp g r{1} = r{2} /\ r{1} \in EU /\
             map (fun _ => exp g) OAEU.m{1} = OAG.m{2} /\
             map (fun _ => exp g) OBEU.m{1} = OBG.m{2} /\
             (forall r, r \in OAEU.m => oget (OAEU.m.[r]) \in EU){1} /\
             (forall r, r \in OBEU.m => oget (OBEU.m.[r]) \in EU){1} /\
             ={G2.ca, G2.cb, G.bad} /\ ={cddh, i_k, j_k, k}(Gk, Gk));
    2: by if; auto => />; smt(get_setE get_set_sameE mapE map_set).
  rnd (exp g) (elog); auto => /> *.
  split => [|_]; 1: smt(expK supp_dmap supp_duniform).
  split => [|_]; 1: exact mu1_dmap_exp.
  smt(expK supp_dmap supp_duniform).
- proc; inline *; sp.
  seq 1 1 : (={x} /\ exp g r{1} = r{2} /\ r{1} \in EU /\
             map (fun _ => exp g) OAEU.m{1} = OAG.m{2} /\
             map (fun _ => exp g) OBEU.m{1} = OBG.m{2} /\
             (forall r, r \in OAEU.m => oget (OAEU.m.[r]) \in EU){1} /\
             (forall r, r \in OBEU.m => oget (OBEU.m.[r]) \in EU){1} /\
             ={G2.ca, G2.cb, G.bad} /\ ={cddh, i_k, j_k, k}(Gk, Gk));
    2: by if; auto => />; smt(get_setE get_set_sameE mapE map_set).
  rnd (exp g) (elog); auto => /> *.
  split => [|_]; 1: smt(expK supp_dmap supp_duniform).
  split => [|_]; 1: exact mu1_dmap_exp.
  smt(expK supp_dmap supp_duniform).
- proc; inline *; sp 3 3.
  seq 2 2 : (={x} /\ exp g r0{1} = r0{2} /\ r0{1} \in EU /\
             map (fun _ => exp g) OAEU.m{1} = OAG.m{2} /\
             map (fun _ => exp g) OBEU.m{1} = OBG.m{2} /\
             (forall r, r \in OAEU.m => oget (OAEU.m.[r]) \in EU){1} /\
             (forall r, r \in OBEU.m => oget (OBEU.m.[r]) \in EU){1} /\
             ={G2.ca, G2.cb, G.bad} /\ ={cddh, i_k, j_k, k}(Gk, Gk));
      2: by if; auto => />; smt(expK get_setE get_set_sameE mapE map_set).
  rnd (exp g) (elog); auto => /> *.
  split => [|_]; 1: smt(expK supp_dmap supp_duniform).
  split => [|_]; 1: exact mu1_dmap_exp.
  smt(expK supp_dmap supp_duniform).
- proc; inline *; sp 3 3.
  seq 2 2 : (={x} /\ exp g r0{1} = r0{2} /\ r0{1} \in EU /\
             map (fun _ => exp g) OAEU.m{1} = OAG.m{2} /\
             map (fun _ => exp g) OBEU.m{1} = OBG.m{2} /\
             (forall r, r \in OAEU.m => oget (OAEU.m.[r]) \in EU){1} /\
             (forall r, r \in OBEU.m => oget (OBEU.m.[r]) \in EU){1} /\
             ={G2.ca, G2.cb, G.bad} /\ ={cddh, i_k, j_k, k}(Gk, Gk));
    2: by if; auto => />; smt(expK get_setE get_set_sameE mapE map_set).
  rnd (exp g) (elog); auto => /> *.
  split => [|_]; 1: smt(expK supp_dmap supp_duniform).
  split => [|_]; 1: exact mu1_dmap_exp.
  smt(expK supp_dmap supp_duniform).
- proc; inline *; sp; if; 1,3: by auto.
  seq 8 8 : (exp g a{1} = a{2} /\ a{1} \in EU /\
             exp g b{1} = b{2} /\ b{1} \in EU /\
             map (fun _ => exp g) OAEU.m{1} = OAG.m{2} /\
             map (fun _ => exp g) OBEU.m{1} = OBG.m{2} /\
             (forall r, r \in OAEU.m => oget (OAEU.m.[r]) \in EU){1} /\
             (forall r, r \in OBEU.m => oget (OBEU.m.[r]) \in EU){1} /\
             ={G2.ca, G2.cb, G.bad, i0, j0, m0, r0} /\
             ={cddh, i_k, j_k, k}(Gk, Gk));
    2: by sp 1 1; if; auto; smt(expK expM).
  seq 4 4 : (exp g a{1} = a{2} /\ a{1} \in EU /\
             map (fun _ => exp g) OAEU.m{1} = OAG.m{2} /\
             map (fun _ => exp g) OBEU.m{1} = OBG.m{2} /\
             (forall r, r \in OAEU.m => oget (OAEU.m.[r]) \in EU){1} /\
             (forall r, r \in OBEU.m => oget (OBEU.m.[r]) \in EU){1} /\
             ={G2.ca, G2.cb, G.bad, i0, j0, m0, r0} /\
             ={cddh, i_k, j_k, k}(Gk, Gk)).
  + seq 2 2 : (={x} /\ exp g r1{1} = r1{2} /\ r1{1} \in EU /\
               map (fun _ => exp g) OAEU.m{1} = OAG.m{2} /\
               map (fun _ => exp g) OBEU.m{1} = OBG.m{2} /\
               (forall r, r \in OAEU.m => oget (OAEU.m.[r]) \in EU){1} /\
               (forall r, r \in OBEU.m => oget (OBEU.m.[r]) \in EU){1} /\
               ={G2.ca, G2.cb, G.bad, i0, j0, m0, r0} /\
               ={cddh, i_k, j_k, k}(Gk, Gk));
      2: by if; auto => />; smt(get_setE get_set_sameE mapE map_set).
    rnd (exp g) (elog); auto => /> *.
    split => [|_]; 1: smt(expK supp_dmap supp_duniform).
    split => [|_]; 1: exact mu1_dmap_exp.
    smt(expK supp_dmap supp_duniform).
  + seq 2 2 : (={x0} /\ exp g r2{1} = r2{2} /\ r2{1} \in EU /\
               exp g a{1} = a{2} /\ a{1} \in EU /\
               map (fun _ => exp g) OAEU.m{1} = OAG.m{2} /\
               map (fun _ => exp g) OBEU.m{1} = OBG.m{2} /\
               (forall r, r \in OAEU.m => oget (OAEU.m.[r]) \in EU){1} /\
               (forall r, r \in OBEU.m => oget (OBEU.m.[r]) \in EU){1} /\
               ={G2.ca, G2.cb, G.bad, i0, j0, m0, r0} /\
               ={cddh, i_k, j_k, k}(Gk, Gk));
      2: by if; auto => />; smt(get_setE get_set_sameE mapE map_set).
    rnd (exp g) (elog); auto => /> *.
    split => [|_]; 1: smt(expK supp_dmap supp_duniform).
    split => [|_]; 1: exact mu1_dmap_exp.
    smt(expK supp_dmap supp_duniform).
- by auto => />; smt(map_empty mem_empty).
qed.


local module Gkx1 : CDH_RSR_Oracles_i = {
  import var G2 G Gk
  include var Gkx [ob,oB]

  proc init () = {
    OAG1.init();
    OAG2.init();
    OBG.init();
    ca  <- [];
    cb  <- [];
    bad <- false;
    k     <$ [1..q_ddh];
    i_k   <- -1;
    j_k   <- -1;
    cddh  <- 0;
    ia    <$ dlist (dbiased pa) na;
    ib    <$ dlist (dbiased pb) nb;
  }

  proc oag_get(i) = {
    var a;

    if (nth false ia i) { a <@ OAG1.get(i); }
    else { a <@ OAG2.get(i); }
    return a;
  }

  proc oa (i : int) = {
    var a;

    if (!bad) ca <- i :: ca;
    a <@ oag_get(i);
    return (elog a);
  }

  proc oA (i : int) = {
    var a;

    a <@ oag_get(i);
    return a;
  }

  proc ddh (m, i, j) = {
    var a, b, r, t;

    a <- g;
    b <- g;
    r <- false;
    t <- false;
    cddh <- cddh + 1;
    if (0 <= i < na /\ 0 <= j < nb) {
      a <@ oag_get(i);
      b <@ OBG.get(j);
      t <- m = a ^ (elog b);
      if (i \in ca \/ j \in cb) {
        r <- t;
      } else {
          if (t /\ cddh = k /\ ! bad) {
            bad <- true;
            i_k <- i;
            j_k <- j;
        }
      }
    }
    return r;
  }
}.

local lemma Gkx_Gkx1 &m :
    Pr[Game(Gkx,A).main() @ &m :
       G.bad /\ nstop Gk.ia Gk.ib G2.ca G2.cb /\
       nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k] <=
    Pr[Game(Gkx1,A).main() @ &m :
       G.bad /\ nstop Gk.ia Gk.ib G2.ca G2.cb /\
       nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k].
proof.
byequiv => //; proc; inline *.
call (: (OAG.m{1} = OAG1.m{2} + OAG2.m{2}) /\
        (forall i, ! (i \in OAG1.m /\ i \in OAG2.m)){2} /\
        (forall i, nth false Gk.ia{1} i => (i \in OAG.m{1} <=> i \in OAG1.m{2})) /\
        (* (forall r, r \in OAEU.m => oget (OAEU.m.[r]) \in EU){1} /\ *)
        (* (forall r, r \in OBEU.m => oget (OBEU.m.[r]) \in EU){1} /\ *)
        ={G2.ca, G2.cb, G.bad, OBG.m} /\ ={cddh, i_k, j_k, k}(Gk, Gk)).
- proc. inline Gkx1.oag_get. sp. if{2}; auto.
  + inline*. auto => />
  exlim i{1}, i0{2} => i1 i2.
  call(: (OAG.m{1} = OAG1.m{2} + OAG2.m{2}) /\
        (forall i, ! (i \in OAG1.m /\ i \in OAG2.m)){2} /\
        (forall i, nth false Gk.ia{1} i => (i \in OAG.m{1} <=> i \in OAG1.m{2})) /\
        nth false Gk.ia{1} i2 /\ i1 = i2).
  auto. smt.



local lemma Gkx_Sx &m x' y' : x' \in EU => y' \in EU =>
  Pr[Game(Gkx,A).main() @ &m :
     G.bad /\ nstop Gk.ia Gk.ib G2.ca G2.cb /\
     nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k] <=
  Pr[GameSx(A).main(x', y') @ &m : Sx.m_crit = exp g (x' * y')].
proof.
move => x_EU y_EU; byequiv => //; proc; inline *; symmetry.
have mu : forall (rR : G) b x,
            x \in EU =>
            rR \in dmap (duniform (elems EU)) (exp g) =>
            mu1 (dmap (duniform (elems EU)) (exp g)) rR =
            mu1 (dmap (duniform (elems EU)) (exp g))
                (if b then rR ^ inv (elog (exp g x)) else rR).
  move=> ? [|] //= z z_EU; rewrite expK // => /supp_dmap [a [Ha ->]].
  rewrite dmap_duniform; 1: smt(memE exp_inj).
  apply duniform_uni; rewrite supp_duniform.
  - apply/mapP; exists a. smt(supp_duniform).
  rewrite -expM.
  have S : exp g a ^ inv z \in image (fun i => exp g (z * i)) EU.


have inmap : forall (rL : G) b x,
               x \in EU =>
               rL \in dmap (duniform (elems EU)) (exp g) =>
               (if b then rL ^ elog (exp g x) else rL) \in
                dmap (duniform (elems EU)) (exp g).
- move => 4? /supp_dmap [z [/supp_duniform z_EU ->]].
  suff : dmap (duniform (elems EU)) (exp g) =
         dmap (duniform (elems EU)) (fun x => exp g (z * x))
    by smt(expK expM supp_dmap supp_duniform).
  rewrite ?dmap_duniform; 1,2: smt(exp_inj exp_inj').
  apply eq_duniformP => e.
  by split; move => ?; suff : e \in image (exp g) EU; smt(imageP img_exp mapP).
call (: ! nstop Gk.ia Gk.ib G2.ca G2.cb \/
        ! (G.bad => nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k) \/
        Gk.k <= Gk.cddh,

        ={G2.ca, G2.cb} /\ ={cddh, k, ia, ib}(Sx, Gk) /\
        (Sx.gx = exp g x' /\ Sx.gy = exp g y'){1} /\
        (map (fun i a => if nth false Sx.ia i then a ^ (elog Sx.gx)
                         else a) OAG.m){1} = OAG.m{2} /\
        (map (fun j b => if nth false Sx.ib j then b ^ (elog Sx.gy)
                         else b) OBG.m){1} = OBG.m{2} /\
        (G.bad{2} => Sx.m_crit{1} = exp g (x' * y')) /\
        (G.bad <=> Gk.k <= Gk.cddh){2},

        ! (nstop Gk.ia Gk.ib G2.ca G2.cb){2} \/
        ! (G.bad => nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k){2} \/
        (Sx.k <= Sx.cddh /\ Sx.m_crit = exp g (x' * y')){1} \/
        (Gk.k <= Gk.cddh /\ ! G.bad){2}).
- by exact A_ll.
- proc; inline *; wp.
  rnd (fun r => if nth false Sx.ia i then r ^ (elog Sx.gx) else r){1}
      (fun r => if nth false Sx.ia i then r ^ (inv (elog Sx.gx)) else r){1}.
  auto => /> &m1 &m2 *.
  split; 1: smt(expK mulC powM pow_inv supp_dmap supp_duniform).
  move => *; split; 1: by move => ?; apply mu.
  move => _ 2?; split; 1: by apply inmap.
  move => *; split; 2: smt(get_setE get_set_sameE mapE map_set).
  by smt(expK mulC powM pow_inv supp_dmap supp_duniform).
- by move => *; proc; call (: true); auto; smt(dG_ll).
- by move => *; proc; call (: true); auto; smt(dG_ll).
- proc; inline *; wp.
  rnd (fun r => if nth false Sx.ib j then r ^ (elog Sx.gy) else r){1}
      (fun r => if nth false Sx.ib j then r ^ (inv (elog Sx.gy)) else r){1}.
  auto => /> &m1 &m2 *.
  split; 1: smt(expK mulC powM pow_inv supp_dmap supp_duniform).
  move => *; split; 1: by move => ?; apply mu.
  move => _ 2?; split; 1: by apply inmap.
  move => *; split; 2: smt(get_setE get_set_sameE mapE map_set).
  by smt(expK mulC powM pow_inv supp_dmap supp_duniform).
- by move => *; proc; call (: true); auto; smt(dG_ll).
- by move => *; proc; call (: true); auto; smt(dG_ll).
- proc; inline *; wp.
  rnd (fun r => if nth false Sx.ia i then r ^ (elog Sx.gx) else r){1}
      (fun r => if nth false Sx.ia i then r ^ (inv (elog Sx.gx)) else r){1}.
  sp 2 2; if; 1: smt().
  + auto => /> &m1 &m2 *.
    move => *; split; 1: smt(expK mulC powM pow_inv supp_dmap supp_duniform).
    move => *; split; 1: by move => ?; apply mu.
    move => _ 2?; split; 1: by apply inmap.
    move => *; split; 2: smt(get_setE get_set_sameE mapE map_set).
    by smt(expK mulC powM pow_inv supp_dmap supp_duniform).
  + auto => /> &m1 &m2 *.
    move => *; split; 1: smt(expK mulC powM pow_inv supp_dmap supp_duniform).
    move => *; split; 1: by move => ?; apply mu.
    move => _ 2?; split; 1: by apply inmap.
    move => *; split; 2: smt(get_setE get_set_sameE mapE map_set).
    by smt(expK mulC powM pow_inv supp_dmap supp_duniform).
- by move => *; proc; inline Sx.oa; wp; call (: true); auto; smt(dG_ll).
- by move => *; proc; inline Gkx.oa; wp; call (: true); auto; smt(dG_ll).
- proc; inline *; wp.
  rnd (fun r => if nth false Sx.ib j then r ^ (elog Sx.gy) else r){1}
      (fun r => if nth false Sx.ib j then r ^ (inv (elog Sx.gy)) else r){1}.
  sp 2 2; if; 1: smt().
  + auto => /> &m1 &m2 *.
    move => *; split; 1: smt(expK mulC powM pow_inv supp_dmap supp_duniform).
    move => *; split; 1: by move => ?; apply mu.
    move => _ 2?; split; 1: by apply inmap.
    move => *; split; 2: smt(get_setE get_set_sameE mapE map_set).
    by smt(expK mulC powM pow_inv supp_dmap supp_duniform).
  + auto => /> &m1 &m2 *.
    move => *; split; 1: smt(expK mulC powM pow_inv supp_dmap supp_duniform).
    move => *; split; 1: by move => ?; apply mu.
    move => _ 2?; split; 1: by apply inmap.
    move => *; split; 2: smt(get_setE get_set_sameE mapE map_set).
    by smt(expK mulC powM pow_inv supp_dmap supp_duniform).
- by move => *; proc; inline Sx.ob; wp; call (: true); auto; smt(dG_ll).
- by move => *; proc; inline Gkx.ob; wp; call (: true); auto; smt(dG_ll).
- proc; inline Count(Sx).ddh Sx.ddh Count(Gkx).ddh Gkx.ddh; wp; sp 8 9.
  if; 1, 3: by auto; smt().
  seq 2 2 : (! (! nstop Gk.ia Gk.ib G2.ca G2.cb \/
                ! (G.bad => nth false Gk.ia Gk.i_k /\ nth false Gk.ib Gk.j_k) \/
                Gk.k + 1 <= Gk.cddh){2} /\
             ={m0, i0, j0, r0} /\ ={G2.ca, G2.cb} /\
             ={cddh, k, ia, ib}(Sx, Gk) /\
             (Sx.gx = exp g x' /\ Sx.gy = exp g y'){1} /\
             (map (fun i a => if nth false Sx.ia i then a ^ (elog Sx.gx)
                              else a) OAG.m){1} = OAG.m{2} /\
             (map (fun j b => if nth false Sx.ib j then b ^ (elog Sx.gy)
                              else b) OBG.m){1} = OBG.m{2} /\
             (G.bad{2} => Sx.m_crit{1} = exp g (x' * y')) /\
             (G.bad <=> Gk.k + 1 <= Gk.cddh){2} /\
             (if nth false Sx.ia i0 then a ^ (elog Sx.gx) else a){1} = a{2} /\
             (if nth false Sx.ib j0 then b ^ (elog Sx.gy) else b){1} = b{2}).
  + seq 1 1 : (! (! nstop Gk.ia Gk.ib G2.ca G2.cb \/
                  ! (G.bad => nth false Gk.ia Gk.i_k /\
                              nth false Gk.ib Gk.j_k) \/
                  Gk.k + 1 <= Gk.cddh){2} /\
               ={m0, i0, j0, r0} /\ ={G2.ca, G2.cb} /\
               ={cddh, k, ia, ib}(Sx, Gk) /\
               (Sx.gx = exp g x' /\ Sx.gy = exp g y'){1} /\
               (map (fun i a => if nth false Sx.ia i then a ^ (elog Sx.gx)
                                else a) OAG.m){1} = OAG.m{2} /\
               (map (fun j b => if nth false Sx.ib j then b ^ (elog Sx.gy)
                                else b) OBG.m){1} = OBG.m{2} /\
               (G.bad{2} => Sx.m_crit{1} = exp g (x' * y')) /\
               (G.bad <=> Gk.k + 1 <= Gk.cddh){2} /\
               (if nth false Sx.ia i0 then a ^ (elog Sx.gx) else a){1} = a{2}).
    * inline *.
      seq 2 2 : (! (! nstop Gk.ia Gk.ib G2.ca G2.cb \/
                    ! (G.bad => nth false Gk.ia Gk.i_k /\
                                nth false Gk.ib Gk.j_k) \/
                    Gk.k + 1 <= Gk.cddh){2} /\
                 ={m0, i0, j0, r0} /\ ={G2.ca, G2.cb} /\
                 ={cddh, k, ia, ib}(Sx, Gk) /\
                 (Sx.gx = exp g x' /\ Sx.gy = exp g y'){1} /\
                 (map (fun i a => if nth false Sx.ia i then a ^ (elog Sx.gx)
                                  else a) OAG.m){1} = OAG.m{2} /\
                 (map (fun j b => if nth false Sx.ib j then b ^ (elog Sx.gy)
                                  else b) OBG.m){1} = OBG.m{2} /\
                 (G.bad{2} => Sx.m_crit{1} = exp g (x' * y')) /\
                 (G.bad <=> Gk.k + 1 <= Gk.cddh){2} /\
                 x{1} = i0{1} /\ x{2} = i0{2} /\
                 (if nth false Sx.ia i0 then r1 ^ (elog Sx.gx)
                  else r1){1} = r1{2});
        2: by auto; smt(get_setE get_set_sameE mapE map_set).
      rnd (fun r => if nth false Sx.ia x then r ^ (elog Sx.gx) else r){1}
          (fun r => if nth false Sx.ia x then r ^ (inv (elog Sx.gx)) else r){1}.
      auto => /> &m1 &m2 *.
      split; 1: smt(expK mulC powM pow_inv supp_dmap supp_duniform).
      move => *; split; 1: by move => ?; apply mu.
      move => _ 2?; split; 1: by apply inmap.
      move => *; split; 2: smt(get_setE get_set_sameE mapE map_set).
      by smt(expK mulC powM pow_inv supp_dmap supp_duniform).
    * inline *.
      seq 2 2 : (! (! nstop Gk.ia Gk.ib G2.ca G2.cb \/
                    ! (G.bad => nth false Gk.ia Gk.i_k /\
                                nth false Gk.ib Gk.j_k) \/
                    Gk.k + 1 <= Gk.cddh){2} /\
                 ={m0, i0, j0, r0} /\ ={G2.ca, G2.cb} /\
                 ={cddh, k, ia, ib}(Sx, Gk) /\
                 (Sx.gx = exp g x' /\ Sx.gy = exp g y'){1} /\
                 (map (fun i a => if nth false Sx.ia i then a ^ (elog Sx.gx)
                                  else a) OAG.m){1} = OAG.m{2} /\
                 (map (fun j b => if nth false Sx.ib j then b ^ (elog Sx.gy)
                                  else b) OBG.m){1} = OBG.m{2} /\
                 (G.bad{2} => Sx.m_crit{1} = exp g (x' * y')) /\
                 (G.bad <=> Gk.k + 1 <= Gk.cddh){2} /\
                 x{1} = j0{1} /\ x{2} = j0{2} /\
                 (if nth false Sx.ia i0 then a ^ (elog Sx.gx)
                  else a){1} = a{2} /\
                 (if nth false Sx.ib j0 then r1 ^ (elog Sx.gy)
                  else r1){1} = r1{2});
        2: by auto; smt(get_setE get_set_sameE mapE map_set).
      rnd (fun r => if nth false Sx.ib x then r ^ (elog Sx.gy) else r){1}
          (fun r => if nth false Sx.ib x then r ^ (inv (elog Sx.gy)) else r){1}.
      auto => /> &m1 &m2 *.
      split; 1: smt(expK mulC powM pow_inv supp_dmap supp_duniform).
      move => *; split; 1: by move => ?; apply mu.
      move => _ 2?; split; 1: by apply inmap.
      by smt(expK mulC powM pow_inv supp_dmap supp_duniform).
  + sp 0 1; if; 1: smt().

auto => /> &m1 &m2 *; split.

move => *; split.

move => *; split; 1: smt().

move => *; split.

have -> /= : ! (nth false Gk.ia{m2} i0{m2}) by smt().
admit.

admit.

admit.

admit.

admit.

- move => *; proc; inline Sx.ddh; wp; sp 8; if; wp; 2: by auto; smt(dG_ll).
  by call (: true); [ | call (: true)]; auto; smt(dG_ll).
- move => *; proc; inline Gkx.ddh; wp; sp 9; if; wp; 2: by auto; smt(dG_ll).
  by call (: true); [ | call (: true)]; auto; smt(dG_ll).
- by auto; smt(map_empty).
qed.


local lemma Sx_S &m x y : x \in EU => y \in EU =>
 Pr[GameSx(A).main(x, y) @ &m : Sx.m_crit = exp g (x * y)] =
 Pr[GameS(A).main(exp g x, exp g y) @ &m : S.m_crit = exp g (x * y)].
proof.


admitted.


*)

end section.

end Inner.

(* The optimal bound is obtained by setting pa = 1/(q_oa + 1) and likewise for pb *)

lemma pa_bound :
  0%r < (1%r/(q_oa + 1)%r) &&
  if q_oa = 0 then (1%r/(q_oa + 1)%r) <= 1%r else (1%r/(q_oa + 1)%r) < 1%r.
proof. smt. qed.

lemma pb_bound :
  0%r < (1%r/(q_ob + 1)%r) &&
  if q_ob = 0 then (1%r/(q_ob + 1)%r) <= 1%r else (1%r/(q_ob + 1)%r) < 1%r.
proof. smt. qed.

clone import Inner as I with
  op pa <- (1%r/(q_oa + 1)%r),
  op pb <- (1%r/(q_ob + 1)%r),
  axiom pa_bound <- pa_bound, (* does anything break/change if we remove this? *)
  axiom pb_bound <- pb_bound.

lemma foo_monotone (n m : int) :
  0 <= n => n <= m => (n%r/(n+1)%r)^(n+1) <= (m%r/(m+1)%r)^(m+1).
proof.
suff nP : forall n, 0 <= n =>
                    (n%r / (n + 1)%r) ^ (n + 1) <=
                    ((n + 1)%r / (n + 1 + 1)%r) ^ (n + 1 + 1).
- move => n_ge0; rewrite StdOrder.IntOrder.ler_eqVlt; move => [<- /#|mP].
  have {mP} [q] : (exists q, m - n = q /\ 0 < q) by smt ().
  have [p] : exists p, p = q - 1 by smt().
  rewrite eq_sym subr_eq => ->; rewrite subr_eq addrC.
  move => {q} [-> pP]; have {pP} pP : 0 <= p by smt().
  elim: p pP; 1: smt().
  move => i i_ge0 iP; apply (ler_trans _ _ _ iP).
  apply (ler_trans (((n+i+1)%r/((n+i+1)+1)%r)^((n+i+1)+1))); 1: smt().
  have {i_ge0 n_ge0} n_ge0 : 0<= n + i + 1 by smt().
  by apply (ler_trans _ _ _ (nP _ n_ge0)); smt().
- move => {m n} n; rewrite StdOrder.IntOrder.ler_eqVlt; move => [<-|n_gt0];
    1: by rewrite add0r mul0r exprSr // !expr1; smt(mulr_ge0).
  have -> : ((n + 1)%r / (n + 1 + 1)%r) ^ (n + 1 + 1) =
            (n%r / (n + 1)%r) ^ (n + 1) * ((n + 1)%r / (n + 2)%r) *
            ((n + 1)%r ^2 / (n%r * (n + 2)%r)) ^ (n + 1).
  + rewrite mulrAC -exprMn; 1: smt().
    suff -> : n%r / (n + 1)%r * ((n + 1)%r ^ 2 / (n%r * (n + 2)%r)) =
              (n + 1)%r / (n + 2)%r by smt(exprSr).
    by rewrite expr2; algebra; smt(expr2).
  have {1}-> : (n%r/(n+1)%r)^(n+1) = (n%r/(n+1)%r)^(n+1)*1%r by smt().
  rewrite -subr_ge0 -!mulrA -mulrBr mulr_ge0; 1: smt(expr_gt0).
  rewrite subr_ge0 -ler_pdivr_mull; 1: smt().
  rewrite -ler_pdivr_mull; 1: smt().
  apply (ler_trans (1%r + 1%r / (n + 1)%r));
    1: by rewrite -subr_ge0 le0r; left; algebra; smt().
  have -> : (n + 1)%r ^ 2 / (n%r * (n + 2)%r) = 1%r + 1%r / (n%r * (n + 2)%r)
    by algebra; smt(expr2).
  apply (ler_trans (1%r + (n + 1)%r / (n%r * (n + 2)%r))).
  + suff : 1%r / (n + 1)%r <= (n + 1)%r / (n%r * (n + 2)%r) by smt().
    rewrite -ler_pdivl_mulr; 1: smt().
    apply (ler_trans ((n + 1)%r ^ 2 / (n%r * (n + 2)%r))).
    * move: (subr_sqr_1 (n + 1)%r); rewrite subr_eq => ->.
      rewrite ler_pdivl_mulr ?mul1r; 1: smt().
      suff: n%r * (n + 2)%r <= ((n + 1)%r - 1%r) * ((n + 1)%r + 1%r); 1: smt().
      by rewrite -fromintD -fromintB; smt().
    * by rewrite -subr_ge0 le0r; left; algebra; smt(expr2).
  + rewrite Binomial.BCR.binomial; 1: smt().
    rewrite 2?rangeSr; 1, 2: smt().
    rewrite !StdBigop.Bigreal.BRA.big_rcons /predT /=.
    rewrite -addrA Binomial.binn; 1: smt().
    apply ler_paddl.
    * apply StdBigop.Bigreal.sumr_ge0_seq.
      move => a aP _; rewrite mulr_ge0; 1: smt(Binomial.ge0_bin).
      by rewrite expr1z mul1r; smt(expr_gt0).
    * have -> : n + 1 - n = 1 by algebra.
      rewrite !expr1z expr0 expr1 !mul1r.
      suff -> : (Binomial.bin (n + 1) n)%Binomial = n + 1 by smt().
      have {n_gt0} n_ge0 : 0 <= n by smt().
      elim: n n_ge0; 1: smt(Binomial.bin0).
      move => n n_ge0 nP; rewrite Binomial.binSn; 1, 2: smt().
      by rewrite nP Binomial.binn; smt().
qed.

section.

declare module A : Adversary {G1, G2, G, S, Count,
                              OAEU, OBEU, OAEUt, OBEUt,
                              OA0EU, OA1EU, OB0EU, OB1EU,
                              RO, RO_DOMt, ROT.RO, ROF.RO, FROEUt.RO,
                              OAG, OBG, FROG.RO}.

axiom A_ll : forall (O <: CDH_RSR_Oracles{A}),
  islossless O.oA =>
  islossless O.oB =>
  islossless O.oa =>
  islossless O.ob =>
  islossless O.ddh =>
  islossless A(O).guess.

axiom A_bound : forall (O <: CDH_RSR_Oracles{A}),
  hoare [A(Count(O)).guess :
         Count.ca = 0 /\ Count.cb = 0 /\ Count.cddh = 0 ==>
         Count.ca <= q_oa /\ Count.cb <= q_ob /\ Count.cddh <= q_ddh].

lemma G1G2_NCDH &m :
  `| Pr[Game(G1,A).main() @ &m : res ] - Pr[ Game(G2,A).main() @ &m : res] | <=
  q_ddh%r * (max 1 (4*q_oa))%r * (max 1 (4 * q_ob))%r *
  Pr [NCDH.Game(B(A)).main() @ &m : res] + DELTA.
proof.
have H := I.G1G2_NCDH (<:A) A_ll A_bound &m.
apply (ler_trans _ _ _ H) => {H}.
suff Hmax : forall (n : int),
              0 <= n =>
              1%r/((1%r-1%r/(n+1)%r)^n*(1%r/(n+1)%r)) <= (max 1 (4*n))%r.
- rewrite ler_add2r ler_wpmul2r; 1: smt.
  rewrite -!mulrA ler_wpmul2l; 1: smt(q_ddh_ge1).
  apply (ler_trans ((1%r/((1%r-1%r/(q_oa+1)%r)^q_oa*(1%r/(q_oa+1)%r))) *
                    (1%r/((1%r-1%r/(q_ob+1)%r)^q_ob*(1%r/(q_ob+1)%r)))));
    1: smt.
  apply ler_pmul; smt(q_oa_ge0 q_ob_ge0 divr_ge0 expr_ge0 invr_ge0 mulr_ge0).
- move => n n_ge0; case (n = 0) => [-> /=|H]; 1: smt(expr0).
  have {H n_ge0} n_gt0 : 1 <= n by smt().
  apply (ler_trans (4 * n)%r); 2: smt().
  rewrite ler_pdivr_mulr; 1: smt (divr_gt0 expr_gt0 mulr_gt0).
  rewrite mulrC -ler_pdivr_mulr; 1: smt().
  have -> : 1%r / (4 * n)%r = (1%r /(1 + 1)%r)^(1 + 1) * (1%r / n%r)
    by rewrite !div1r expr2 -!invfM fromintD fromintM mulrDl mul1r -addrA.
  suff -> : (1%r - 1%r / (n + 1)%r) ^ n * (1%r / (n + 1)%r) =
            (n%r / (n + 1)%r)^(n + 1) * (1%r / n%r)
    by rewrite ler_wpmul2r; [smt(divr_ge0)|by apply foo_monotone].
  apply (can2_eq (fun x, x * (1%r / (n + 1)%r)) (fun x, x * (n + 1)%r)) => /=;
    1,2: by move => x; smt(divrr).
  rewrite -mulrA exprSr; 1: smt().
  rewrite- mulrA -{2}invf_div divrr ?mulr1; 1: smt().
  suff: 1%r - inv (n + 1)%r = n%r / (n + 1)%r; smt.
qed.

end section.
