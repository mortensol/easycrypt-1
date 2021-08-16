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
    (forall i x, x \in xs =>  g i (f i x) = x) => mapi g (mapi f xs) = xs.
proof. rewrite /mapi; elim: xs 0 => //=; smt(). qed.

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

(* TODO: For [I = fset1 i], this subsumes dlist_nthE *)
lemma dlist_setE x0 (d : 'a distr) (p : 'a -> bool) n (I : int fset) : 
  is_lossless d => (forall i, i \in I => 0 <= i && i < n) => 
  mu (dlist d n) (fun xs => forall i, i \in I => p (nth x0 xs i)) = (mu d p)^(card I).
proof.
move => d_ll. elim/natind : n I => [n n_le0 I ranI|n n_ge0 IH I ranI].
  have -> : I = fset0 by smt(in_eq_fset0).
  rewrite muT ?dlist_ll; smt(in_fset0 fcards0 expr0).
rewrite dlistS //= dmapE.
pose P1 x := (0 \in I => p x).
pose P2 xs := (forall i, i \in image (fun i => i - 1) (I `\` fset1 0)  => p (nth x0 xs i)).
have -> : ((fun (xs : 'a list) => forall (i : int), i \in I => p (nth x0 xs i)) \o 
           fun (xy : 'a * 'a list) => xy.`1 :: xy.`2) =  
          (fun ab : 'a * 'a list => P1 ab.`1 /\ P2 ab.`2).
  apply/fun_ext => -[x xs]; rewrite /(\o) /= /P1 /P2.
  apply/eq_iff; split => [H|[H0 Hi]]. split; 1: exact H.
  move => i /imageP [j [J1 J2]]; smt(in_fsetD1).
  move => i; case (i = 0) => [/#|iN0 iI]; apply: (Hi (i-1)). 
  apply/imageP; exists i. smt(in_fsetD1).
rewrite dprodE.
have {IH} IH := IH (image (transpose Int.(+) (-1)) (I `\` fset1 0)) _.
  move => i /imageP [j [J1 <-]] /=. smt(in_fsetD1 in_fset0).
rewrite IH inj_card_image; 1: smt().
rewrite /P1 (fcardD1 I 0); case (0 \in I) => /= [I0|IN0]. 
- by rewrite exprS ?card_ge0; smt. 
- by rewrite d_ll. 
qed.

lemma dlist_nthE x0 (d : 'a distr) (p : 'a -> bool) i n : 
  is_lossless d => 0 <= i && i < n =>
  mu (dlist d n) (fun xs => p (nth x0 xs i)) = mu d p.
proof.
move => d_ll Hn.
have E := dlist_setE x0 d p n (fset1 i) d_ll _; 1: smt(in_fset1).
have -> : (fun xs => p (nth x0 xs i)) = 
          (fun (xs : 'a list) => forall (i0 : int), i0 \in fset1 i => p (nth x0 xs i0)).
  by apply fun_ext => xs; smt(in_fset1).
by rewrite E fcard1 expr1.
(* initial direct proof 
move => d_ll. elim/natind : n i => [/#|n n_ge0 IH i Hi].
pose P1 x := (i = 0 => p x).
pose P2 xs := i <> 0 => p (nth x0 xs (i - 1)).
have -> : (fun (xs : 'a list) => p (nth x0 xs i)) = 
          (fun (xs : 'a list) => P1 (head x0 xs) /\ P2 (behead xs)) by smt().
rewrite dlistSE //; case: (i = 0) => [i0|iN0].
- rewrite (eq1_mu _ P2); 1,2: smt(dlist_ll). 
  have -> : P1 = p; smt(). 
- rewrite (eq1_mu _ P1) //; 1: smt(). 
  have -> : P2 = (fun (xs : 'a list) => p (nth x0 xs (i - 1))) by smt(). 
  by rewrite IH; smt(). *)
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

op nth' (zs : 'a list) = nth witness zs.

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

  proc ddh(m, i, j) = { return m = exp g (nth' a i * nth' b j); }
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
  proc ob (i : int) = { cb <- i::cb ; return nth' b i; }

  proc ddh(m, i, j) = {
    return
      if (i \in ca || j \in cb)
      then m = exp g (nth' a i * nth' b j)
      else false;
   }
}.

(* Intermediate games:
- G sets "bad" where G1 and G2 differ
- G' behaves like G, but samples invertible exponents (i.e. from EU *)

module G = {
  import var G1
  include var G2 [-ddh,init]
  var bad : bool

  proc init () = {
    G2.init();
    bad <- false;
  }

  proc ddh(m : G, i,j : int) = {
    var r,t;
    t <- m = exp g (nth' a i * nth' b j);

    r <- false;
    (* answer honestly if a[i] or b[j] was leaked *)
    if (i \in ca || j \in cb) { r <- t; }

    (* execute bad if neither was leaked and "false" is not the right answer *)
    if (!(i \in ca || j \in cb) /\ t) { bad <- true; }

    return r;
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

    (* always answer honestly *)
    t <- m = exp g (nth' a i * nth' b j);

    (* execute bad if neither was leaked and "false" is not the right answer *)
    if (!(i \in ca || j \in cb) /\ t) { bad <- true; }

    return t;
  }
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
  var stop : bool
  var gs : (G*int*int) list

  proc init (gx' : G, gy' : G) = {
    ia <$ dlist (dbiased pa) na;
    ib <$ dlist (dbiased pb) nb;
    a <$ dlist (duniform (elems EU)) na;
    b <$ dlist (duniform (elems EU)) nb;
    ca <- [];
    cb <- [];
    gx <- gx';
    gy <- gy';
    stop <- false;
    gs <- [];
  }

  proc oa (i : int) = {
    if (nth false ia i) { stop <- true; }
    ca <- i :: ca;
    return (nth' a i);
  }

  proc ob (j : int) = {
    if (nth false ib j) { stop <- true; }
    cb <- j :: cb;
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

    r <- false;

    if (i \in ca) {
      r <- m = (if nth false ib j then gy^(nth' b j) else exp g (nth' b j))^nth' a i;
    }
    if (j \in cb) {
      r <- m = (if nth false ia i then gx^(nth' a i) else exp g (nth' a i))^nth' b j;
    }

    (* record queries *)
    gs <- (m,i,j) :: gs ;

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
  var g : G * int * int

  proc solve(gx gy : G) : G = {
    GameS(A).main(gx,gy);
    g <$ duniform S.gs;
    return g.`1;
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
  hoare [ A(Count(O)).guess : true ==> Count.ca <= q_oa /\ Count.cb <= q_ob /\ Count.cddh <= q_ddh].

(* same as G', but with a stop event equivalent to S *)
local module G's = {
  import var G1 G2 G
  include var G' [-init,oa,ob]
  var ia, ib : bool list (* inject a/b *)
  var stop : bool

  proc init () = {
    ia <$ dlist (dbiased pa) na;
    ib <$ dlist (dbiased pb) nb;
    a <$ dlist (duniform (elems EU)) na;
    b <$ dlist (duniform (elems EU)) nb;
    ca <- [];
    cb <- [];
    bad <- false;
    stop <- false;
  }

  proc oa (i) = {
    if (nth false ia i) { stop <- true; }
    ca <- i :: ca;
    return (nth' a i);
  }

  proc ob (j : int) = {
    if (nth false ib j) { stop <- true; }
    cb <- j :: cb;
    return (nth' b j);
  }
}.


lemma G1G2_Gbad &m :
    `| Pr[ Game(G1,A).main() @ &m : res ] - Pr[ Game(G2,A).main() @ &m : res ] | <=
       Pr[ Game(G,A).main() @ &m : G.bad ].
proof.
(* Introduce bad events into G1 and G2 *)
have -> : Pr[ Game(G2,A).main() @ &m : res ] = Pr[ Game(G,A).main() @ &m : res ].
  byequiv => //. proc; inline *.
  call (_ : ={glob G2}) => //; 1..4: (by sim); last by auto => />.
  by proc; inline *; auto.
have -> : Pr[ Game(G1,A).main() @ &m : res ] = Pr[ Game(G1b,A).main() @ &m : res ].
  byequiv => //; proc; inline *.
  call (_ : ={glob G1}); 1..4: (by sim); last by auto => />.
  by proc; inline *; auto.
(* up-to-bad reasoning *)
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

(* this is only enough if we can prove that P[G's : !stop] and [G's :
bad] are independent, which is most likely not the case *)
local lemma G's_stop &m : 
    Pr [Game(G's,A).main() @ &m : !G's.stop] >= (1%r-clamp pa)^q_oa * (1%r- clamp pb)^q_ob.
proof.
have H : hoare [Game(G's,A).main : true ==> size G2.ca <= q_oa /\ size G2.cb <= q_ob ].
  admit. (* A_bound *)
have -> : Pr[Game(G's, A).main() @ &m : !G's.stop] = 
          Pr[Game(G's, A).main() @ &m : (forall i, i \in G2.ca => !nth false G's.ia i) /\ 
                                        (forall i, i \in G2.cb => !nth false G's.ib i) ].
byequiv => //; proc; inline *.
call(: ={glob G's,glob G1,glob G2,glob Count} /\
      (!G's.stop{1} <=> (forall (i : int), i \in G2.ca{2} => ! nth false G's.ia{2} i) /\
                         forall (i : int), i \in G2.cb{2} => ! nth false G's.ib{2} i)); 
  by (try proc); inline *; auto => /> /#.
admitted.

local lemma G's_stop' &m :
    (1%r-clamp pa)^q_oa * (1%r- clamp pb)^q_ob * Pr[Game(G's,A).main() @ &m : G.bad]
    <= Pr [Game(G's,A).main() @ &m : G.bad /\ !G's.stop].
proof.
(* proof idea:
  - If Game(G's,A).main() triggers G.bad, it does so by making at most 
  q_oa queries to oa and q_ob queries to ob. 
  - thus the query logs ca and cb have at most length q_oa (resp. q_ob)
  - !stop holds if the log contains no i(resp. j) such that ia[i] (resp. ib[j]) is true
  - all the ia[i]/ib[j] are sampled independently at the start. *)   
admitted.

local lemma G's_S &m x y : x \in EU => y \in EU => 
    Pr [Game(G's,A).main() @ &m : G.bad /\ !G's.stop] <= 
    Pr [GameS(A).main(exp g x, exp g y) @ &m : exists m i j, (m,i,j) \in S.gs /\ 
        (nth false S.ia i && nth false S.ib j => m = exp g (nth' G1.a i * nth' G1.b j * x * y)) ].
proof.
move => x_EU y_EU.
byequiv => //; proc; inline *. 
call (: S.stop, 
  ={glob Count,G2.ca,G2.cb} /\ ={ia,ib,stop}(G's,S) /\ 
  (S.gx = exp g x /\ S.gy = exp g y){2} /\
  (forall i,
    nth' G1.a{1} i = if nth false S.ia{2} i then nth' G1.a{2} i * x else nth' G1.a{2} i) /\
  (forall j,
    nth' G1.b{1} j = if nth false S.ib{2} j then nth' G1.b{2} j * y else nth' G1.b{2} j) /\
  (forall i, i \in G2.ca{2} => !nth false S.ia{2} i) /\
  (forall j, j \in G2.cb{2} => !nth false S.ib{2} j) /\ 
  (G.bad{1} => exists (m : G) (i j : int),
    ((m, i, j) \in S.gs{2}) /\ 
    (nth false S.ia{2} i && nth false S.ib{2} j => m = exp g (nth' G1.a{2} i * nth' G1.b{2} j * x * y))), 
  ={stop}(G's,S));
  try by move => *; proc; inline*; auto.
- exact: A_ll.
- proc; inline *; auto => /> &1 &2 NS Ha Hb Hca Hcb ?. rewrite Ha. smt(mulA mulC expM). 
- proc; inline *; auto => /> &1 &2 NS Ha Hb Hca Hcb ?. rewrite Hb. smt(mulA mulC expM).
- proc; inline *; auto => /> &1 &2 NS Ha Hb Hca Hcb ?. smt().
- move => *; proc; inline*; auto => /> /#.
- move => *; proc; inline*; auto => /> /#.
- proc; inline *; auto => /> &1 &2 NS Ha Hb Hca Hcb ?. smt().
- move => *; proc; inline*; auto => /> /#.
- move => *; proc; inline*; auto => /> /#.
- proc; inline *; auto => /> &1 &2 NS Ha Hb Hca Hcb Hinv. 
- (* ddh sumulation *)
  move: (i{2}) (j{2}) => i j. 
  split => [i_ca|iNca]; (split => [j_cb|jNcb]); (split => [|Hbad]).
  + rewrite Ha. smt(mulA mulC expM). 
  + case: (Hinv Hbad) => m' i' j' ?. exists m' i' j'. smt().
  + rewrite Hb. smt(mulA mulC expM). 
  + case: (Hinv Hbad) => m' i' j' ?. exists m' i' j'. smt().
  + rewrite Ha. smt(mulA mulC expM). 
  + case: (Hinv Hbad) => m' i' j' ?. exists m' i' j'. smt().
  + exists (exp g (nth' G1.a{1} i * nth' G1.b{1} j)) i j. smt(mulA mulC expM).
  + move => {Hbad} Hbad. case: (Hinv Hbad) => m' i' j' ?. exists m' i' j'. smt().
(* establishing the invariant *)
wp; sp.
rnd (mapi (fun j z => if nth false S.ib{2} j then z * inv y else z))
    (mapi (fun j z => if nth false S.ib{2} j then z * y else z)).
rnd (mapi (fun i z => if nth false S.ia{2} i then z * inv x else z))
    (mapi (fun i z => if nth false S.ia{2} i then z * x else z)).
rnd; rnd; auto => /> ia d_ia ib d_ib.
have [? ?] : 0 <= na /\ 0 <= nb. smt(na_ge0 nb_ge0).
have Hmapi : forall a' b' na' x', 0 <= na' => x' \in EU => a' \in dlist (duniform (elems EU)) na' =>
    mapi (fun (i : int) (z : Z) => if b' i then z * x' else z) a' \in dlist (duniform (elems EU)) na'.
  move => a' b' na' x' na'_ge0 x'_EU. rewrite supp_dlist ?na'_ge0 => -[size_a' /allP supp_a'].
  apply: dlist_fu_eq; 1: by rewrite size_mapi size_a'.
  move => z /mapiP /(_ witness) [n] /= [Hn Hz].
  have ? : nth' a' n \in EU. rewrite memE -supp_duniform. exact/supp_a'/mem_nth.
  rewrite supp_duniform -memE. smt(Emult).
split => [a d_a | ? ].
  rewrite in_mapiK => //= i z z_a. case (nth false ia i) => // _.
  rewrite invK //. exact: dlist_EU d_a z_a.
split => [a d_a | _ ].
  apply: dlist_uni => //; 1: exact: duniform_uni.
  exact: Hmapi.
move => a a_d; split => [| _].
  apply: Hmapi => //. exact: Einv.
split => [|_].
  rewrite in_mapiK => //= i z z_a. case (nth false ia i) => // _.
  rewrite invK' //. exact: dlist_EU a_d z_a.
split => [b b_d | _ ].
  rewrite in_mapiK => //= j z z_b. case (nth false ib j) => // _.
  rewrite invK //. exact: dlist_EU b_d z_b.
split => [b b_d | _].
  apply: dlist_uni => //; 1: exact: duniform_uni.
  exact: Hmapi.
move => b b_d; split => [| _].
  apply: Hmapi => //. exact: Einv.
split => [|_].
  rewrite in_mapiK => //= j z z_b. case (nth false ib j) => // _.
  rewrite invK' //. exact: dlist_EU b_d z_b.
split; first split.
- move => i. case (0 <= i && i < size a) => [i_in|i_out].
  + rewrite /nth' (nth_mapi witness a) //=.
    case (nth false ia i) => //. rewrite invK' //.
    suff: nth witness a i \in a by apply: dlist_EU a_d. exact/mem_nth.
  + rewrite /nth' !(nth_out false) //= ?(nth_out witness) ?size_mapi //.
    smt(supp_dlist_size).
- move => j. case (0 <= j && j < size b) => [j_in|j_out].
  + rewrite /nth'. rewrite (nth_mapi witness b) //=.
    case (nth false ib j) => //. rewrite invK' //.
    suff: nth witness b j \in b by apply: dlist_EU b_d. exact/mem_nth.
  + rewrite /nth' !(nth_out false) //= ?(nth_out witness) ?size_mapi //.
    smt(supp_dlist_size).
by move => _ _ />; smt().
qed.



(* not really the lemma we want 
lemma G'_S_stop &m x y : x \in EU => y \in EU =>
   `| Pr [ Game(G',A).main() @ &m : res ] - Pr [ GameS(A).main(exp g x,exp g y) @ &m : res ] |
    <= Pr [ GameS(A).main(exp g x,exp g y) @ &m : S.stop ].
proof.
move => x_EU y_EU.
have -> : Pr[ Game(G',A).main() @ &m : res ] = Pr[ Game(G's,A).main() @ &m : res ].
  byequiv => //. proc; inline *.
  call (: ={glob G1,glob G2}); try by sim.
  auto => />; smt(dlist_ll dbiased_ll).
byequiv : G's.stop => //; last by smt().
proc; inline *. sp.
call (_ : S.stop,
  ={glob Count,G2.ca,G2.cb} /\ ={ia,ib,stop}(G's,S) /\
  (S.gx = exp g x /\ S.gy = exp g y){2} /\
  (forall i,
    nth' G1.a{1} i = if nth false S.ia{2} i then nth' G1.a{2} i * x else nth' G1.a{2} i) /\
  (forall j,
    nth' G1.b{1} j = if nth false S.ib{2} j then nth' G1.b{2} j * y else nth' G1.b{2} j) /\
  (forall i, i \in G2.ca{2} => !nth false S.ia{2} i) /\
  (forall j, j \in G2.cb{2} => !nth false S.ib{2} j)
  ,
  G's.stop{1}); try by move => *; proc; inline*; auto => />.
- exact: A_ll.
- proc; inline *; auto => /> &m1 &m2 _ Ha Hb. rewrite Ha. smt(mulA mulC expM).
- proc; inline *; auto => /> &m1 &m2 _ Ha Hb. rewrite Hb. smt(mulA mulC expM).
- proc; inline*; auto => />. smt().
- proc; inline*; auto => />. smt().
- proc; inline*; auto => /> &1 &2 NS Ha Hb Hca Hcb. smt(mulA mulC expM).
(* main goal: establishing the invariant *)
wp.
rnd (mapi (fun j z => if nth false S.ib{2} j then z * inv y else z))
    (mapi (fun j z => if nth false S.ib{2} j then z * y else z)).
rnd (mapi (fun i z => if nth false S.ia{2} i then z * inv x else z))
    (mapi (fun i z => if nth false S.ia{2} i then z * x else z)).
rnd; rnd; auto => /> ia d_ia ib d_ib.
have [? ?] : 0 <= na /\ 0 <= nb. smt(na_ge0 nb_ge0).
have Hmapi : forall a' b' na' x', 0 <= na' => x' \in EU => a' \in dlist (duniform (elems EU)) na' =>
    mapi (fun (i : int) (z : Z) => if b' i then z * x' else z) a' \in dlist (duniform (elems EU)) na'.
  move => a' b' na' x' na'_ge0 x'_EU. rewrite supp_dlist ?na'_ge0 => -[size_a' /allP supp_a'].
  apply: dlist_fu_eq; 1: by rewrite size_mapi size_a'.
  move => z /mapiP /(_ witness) [n] /= [Hn Hz].
  have ? : nth' a' n \in EU. rewrite memE -supp_duniform. exact/supp_a'/mem_nth.
  rewrite supp_duniform -memE. smt(Emult).
split => [a d_a | _ ].
  rewrite in_mapiK => //= i z z_a. case (nth false ia i) => // _.
  rewrite invK //. exact: dlist_EU d_a z_a.
split => [a d_a | _ ].
  apply: dlist_uni => //; 1: exact: duniform_uni.
  exact: Hmapi.
move => a a_d; split => [| _].
  apply: Hmapi => //. exact: Einv.
split => [|_].
  rewrite in_mapiK => //= i z z_a. case (nth false ia i) => // _.
  rewrite invK' //. exact: dlist_EU a_d z_a.
split => [b b_d | _ ].
  rewrite in_mapiK => //= j z z_b. case (nth false ib j) => // _.
  rewrite invK //. exact: dlist_EU b_d z_b.
split => [b b_d | _].
  apply: dlist_uni => //; 1: exact: duniform_uni.
  exact: Hmapi.
move => b b_d; split => [| _].
  apply: Hmapi => //. exact: Einv.
split => [|_].
  rewrite in_mapiK => //= j z z_b. case (nth false ib j) => // _.
  rewrite invK' //. exact: dlist_EU b_d z_b.
split; first split.
- move => i. case (0 <= i && i < size a) => [i_in|i_out].
  + rewrite /nth' (nth_mapi witness a) //=.
    case (nth false ia i) => //. rewrite invK' //.
    suff: nth witness a i \in a by apply: dlist_EU a_d. exact/mem_nth.
  + rewrite /nth' !(nth_out false) //= ?(nth_out witness) ?size_mapi //.
    smt(supp_dlist_size).
- move => j. case (0 <= j && j < size b) => [j_in|j_out].
  + rewrite /nth'. rewrite (nth_mapi witness b) //=.
    case (nth false ib j) => //. rewrite invK' //.
    suff: nth witness b j \in b by apply: dlist_EU b_d. exact/mem_nth.
  + rewrite /nth' !(nth_out false) //= ?(nth_out witness) ?size_mapi //.
    smt(supp_dlist_size).
move => _ _. smt().
qed.
*)



lemma nth_dlist b i n p :
  0%r <= p => p <= 1%r => 0 <= i => i < n =>
  mu (dlist (dbiased p) n) (transpose (nth b) i) = p.
proof.
move => *; rewrite (dlist_nthE b _ (fun x => x)) ?dbiasedE /=; 
  smt(clamp_id dlist_ll dbiased_ll).
qed.


lemma S_ia &m gx gy i e :
  e \in EU => 0%r <= pa => pa <= 1%r => 0 <= i /\ i < na =>
  Pr[ GameS(A).main(gx, gy) @ &m : nth' S.ia i ] = pa.
proof.
move => eP pa_ge0 pa_le1 [i_ge0 i_lt_na]; byphoare => //; proc; inline *.
seq 3: (nth' S.ia i) pa 1%r (1%r - pa) 0%r; 1: by auto.
- by rnd; auto => />; apply nth_dlist.
- call (: true); 1: (by exact A_ll); 1..5: (by proc; inline *; auto).
  auto => />; smt(dbiased_ll dlist_ll duniform_ll).
- by hoare; call (: true); 1..5: (by proc; inline *; auto); auto => />.
- by auto => />.
qed.

lemma S_ib &m gx gy j e :
  e \in EU => 0%r <= pb => pb <= 1%r => 0 <= j /\ j < nb =>
  Pr[ GameS(A).main(gx,gy) @ &m : nth' S.ib j ] = pb.
proof.
move => eP pb_ge0 pb_le1 [i_ge0 i_lt_nb]; byphoare => //; proc; inline *.
seq 4: (nth' S.ib j) pb 1%r (1%r - pb) 0%r; 1: by auto.
- by rnd; rnd; auto => />; split; [by apply nth_dlist|smt(dbiased_ll dlist_ll)].
- call (: true); 1: (by exact A_ll); 1..5: (by proc; inline *; auto).
  by wp; rnd; rnd; skip => />; smt(dbiased_ll dlist_ll duniform_ll).
- by hoare; call (: true); 1..5: (by proc; inline *; auto); auto => />.
- by auto => />.
qed.

lemma GameS_size_gs : hoare [GameS(A).main : true ==> size S.gs <= q_ddh].
admitted. (* needs a axiom on the number of queries performed by A *)

lemma B_qddh &m x y : 
  1%r/q_ddh%r * 
  Pr[ GameS(A).main(exp g x,exp g y) @ &m : exists m i j, (m,i,j) \in S.gs /\ 
      (nth false S.ia i && nth false S.ib j => m = exp g (nth' G1.a i * nth' G1.b j * x * y)) ] <=
  Pr[B(A).solve(exp g x,exp g y) @ &m : 
    let (m,i,j) = B.g in 
    (nth false S.ia i && nth false S.ib j => m = exp g (nth' G1.a i * nth' G1.b j * x * y)) ].
proof. 
pose p := Pr[ GameS(A).main(exp g x,exp g y) @ &m : exists m i j, (m,i,j) \in S.gs /\ 
      (nth false S.ia i && nth false S.ib j => m = exp g (nth' G1.a i * nth' G1.b j * x * y)) ].
byphoare (_ : gx = exp g x /\ gy = exp g y /\ glob A = (glob A){m} ==> _) => //. proc => /=. 
seq 1 : (exists (m : G) (i j : int),
            ((m, i, j) \in S.gs) /\
            (nth false S.ia i && nth false S.ib j => m = exp g (nth' G1.a i * nth' G1.b j * x * y)))
      p (1%r/q_ddh%r) _ 0%r (size S.gs <= q_ddh).
- by call (: true ==> size S.gs <= q_ddh) => //; apply GameS_size_gs.
- (* this is the definition of p, up to the implicit memory of the pHL goal *)
  (* proof follows what's done in LorR.ec, is there a simpler way? *)
  call (: gx = exp g x /\ gy = exp g y /\ (glob A) = (glob A){m} ==> 
    exists (m : G) (i j : int),
      ((m, i, j) \in S.gs) /\ 
      (nth false S.ia i && nth false S.ib j => m = exp g (nth' G1.a i * nth' G1.b j * x * y))).
  + bypr => /> &m' -> -> eqA. rewrite /p /=. (* only the memory differs *)
    byequiv => //; proc; inline *. 
    call (: ={glob Count, glob S, glob G1, glob G2}); try sim.
    auto => /> _ _ _ _ _ _ _ _. by rewrite eqA.
  + skip => />.
- rnd; skip => /> &1 size_gs m i j mij_gs mij_good. 
  apply (ler_trans (mu1 (duniform S.gs{1}) (m,i,j))).
  + rewrite duniform1E mij_gs /=. smt. (* slow, but works *)
  + apply mu_sub => -[m' i' j']. case => -> -> -> /=. exact mij_good.
- by auto.
- by auto.
qed.

lemma bar &m x y : 
  pa * pb * Pr[B(A).solve(exp g x,exp g y) @ &m : 
    let (m,i,j) = B.g in 
    (nth false S.ia i && nth false S.ib j => m = exp g (nth' G1.a i * nth' G1.b j * x * y)) ] <=
  Pr[B(A).solve(exp g x,exp g y) @ &m : 
    let (m,i,j) = B.g in m = exp g (nth' G1.a i * nth' G1.b j * x * y) ].
admitted.

(* does this follow (easily)? *)
lemma G'_S' &m x y :  
   pa * pb * Pr[ Game(G',A).main() @ &m : G.bad ] <= 
   Pr[ GameS(A).main(exp g x,exp g y) @ &m : 
       exists m i j, (m,i,j) \in S.gs /\ m = exp g (nth' G1.a i * nth' G1.b j * x * y) ] + 
   Pr[ GameS(A).main(exp g x,exp g y) @ &m : S.stop ].
proof.
abort. (*likely not ... *)

lemma badG'_cdh &m :
    Pr[ Game(G',A).main() @ &m : G.bad ] <= p * Pr [ NCDH.Game(B(A)).main() @ &m : res ].
admitted.
