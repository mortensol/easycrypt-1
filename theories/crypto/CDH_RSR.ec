require import AllCore List Distr DBool DInterval DList.
require import FinType FSet SmtMap NominalGroup.

import Distr.MRat.
import DBool.Biased.

clone import NominalGroup.NominalGroup as N.

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

module B (A : Adversary) : NCDH.Adversary = {
   proc solve(gx gy : G) : G = { 
    var g;

    S.init(gx,gy);
    A(S).guess();
    (* return random potentially good group element *)
    g <$ duniform S.gs;
    return g.`1;
  }
}.

op DELTA : real. (* TODO specify *)
op p : real.     (* TODO specify *)

section.


declare module A : Adversary {G1,G2,G,Count,S}.

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


axiom A_ll : forall (O <: CDH_RSR_Oracles{A}),
  islossless O.oA => islossless O.oB => islossless O.oa => islossless O.ob => islossless O.ddh => islossless A(O).guess.


lemma G1G2_Gbad &m : 
    `| Pr[ Game(G1,A).main() @ &m : res ] - Pr[ Game(G2,A).main() @ &m : res ] | <=
       Pr[ Game(G,A).main() @ &m : G.bad ].
proof.
(* Intruduce bad events into G1 and G2 *)
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

(** theory of [mapi], move elsewhere *)
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

local lemma dlist_EU n x xs : xs \in dlist (duniform (elems EU)) n => x \in xs => x \in EU.
proof. 
move => xs_d x_xs. rewrite memE -supp_duniform. 
move: xs_d; case (0 <= n) => Hn; last by rewrite supp_dlist0; smt().
rewrite supp_dlist // => -[? /allP H]; exact: H.
qed.

lemma nth_mapi x1 (s : 'a list) x2 (f : int -> 'a -> 'b) n : 0 <= n && n < size s =>
    nth x2 (mapi f s) n = f n (nth x1 s n).
admitted.

(* variant of [dlist_fu] whose conclusion is a linear pattern *)
lemma dlist_fu_eq (d : 'a distr) (xs : 'a list) n :
   n = size xs => (forall (x : 'a), x \in xs => x \in d) => xs \in dlist d n.
proof. move => ->. exact: dlist_fu. qed.

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
(* establishing the invariant *)
wp.
rnd (mapi (fun j z => if nth false S.ib{2} j then z * inv y else z)) 
    (mapi (fun j z => if nth false S.ib{2} j then z * y else z)).
rnd (mapi (fun i z => if nth false S.ia{2} i then z * inv x else z)) 
    (mapi (fun i z => if nth false S.ia{2} i then z * x else z)).
rnd; rnd; auto => /> ia d_ia ib d_ib. 
split => [a d_a | _ ]. 
  rewrite in_mapiK => //= i z z_a. case (nth false ia i) => // _.
  rewrite invK //. exact: dlist_EU d_a z_a.
split => [a d_a | _ ].
  apply: dlist_uni => //; 1: exact: duniform_uni.
  move: d_a; rewrite supp_dlist ?na_ge0 => -[size_a supp_a].
  apply: dlist_fu_eq; 1: by rewrite size_mapi size_a.
  admit. (* need mapiP or something similar *)
move => a a_d; split => [| ?]. 
  admit. (* almost as above *)
split => [|aK']. 
  rewrite in_mapiK => //= i z z_a. case (nth false ia i) => // _.
  rewrite invK' //. exact: dlist_EU a_d z_a.
split => [b b_d | _ ]. 
  rewrite in_mapiK => //= j z z_b. case (nth false ib j) => // _.
  rewrite invK //. exact: dlist_EU b_d z_b.
split => [b b_d | _]. 
  apply: dlist_uni => //; 1: exact: duniform_uni.
  admit.
move => b b_d; split => [| ?].
  admit.
split => [|_].
  rewrite in_mapiK => //= j z z_b. case (nth false ib j) => // _.
  rewrite invK' //. exact: dlist_EU b_d z_b.
split; first split.
- move => i. case (0 <= i && i < size a) => [i_in|i_out]. 
  + rewrite /nth'. rewrite (nth_mapi witness a) //=.
    case (nth false ia i) => //. rewrite invK' //. admit. 
  + rewrite /nth' !(nth_out false) //= ?(nth_out witness) ?size_mapi //. admit. 
- move => j. case (0 <= j && j < size b) => [j_in|j_out]. 
  + rewrite /nth'. rewrite (nth_mapi witness b) //=.
    case (nth false ib j) => //. rewrite invK' //. admit. 
  + rewrite /nth' !(nth_out false) //= ?(nth_out witness) ?size_mapi //. admit. 
move => _ _. smt().
qed.

lemma S_ia &m gx gy i : 0 <= i /\ i < na =>
    Pr[ GameS(A).main(gx,gy) @ &m : nth' S.ia i ] = pa.
admitted.

lemma S_ib &m gx gy j : 0 <= j /\ j < nb =>
    Pr[ GameS(A).main(gx,gy) @ &m : nth' S.ib j ] = pb.
admitted.

(* we think we can (maybe) prove *)
lemma G'_S &m x y : 
    Pr[ Game(G',A).main() @ &m : G.bad ] <= 
    Pr[ GameS(A).main(exp g x,exp g y) @ &m : exists m i j, (m,i,j) \in S.gs /\ 
        nth' S.ia i && nth' S.ib j => m = exp g (nth' S.a i * nth' S.b j * x * y) ].
admitted.

(* does this follow (easily)? *)
lemma G'_S' &m x y :  
   pa * pb * Pr[ Game(G',A).main() @ &m : G.bad ] <= 
   Pr[ GameS(A).main(exp g x,exp g y) @ &m : 
       exists m i j, (m,i,j) \in S.gs /\ m = exp g (nth' S.a i * nth' S.b j * x * y) ].
admitted.

lemma badG'_cdh &m : 
    Pr[ Game(G',A).main() @ &m : G.bad ] <= p * Pr [ NCDH.Game(B(A)).main() @ &m : res ].
admitted.
