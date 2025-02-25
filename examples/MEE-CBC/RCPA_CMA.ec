(** Encrypt-then-MAC and MAC-then-Encrypt -- Generic Reductions **)
require import AllCore Int FSet Real Distr DProd.
require (*--*) SKE_INDR MACs.

(** We now reason about the security of MtE(E,M) for an
    IND$-CPA secure SKE E and a SUF-CMA secure MAC M whose
    types align                                           **)
theory MtE.
  type mK, eK, ptxt, ctxt, tag.

  (** Tags are completely public... **)
  type leaks.
  op leak: ptxt -> leaks.

  op dC: leaks -> ctxt distr.
  axiom dC_ll l: is_lossless (dC l).

  (** We instantiate the security notions for E and M **)
  clone SKE_INDR as SKEa with
    type eK                   <- eK,
    type ptxt                 <- ptxt * tag,
    type ctxt                 <- ctxt,
    type leaks                <- leaks,
    op   leak (pt:ptxt * tag) <- leak pt.`1,
    op   dC                   <- dC
  proof * by smt.

  clone MACs as MACa with
    type mK   <- mK,
    type msg  <- ptxt,
    type tag  <- tag.

  (** ... and for EtM(E,M) **)
  clone import SKE_INDR as Sec with
    type eK    <- eK * mK,
    type ptxt  <- ptxt,
    type ctxt  <- ctxt,
    type leaks <- leaks,
    op   leak  <- leak,
    op   dC    <- dC
  proof * by smt.

  (** The black-box construction is as follows **)
  module MacThenEncrypt(E:SKEa.Enc_Scheme, M:MACa.MAC_Scheme): Enc_Scheme = {
    proc keygen(): eK * mK = {
      var ek, mk;

      ek <@ E.keygen();
      mk <@ M.keygen();
      return (ek,mk);
    }

    proc enc(k:eK * mK, p:ptxt): ctxt = {
      var ek, mk, c, t;

      (ek,mk) <- k;
      t       <@ M.tag(mk,p);
      c       <@ E.enc(ek,(p,t));
      return c;
    }

    proc dec(k:eK * mK, c:ctxt): ptxt option = {
      var ek, mk, t, b, pt, p';
      var p <- None;

      (ek,mk) <- k;
      pt      <@ E.dec(ek,c);
      if (pt <> None) {
        (p',t) <- oget pt;
        b      <@ M.verify(mk,p',t);
        p      <- if b then Some p' else None;
      }
      return p;
    }
  }.

  (** A useful result for use later on **)
  section Losslessness.
    declare module E <: SKEa.Enc_Scheme.
    declare module M <: MACa.MAC_Scheme.

    lemma MtE_keygen_ll:
      islossless E.keygen =>
      islossless M.keygen =>
      islossless MacThenEncrypt(E,M).keygen.
    proof.
      move=> E_ll M_ll.
      by proc; call M_ll; call E_ll.
    qed.

    lemma MtE_enc_ll:
      islossless E.enc =>
      islossless M.tag =>
      islossless MacThenEncrypt(E,M).enc.
    proof.
      move=> E_ll M_ll.
      by proc; call E_ll; call M_ll; auto.
    qed.

    lemma MtE_dec_ll:
      islossless E.dec =>
      islossless M.verify =>
      islossless MacThenEncrypt(E,M).dec.
    proof.
      move=> E_ll M_ll.
      proc; seq  3: true 1%r 1%r 0%r _ => //=.
        by call E_ll; wp.
        by if=> //=; wp; call M_ll; wp.
    qed.
  end section Losslessness.

  (** We first prove that if E is IND-CPA, then MtE(E,M) is IND-CPA **)
  theory RCPA_WUF_RCPA.
    import RCPA.

    (* The MAC and the CPA adversary against MtE(E,M) are combined
       to construct a CPA adversary againt E                           *)
    module RCPAa(M:MACa.MAC_Scheme, A:RCPA_Adversary, O:SKEa.RCPA.RCPA_Oracles) = {
      var mk: mK

      module Sim : RCPA_Oracles = {
        proc enc(p:ptxt): ctxt = {
          var t;
          var c <- witness;

          t <@ M.tag(mk,p);
          c <@ O.enc(p,t);
          return c;
        }
      }

      proc distinguish(): bool = {
        var b;

        mk <@ M.keygen();
        b  <@ A(Sim).distinguish();
        return b;
      }

    }.

    section RCPA.
      declare module E <: SKEa.Enc_Scheme { RCPA_Wrap, SKEa.RCPA.RCPA_Wrap, RCPAa }.
      declare module M <: MACa.MAC_Scheme { RCPA_Wrap, SKEa.RCPA.RCPA_Wrap, RCPAa, E }.
      declare module A <: RCPA_Adversary  { RCPA_Wrap, SKEa.RCPA.RCPA_Wrap, RCPAa, E, M }.

      lemma RCPA_prob &m:
        Pr[INDR_CPA(MacThenEncrypt(E,M),A).main() @ &m: res]
        = Pr[SKEa.RCPA.INDR_CPA(E,RCPAa(M,A)).main() @ &m: res].
      proof.
        byequiv=> //=.
        proc; inline *.
        wp; call (_:    ={glob E, glob M}
                     /\ RCPA_Wrap.k{1} = (SKEa.RCPA.RCPA_Wrap.k,RCPAa.mk){2}).
          proc; inline *.
          wp=> /=; call (_: true)=> //=.
          wp=> /=; call (_: true)=> //=.
          by auto.
        wp; call (_: true).
        by wp; call (_: true).
      qed.
    end section RCPA.

    (* Adv^{IND$-CPA}_{MacThenEncrypt(E,M)}(A) = Adv^{IND$-CPA}_{E}(RCPAa(A)) *)
    lemma RCPA_preservation (E <: SKEa.Enc_Scheme { RCPA_Wrap, SKEa.RCPA.RCPA_Wrap, RCPAa })
                            (M <: MACa.MAC_Scheme { RCPA_Wrap, SKEa.RCPA.RCPA_Wrap, RCPAa, E })
                            (A <: RCPA_Adversary  { RCPA_Wrap, SKEa.RCPA.RCPA_Wrap, RCPAa, E, M })
                            &m:
      islossless M.keygen =>
      islossless M.tag    =>
      `|Pr[INDR_CPA(MacThenEncrypt(E,M),A).main() @ &m: res]
        - Pr[INDR_CPA(Ideal,A).main() @ &m: res]|
      = `|Pr[SKEa.RCPA.INDR_CPA(E,RCPAa(M,A)).main() @ &m: res]
          - Pr[SKEa.RCPA.INDR_CPA(SKEa.RCPA.Ideal,RCPAa(M,A)).main() @ &m: res]|.
    proof.
      move=> M_keygen_ll M_tag_ll.
      rewrite (RCPA_prob E M A &m) -(RCPA_prob SKEa.RCPA.Ideal M A &m).
      do !congr; byequiv=> //=.
      proc; inline *.
      call (_: true).
        by proc; inline *; auto; call{2} M_tag_ll; auto.
      by wp; call{2} M_keygen_ll; auto.
    qed.
  end RCPA_WUF_RCPA.

  (** We then prove that if E is IND$-CPA and M is SUF-CMA then MacThenEncrypt(E,M) is INT-PTXT **)
  theory RCPA_WUF_PTXT.
    import PTXT.

    (* The SKE and the PTXT adversary against MacThenEncrypt(E,M) are combined
       to construct a CMA adversary againt M                           *)
    module CMAa(E:SKEa.Enc_Scheme, A:PTXT_Adversary, O:MACa.CMA_Oracles) = {
      var ek: eK

      module Sim : PTXT_Oracles = {
        proc enc(p:ptxt): ctxt = {
          var c, t;

          t <@ O.tag(p);
          c <@ E.enc(ek,(p,t));
          return c;
        }

        proc verify(c:ctxt): bool = {
          var t, pt, p;
          var b <- false;

          pt <@ E.dec(ek,c);
          if (pt <> None) {
            (p,t) <- oget pt;
            b     <@ O.verify(p,t);
          }
          return b;
        }
      }

      proc forge(): unit = {
        ek <@ E.keygen();
              A(Sim).forge();
      }
    }.

    section PTXT.
      declare module E <: SKEa.Enc_Scheme { PTXT_Wrap, MACa.WUF_CMA.WUF_Wrap, CMAa }.
      declare module M <: MACa.MAC_Scheme { PTXT_Wrap, MACa.WUF_CMA.WUF_Wrap, CMAa, E }.
      declare module A <: PTXT_Adversary  { PTXT_Wrap, MACa.WUF_CMA.WUF_Wrap, CMAa, E, M }.

      (* Equivalence up to failure requires termination of oracles and adversaries *)
      declare axiom E_keygen_ll: islossless E.keygen.
      declare axiom E_enc_ll   : islossless E.enc.
      declare axiom E_dec_ll   : islossless E.dec.

      declare axiom M_keygen_ll: islossless M.keygen.
      declare axiom M_tag_ll   : islossless M.tag.
      declare axiom M_verify_ll: islossless M.verify.

      declare axiom A_forge_ll (O <: PTXT_Oracles { A }):
        islossless O.enc => islossless O.verify => islossless A(O).forge.

      (* Adv^{INT-PTXT}_{MacThenEncrypt(E,M)}(A) <= Adv^{WUF-CMA}_{M}(CMAa(E,A)) *)
      lemma PTXT_security &m:
        Pr[INT_PTXT(MacThenEncrypt(E,M),A).main() @ &m: res]
        <= Pr[MACa.WUF_CMA.WUF_CMA(M,CMAa(E,A)).main() @ &m: res].
      proof.
        byequiv=> //=.
        proc; inline *.
        call (_: MACa.WUF_CMA.WUF_Wrap.win,
                    ={glob E, glob M}
                 /\ PTXT_Wrap.k{1} = (CMAa.ek,MACa.WUF_CMA.WUF_Wrap.k){2}
                 /\ (forall p, mem PTXT_Wrap.s{1} p <=> mem MACa.WUF_CMA.WUF_Wrap.s{2} p)
                 /\ (PTXT_Wrap.win{1} => MACa.WUF_CMA.WUF_Wrap.win{2})).
          (* adversary is lossless *)
          exact/A_forge_ll.
          (* encryption oracle *)
          (* equivalence *)
          proc; inline *.
          wp=> /=; call (_: true).
          wp=> /=; call (_: true).
          by auto; smt.
          (* lossless after win *)
          by move=> &2 win; proc; wp; call (MtE_enc_ll E M E_enc_ll M_tag_ll).
          (* lossless and preservation of win *)
          move=> &1; proc; inline *.
          wp; call E_enc_ll.
          wp; call M_tag_ll.
          by auto.
          (* decryption oracle *)
          (* equivalence *)
          proc; inline *.
          seq  5  2: (   !MACa.WUF_CMA.WUF_Wrap.win{2}
                      /\ ={glob E, glob M, c, pt}
                      /\ PTXT_Wrap.k{1} = (CMAa.ek,MACa.WUF_CMA.WUF_Wrap.k){2}
                      /\ (forall p, mem PTXT_Wrap.s{1} p <=> mem MACa.WUF_CMA.WUF_Wrap.s{2} p)
                      /\ (PTXT_Wrap.win{1} => MACa.WUF_CMA.WUF_Wrap.win{2})
                      /\ !b{2}
                      /\ k{1} = PTXT_Wrap.k{1}
                      /\ c0{1} = c{1}
                      /\ p0{1} = None
                      /\ (ek,mk){1} = k{1}).
            by call (_: true); auto.
          if=> //=.
            auto; call (_: true); auto=> /> &1 &2 _ /> eq_qs _ /> _.
            by case: (pt{2})=> //= -[p t] r; case: r=> //= _; rewrite eq_qs.
          by auto; smt.
        (* lossless after win *)
        by move=> &2 bad; proc; wp; call (MtE_dec_ll E M E_dec_ll M_verify_ll).
        (* lossless and preservation of win *)
        move=> &1; proc; seq  2: true 1%r 1%r 0%r _ (MACa.WUF_CMA.WUF_Wrap.win) => //=.
          by inline *; wp; call (_: true); auto.
          by inline *; wp; call E_dec_ll; auto.
          if=> /=.
            by inline *; auto; call M_verify_ll; auto; smt.
          done.
        (* back to the experiment *)
        swap{2} 4 -3.
        wp; call (_: true).
        wp; call (_: true).
        by auto; smt.
      qed.
    end section PTXT.
  end RCPA_WUF_PTXT.
end MtE.

(** We now reason about the security of EtM(E,M) for an
    IND$-CPA secure SKE E and a SUF-CMA secure MAC M whose
    types align                                           **)
theory EtM.
  type mK, eK, ptxt, ctxt, tag.

  type leaks.
  op leak: ptxt -> leaks.

  op dC: leaks -> ctxt distr.
  axiom dC_ll l: is_lossless (dC l).

  (** We instantiate the security notions for E and M **)
  clone SKE_INDR as SKEa with
    type eK    <- eK,
    type ptxt  <- ptxt,
    type ctxt  <- ctxt,
    type leaks <- leaks,
    op   leak  <- leak,
    op   dC    <- dC
  proof * by smt.

  clone MACs as MACa with
    type mK   <- mK,
    type msg  <- ctxt,
    type tag  <- tag.

  (** ... and for EtM(E,M) **)
  clone import SKE_INDR as Sec with
    type eK              <- eK * mK,
    type ptxt            <- ptxt,
    type ctxt            <- ctxt * tag,
    type leaks           <- leaks,
    op   leak            <- leak,
    op   dC    (l:leaks) <- (dC l) `*` (MUnit.dunit witness<:tag>)
  proof * by smt.

  (** The black-box construction is as follows **)
  module EtM(E:SKEa.Enc_Scheme, M:MACa.MAC_Scheme): Enc_Scheme = {
    proc keygen(): eK * mK = {
      var ek, mk;

      ek <@ E.keygen();
      mk <@ M.keygen();
      return (ek,mk);
    }

    proc enc(k:eK * mK, p:ptxt): ctxt * tag = {
      var ek, mk, c, t;

      (ek,mk) <- k;
      c       <@ E.enc(ek,p);
      t       <@ M.tag(mk,c);
      return (c,t);
    }

    proc dec(k:eK * mK, ct:ctxt * tag): ptxt option = {
      var ek, mk, c, t, b;
      var p <- None;

      (ek,mk) <- k;
      (c ,t)  <- ct;
      b       <@ M.verify(mk,c,t);
      if (b) { p <@ E.dec(ek,c); }
      return p;
    }
  }.

  (** A useful result for use later on **)
  section Losslessness.
    declare module E <: SKEa.Enc_Scheme.
    declare module M <: MACa.MAC_Scheme.

    lemma EtM_keygen_ll:
      islossless E.keygen =>
      islossless M.keygen =>
      islossless EtM(E,M).keygen.
    proof.
      move=> E_ll M_ll.
      by proc; call M_ll; call E_ll.
    qed.

    lemma EtM_enc_ll:
      islossless E.enc =>
      islossless M.tag =>
      islossless EtM(E,M).enc.
    proof.
      move=> E_ll M_ll.
      by proc; call M_ll; call E_ll; wp.
    qed.

    lemma EtM_dec_ll:
      islossless E.dec =>
      islossless M.verify =>
      islossless EtM(E,M).dec.
    proof.
      move=> E_ll M_ll.
      proc; seq  4: true 1%r 1%r 0%r _ => //=.
        by call M_ll; wp.
        by if=> //=; call E_ll.
    qed.
  end section Losslessness.

  (** We first prove that if E is IND$-CPA, then EtM(E,M) is IND$-CPA **)
  theory RCPA_SUF_RCPA.
    import RCPA.

    (* The MAC and the CPA adversary against EtM(E,M) are combined
       to construct a CPA adversary againt E                           *)
    module RCPAa(M:MACa.MAC_Scheme, A:RCPA_Adversary, O:SKEa.RCPA.RCPA_Oracles) = {
      var mk: mK

      module Sim : RCPA_Oracles = {
        proc enc(p:ptxt): ctxt * tag = {
          var c, t;

          c  <@ O.enc(p);
          t  <@ M.tag(mk,c);
          return (c,t);
        }
      }

      proc distinguish(): bool = {
        var b;

        mk <@ M.keygen();
        b  <@ A(Sim).distinguish();
        return b;
      }

    }.

    section RCPA.
      declare module E <: SKEa.Enc_Scheme { RCPA_Wrap, SKEa.RCPA.RCPA_Wrap, RCPAa }.
      declare module M <: MACa.MAC_Scheme { RCPA_Wrap, SKEa.RCPA.RCPA_Wrap, RCPAa, E }.
      declare module A <: RCPA_Adversary  { RCPA_Wrap, SKEa.RCPA.RCPA_Wrap, RCPAa, E, M }.

      local lemma RCPA_prob &m:
        Pr[INDR_CPA(EtM(E,M),A).main() @ &m: res]
        = Pr[SKEa.RCPA.INDR_CPA(E,RCPAa(M,A)).main() @ &m: res].
      proof.
        byequiv=> //=.
        proc; inline *.
        wp; call (_:    ={glob E, glob M}
                     /\ RCPA_Wrap.k{1} = (SKEa.RCPA.RCPA_Wrap.k,RCPAa.mk){2}).
          proc; inline *.
          wp; call (_: true).
          wp; call (_: true).
          by auto.
        wp; call (_: true).
        by wp; call (_: true).
      qed.

      (* Adv^{IND$-CPA}_{EtM(E,M)}(A) = Adv^{IND$-CPA}_{E}(RCPAa(A)) *)
      lemma RCPA_preservation &m:
        2%r * Pr[INDR_CPA(EtM(E,M),A).main() @ &m: res] - 1%r
        = 2%r * Pr[SKEa.RCPA.INDR_CPA(E,RCPAa(M,A)).main() @ &m: res] - 1%r.
      proof. by rewrite (RCPA_prob &m). qed.
    end section RCPA.
  end RCPA_SUF_RCPA.

  (** We then prove that if E is IND$-CPA and M is SUF-CMA then EtM(E,M) is INT-CTXT **)
  theory RCPA_SUF_CTXT.
    import CTXT.

    (* The SKE and the CTXT adversary against EtM(E,M) are combined
       to construct a CMA adversary againt M                           *)
    module CMAa(E:SKEa.Enc_Scheme, A:CTXT_Adversary, O:MACa.CMA_Oracles) = {
      var ek: eK

      module Sim : CTXT_Oracles = {
        proc enc(p:ptxt): ctxt * tag = {
          var c, t;

          c <@ E.enc(ek,p);
          t <@ O.tag(c);
          return (c,t);
        }

        proc verify(ct:ctxt * tag): bool = {
          var c, t, b;

          (c,t) <- ct;
          b     <@ O.verify(c,t);
          return b;
        }
      }

      proc forge(): unit = {
        ek <@ E.keygen();
              A(Sim).forge();
      }
    }.

    section CTXT.
      declare module E <: SKEa.Enc_Scheme { CTXT_Wrap, MACa.SUF_CMA.SUF_Wrap, CMAa }.
      declare module M <: MACa.MAC_Scheme { CTXT_Wrap, MACa.SUF_CMA.SUF_Wrap, CMAa, E }.
      declare module A <: CTXT_Adversary  { CTXT_Wrap, MACa.SUF_CMA.SUF_Wrap, CMAa, E, M }.

      (* Equivalence up to failure requires termination of oracles and adversaries *)
      declare axiom E_keygen_ll: islossless E.keygen.
      declare axiom E_enc_ll   : islossless E.enc.
      declare axiom E_dec_ll   : islossless E.dec.

      declare axiom M_keygen_ll: islossless M.keygen.
      declare axiom M_tag_ll   : islossless M.tag.
      declare axiom M_verify_ll: islossless M.verify.

      declare axiom A_forge_ll (O <: CTXT_Oracles { A }):
        islossless O.enc => islossless O.verify => islossless A(O).forge.

      (* In addition, this result requires that the encryption scheme is correct,
         and that the decryption algorithm is deterministic and stateless *)
      declare axiom dec_op: exists dec,
           (forall ge _k _c,
              hoare [E.dec: (glob E) = ge /\ k = _k /\ c = _c
                        ==> (glob E) = ge /\ res = dec _k _c])
        /\ (forall _k _p,
              hoare [E.enc: k = _k /\ p = _p ==> dec _k res = Some _p]).

(*    local choice...
      choice dec with dec_op.

      local hoare dec_sem ge _k _c:
        E.dec: (glob E) = ge /\ k = _k /\ c = _c
           ==> (glob E) = ge /\ res = dec _k _c.
      proof. have [h _]:= decE; exact/(h ge _k _c). qed.

      local hoare E_correct _k _p:
        E.enc: k = _k /\ p = _p ==> dec _k res = Some _p.
      proof. have [_ h]:= decE; exact/(h _k _p). qed.

      (* Useful consequences of these facts *)
      local equiv enc_eq _k _p: E.enc ~ E.enc:
            ={glob E, k, p} /\ k{1} = _k /\ p{1} = _p
        ==> ={glob E, res} /\ dec _k res{1} = Some _p.
      proof.
        conseq* (_: ={glob E, k, p} ==> ={glob E, res}) (E_correct _k _p) _.
        by proc true.
      qed.

      local phoare dec_ph ge _k _c:
        [E.dec: (glob E) = ge /\ k = _k /\ c = _c
            ==> (glob E) = ge /\ res = dec _k _c] =1%r.
      proof. by conseq* E_dec_ll (dec_sem ge _k _c). qed.
*)

      (* Adv^{CTXT}_{EtM(E,M)}(A) <= Adv^{SUF-CMA}_{M}(CMAa(E,A)) *)
      lemma CTXT_security &m:
        Pr[INT_CTXT(EtM(E,M),A).main() @ &m: res]
        <= Pr[MACa.SUF_CMA.SUF_CMA(M,CMAa(E,A)).main() @ &m: res].
      proof.
        have [dec [dec_sem enc_sem]]:= dec_op.
        byequiv=> //=.
        proc; inline *.
        call (_: MACa.SUF_CMA.SUF_Wrap.win,
                    ={glob E, glob M}
                 /\ CTXT_Wrap.k{1} = (CMAa.ek,MACa.SUF_CMA.SUF_Wrap.k){2}
                 /\ (forall p, mem CTXT_Wrap.s{1} p <=> mem MACa.SUF_CMA.SUF_Wrap.s{2} p)
                 /\ (forall c t, mem CTXT_Wrap.s{1} (c,t) => dec CMAa.ek{2} c <> None)
                 /\ (CTXT_Wrap.win{1} => MACa.SUF_CMA.SUF_Wrap.win{2})).
          (* adversary is lossless *)
          exact/A_forge_ll.
          (* encryption oracle *)
          (* equivalence *)
          proc; inline *.
          wp; call (_: true).
          wp; sp. exists* ek{1}, p0{1}; elim* => _k _p.
          call (_: ={glob E, k, p} /\ k{1} = _k /\ p{1} = _p ==> ={glob E, res} /\ dec _k res{1} = Some _p).
            by conseq (_: ={glob E, k, p} ==> ={glob E, res}) (enc_sem _k _p); proc true.
          by skip; smt.
          (* lossless after win *)
          by move=> &2 win; proc; wp; call (EtM_enc_ll E M E_enc_ll M_tag_ll).
          (* lossless and preservation of win *)
          move=> &1; proc; inline *.
          wp; call M_tag_ll.
          by wp; call E_enc_ll.
          (* decryption oracle *)
          (* equivalence *)
          proc; inline *.
          seq  6  4: (   !MACa.SUF_CMA.SUF_Wrap.win{2}
                      /\ ={glob E, glob M}
                      /\ b{1} = b0{2}
                      /\ c{1} = ct{2}
                      /\ CTXT_Wrap.k{1} = (CMAa.ek,MACa.SUF_CMA.SUF_Wrap.k){2}
                      /\ (forall p, mem CTXT_Wrap.s{1} p <=> mem MACa.SUF_CMA.SUF_Wrap.s{2} p)
                      /\ (forall c t, mem CTXT_Wrap.s{1} (c,t) => dec CMAa.ek{2} c <> None)
                      /\ (CTXT_Wrap.win{1} => MACa.SUF_CMA.SUF_Wrap.win{2})
                      /\ k{1}  = CTXT_Wrap.k{1}
                      /\ ct{1} = c{1}
                      /\ c{2}  = ct{2}.`1
                      /\ t{2}  = ct{2}.`2
                      /\ p0{1} = None
                      /\ m{2}  = c{2}
                      /\ ek{1} = k{1}.`1
                      /\ mk{1} = k{1}.`2
                      /\ t0{2} = t{2}
                      /\ c0{1} = ct{1}.`1
                      /\ t{1}  = ct{1}.`2).
            by wp; call (_: true); auto.
          if{1}.
            wp. exists* (glob E){1}, ek{1}, c0{1}; elim* => ge _k _c.
            call{1} (_:     (glob E) = ge /\ k = _k /\ c = _c
                        ==> (glob E) = ge /\ res = dec _k _c).
              by conseq (E_dec_ll) (dec_sem ge _k _c).
            by skip; smt.
          by auto; smt.
        (* lossless after win *)
        by move=> &2 bad; proc; wp; call (EtM_dec_ll E M E_dec_ll M_verify_ll).
        (* lossless and preservation of win *)
        move=> &1; proc; seq  2: true 1%r 1%r 0%r _ (MACa.SUF_CMA.SUF_Wrap.win) => //=.
          by inline *; wp; call (_: true); auto; smt.
          by inline *; wp; call M_verify_ll; auto.
        (* back to the experiment *)
        swap{2} 4 -3.
        wp; call (_: true).
        by wp; call (_: true); skip; smt.
      qed.
    end section CTXT.
  end RCPA_SUF_CTXT.
end EtM.
