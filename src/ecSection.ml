(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcPath
open EcTypes
open EcDecl
open EcModules
open EcTheory
open EcFol

module Sid  = EcIdent.Sid
module Mid  = EcIdent.Mid
module MSym = EcSymbols.Msym

(* -------------------------------------------------------------------- *)
exception SectionError of string

let pp_section_error fmt exn =
  match exn with
  | SectionError s ->
      Format.fprintf fmt "%s" s

  | _ -> raise exn

let _ = EcPException.register pp_section_error

let hierror fmt =
  let buf  = Buffer.create 127 in
  let bfmt = Format.formatter_of_buffer buf in

  Format.kfprintf
    (fun _ ->
      Format.pp_print_flush bfmt ();
      raise (SectionError (Buffer.contents buf)))
    bfmt fmt

(* -------------------------------------------------------------------- *)
type cbarg = [
  | `Type       of path
  | `Op         of path
  | `Ax         of path
  | `Module     of mpath
  | `ModuleType of path

]

type cb = cbarg -> unit

(* -------------------------------------------------------------------- *)
let rec on_ty (cb : cb) (ty : ty) =
  match ty.ty_node with
  | Tunivar _        -> ()
  | Tvar    _        -> ()
  | Tglob mp         -> cb (`Module mp)
  | Ttuple tys       -> List.iter (on_ty cb) tys
  | Tconstr (p, tys) -> cb (`Type p); List.iter (on_ty cb) tys
  | Tfun (ty1, ty2)  -> List.iter (on_ty cb) [ty1; ty2]

let on_pv (cb : cb) (pv : prog_var) =
  cb (`Module pv.pv_name.x_top)

let on_lp (cb : cb) (lp : lpattern) =
  match lp with
  | LSymbol (_, ty) -> on_ty cb ty
  | LTuple  xs      -> List.iter (fun (_, ty) -> on_ty cb ty) xs
  | LRecord (_, xs) -> List.iter (on_ty cb |- snd) xs

let on_binding (cb : cb) ((_, ty) : (EcIdent.t * ty)) =
  on_ty cb ty

let on_bindings (cb : cb) (bds : (EcIdent.t * ty) list) =
  List.iter (on_binding cb) bds

let rec on_expr (cb : cb) (e : expr) =
  let cbrec = on_expr cb in

  let rec fornode () =
    match e.e_node with
    | Eint   _            -> ()
    | Elocal _            -> ()
    | Equant (_, bds, e)  -> on_bindings cb bds; cbrec e
    | Evar   pv           -> on_pv cb pv
    | Elet   (lp, e1, e2) -> on_lp cb lp; List.iter cbrec [e1; e2]
    | Etuple es           -> List.iter cbrec es
    | Eop    (p, tys)     -> cb (`Op p); List.iter (on_ty cb) tys
    | Eapp   (e, es)      -> List.iter cbrec (e :: es)
    | Eif    (c, e1, e2)  -> List.iter cbrec [c; e1; e2]
    | Ematch (e, es, ty)  -> on_ty cb ty; List.iter cbrec (e :: es)
    | Eproj  (e, _)       -> cbrec e

  in on_ty cb e.e_ty; fornode ()

let on_lv (cb : cb) (lv : lvalue) =
  let for1 (pv, ty) = on_pv cb pv; on_ty cb ty in

    match lv with
    | LvVar   pv  -> for1 pv
    | LvTuple pvs -> List.iter for1 pvs

let rec on_instr (cb : cb) (i : instr)=
  match i.i_node with
  | Srnd (lv, e) | Sasgn (lv, e) ->
      on_lv cb lv;
      on_expr cb e

  | Sassert e ->
      on_expr cb e

  | Scall (lv, f, args) ->
      lv |> oiter (on_lv cb);
      cb (`Module f.x_top);
      List.iter (on_expr cb) args

  | Sif (e, s1, s2) ->
      on_expr cb e;
      List.iter (on_stmt cb) [s1; s2]

  | Swhile (e, s) ->
      on_expr cb e;
      on_stmt cb s

  | Sabstract _ -> ()

and on_stmt (cb : cb) (s : stmt) =
  List.iter (on_instr cb) s.s_node

let on_lcmem (cb : cb) m =
    cb (`Module (EcMemory.lmt_xpath m).x_top);
    Msym.iter (fun _ (_, ty) -> on_ty cb ty) (EcMemory.lmt_bindings m)

let on_memenv (cb : cb) (m : EcMemory.memenv) =
  match snd m with
  | None    -> ()
  | Some lm -> on_lcmem cb lm

let rec on_modty (cb : cb) mty =
  cb (`ModuleType mty.mt_name);
  List.iter (fun (_, mty) -> on_modty cb mty) mty.mt_params;
  List.iter (fun m -> cb (`Module m)) mty.mt_args

let on_gbinding (cb : cb) (b : gty) =
  match b with
  | EcFol.GTty ty ->
      on_ty cb ty
  | EcFol.GTmodty (mty, (rx, r)) ->
      on_modty cb mty;
      Sx.iter (fun x -> cb (`Module x.x_top)) rx;
      Sm.iter (fun x -> cb (`Module x)) r
  | EcFol.GTmem None->
      ()
  | EcFol.GTmem (Some m) ->
      on_lcmem cb m

let on_gbindings (cb : cb) (b : (EcIdent.t * gty) list) =
  List.iter (fun (_, b) -> on_gbinding cb b) b

let rec on_form (cb : cb) (f : EcFol.form) =
  let cbrec = on_form cb in

  let rec fornode () =
    match f.EcFol.f_node with
    | EcFol.Fint      _            -> ()
    | EcFol.Flocal    _            -> ()
    | EcFol.Fquant    (_, b, f)    -> on_gbindings cb b; cbrec f
    | EcFol.Fif       (f1, f2, f3) -> List.iter cbrec [f1; f2; f3]
    | EcFol.Fmatch    (b, fs, ty)  -> on_ty cb ty; List.iter cbrec (b :: fs)
    | EcFol.Flet      (lp, f1, f2) -> on_lp cb lp; List.iter cbrec [f1; f2]
    | EcFol.Fop       (p, tys)     -> cb (`Op p); List.iter (on_ty cb) tys
    | EcFol.Fapp      (f, fs)      -> List.iter cbrec (f :: fs)
    | EcFol.Ftuple    fs           -> List.iter cbrec fs
    | EcFol.Fproj     (f, _)       -> cbrec f
    | EcFol.Fpvar     (pv, _)      -> on_pv  cb pv
    | EcFol.Fglob     (mp, _)      -> cb (`Module mp)
    | EcFol.FhoareF   hf           -> on_hf  cb hf
    | EcFol.FhoareS   hs           -> on_hs  cb hs
    | EcFol.FequivF   ef           -> on_ef  cb ef
    | EcFol.FequivS   es           -> on_es  cb es
    | EcFol.FeagerF   eg           -> on_eg  cb eg
    | EcFol.FbdHoareS bhs          -> on_bhs cb bhs
    | EcFol.FbdHoareF bhf          -> on_bhf cb bhf
    | EcFol.Fpr       pr           -> on_pr  cb pr

  and on_hf cb hf =
    on_form cb hf.EcFol.hf_pr;
    on_form cb hf.EcFol.hf_po;
    cb (`Module hf.EcFol.hf_f.x_top)

  and on_hs cb hs =
    on_form cb hs.EcFol.hs_pr;
    on_form cb hs.EcFol.hs_po;
    on_stmt cb hs.EcFol.hs_s;
    on_memenv cb hs.EcFol.hs_m

  and on_ef cb ef =
    on_form cb ef.EcFol.ef_pr;
    on_form cb ef.EcFol.ef_po;
    cb (`Module ef.EcFol.ef_fl.x_top);
    cb (`Module ef.EcFol.ef_fr.x_top)

  and on_es cb es =
    on_form cb es.EcFol.es_pr;
    on_form cb es.EcFol.es_po;
    on_stmt cb es.EcFol.es_sl;
    on_stmt cb es.EcFol.es_sr;
    on_memenv cb es.EcFol.es_ml;
    on_memenv cb es.EcFol.es_mr

  and on_eg cb eg =
    on_form cb eg.EcFol.eg_pr;
    on_form cb eg.EcFol.eg_po;
    cb (`Module eg.EcFol.eg_fl.x_top);
    cb (`Module eg.EcFol.eg_fr.x_top);
    on_stmt cb eg.EcFol.eg_sl;
    on_stmt cb eg.EcFol.eg_sr;

  and on_bhf cb bhf =
    on_form cb bhf.EcFol.bhf_pr;
    on_form cb bhf.EcFol.bhf_po;
    on_form cb bhf.EcFol.bhf_bd;
    cb (`Module bhf.EcFol.bhf_f.x_top)

  and on_bhs cb bhs =
    on_form cb bhs.EcFol.bhs_pr;
    on_form cb bhs.EcFol.bhs_po;
    on_form cb bhs.EcFol.bhs_bd;
    on_stmt cb bhs.EcFol.bhs_s;
    on_memenv cb bhs.EcFol.bhs_m

  and on_pr cb pr =
    cb (`Module pr.EcFol.pr_fun.x_top);
    List.iter (on_form cb) [pr.EcFol.pr_event; pr.EcFol.pr_args]

  in
    on_ty cb f.EcFol.f_ty; fornode ()

let rec on_module (cb : cb) (me : module_expr) =
  match me.me_body with
  | ME_Alias (_, mp)  -> cb (`Module mp)
  | ME_Structure st   -> on_mstruct cb st
  | ME_Decl (mty, sm) -> on_mdecl cb (mty, sm)

and on_mdecl (cb : cb) ((mty, (rx, r)) : module_type * mod_restr) =
  on_modty cb mty;
  Sx.iter (fun x -> cb (`Module x.x_top)) rx;
  Sm.iter (fun x -> cb (`Module x)) r

and on_mstruct (cb : cb) (st : module_structure) =
  List.iter (on_mpath_mstruct1 cb) st.ms_body

and on_mpath_mstruct1 (cb : cb) (item : module_item) =
  match item with
  | MI_Module   me -> on_module cb me
  | MI_Variable x  -> on_ty cb x.v_type
  | MI_Function f  -> on_fun cb f

and on_fun (cb : cb) (fun_ : function_) =
  on_fun_sig  cb fun_.f_sig;
  on_fun_body cb fun_.f_def

and on_fun_sig (cb : cb) (fsig : funsig) =
  on_ty cb fsig.fs_arg;
  on_ty cb fsig.fs_ret

and on_fun_body (cb : cb) (fbody : function_body) =
  match fbody with
  | FBalias xp -> cb (`Module xp.x_top)
  | FBdef fdef -> on_fun_def cb fdef
  | FBabs oi   -> on_fun_oi  cb oi

and on_fun_def (cb : cb) (fdef : function_def) =
  List.iter (fun v -> on_ty cb v.v_type) fdef.f_locals;
  on_stmt cb fdef.f_body;
  fdef.f_ret |> oiter (on_expr cb);
  on_uses cb fdef.f_uses

and on_uses (cb : cb) (uses : uses) =
  List.iter (fun x -> cb (`Module x.x_top)) uses.us_calls;
  Sx.iter   (fun x -> cb (`Module x.x_top)) uses.us_reads;
  Sx.iter   (fun x -> cb (`Module x.x_top)) uses.us_writes

and on_fun_oi (cb : cb) (oi : oracle_info) =
  List.iter (fun x -> cb (`Module x.x_top)) oi.oi_calls

(* -------------------------------------------------------------------- *)
let on_tydecl (env:EcEnv.env) (cb : EcEnv.env -> cb) name (tyd : tydecl) =
  match tyd.tyd_type with
  | `Concrete ty -> on_ty (cb env) ty
  | `Abstract _  -> ()

  | `Record (f, fds) ->
      let env = EcEnv.Ty.bind name tyd env in
      let cb = cb env in
      on_form cb f;
      List.iter (on_ty cb |- snd) fds

  | `Datatype dt ->
     let env = EcEnv.Ty.bind name tyd env in
     let cb  = cb env in
     List.iter (List.iter (on_ty cb) |- snd) dt.tydt_ctors;
     List.iter (on_form cb) [dt.tydt_schelim; dt.tydt_schcase]

(* -------------------------------------------------------------------- *)
let on_opdecl (env:EcEnv.env) (cb : EcEnv.env -> cb) name (opdecl : operator) =
  let for_kind () =
    match opdecl.op_kind with
   | OB_pred None -> ()

   | OB_pred (Some (PR_Plain f)) ->
      on_form (cb env) f

   | OB_pred (Some (PR_Ind pri)) ->
     let cb = cb env in
     on_bindings cb pri.pri_args;
     List.iter (fun ctor ->
         on_gbindings cb ctor.prc_bds;
         List.iter (on_form cb) ctor.prc_spec)
       pri.pri_ctors

   | OB_nott nott ->
     let cb = cb env in
     List.iter (on_ty cb |- snd) nott.ont_args;
     on_ty cb nott.ont_resty;
     on_expr cb nott.ont_body

   | OB_oper None   -> ()
   | OB_oper Some b ->
     match b with
     | OP_Constr _ | OP_Record _ | OP_Proj   _ -> assert false
     | OP_TC -> assert false
     | OP_Plain  (e, _) -> on_expr (cb env) e
     | OP_Fix    f ->
       let env =
         EcEnv.Op.bind name { opdecl with op_kind = OB_oper None } env in
       let cb = cb env in
       let rec on_mpath_branches br =
         match br with
         | OPB_Leaf (bds, e) ->
           List.iter (on_bindings cb) bds;
           on_expr cb e
         | OPB_Branch br ->
           Parray.iter on_mpath_branch br

       and on_mpath_branch br =
         on_mpath_branches br.opb_sub

       in on_mpath_branches f.opf_branches

  in on_ty (cb env) opdecl.op_ty; for_kind ()

(* -------------------------------------------------------------------- *)
let on_axiom (cb : cb) (ax : axiom) =
  on_form cb ax.ax_spec

(* -------------------------------------------------------------------- *)
let on_modsig (cb:cb) (ms:module_sig) =
  List.iter (fun (_,mt) -> on_modty cb mt) ms.mis_params;
  List.iter (fun (Tys_function(fs,_)) ->
      on_ty cb fs.fs_arg;
      oiter (List.iter (fun x -> on_ty cb x.v_type)) fs.fs_anames;
      on_ty cb fs.fs_ret;) ms.mis_body

(* -------------------------------------------------------------------- *)

type sc_name =
  | Th of symbol
  | Sc of symbol option
  | Top

type scenv = {
  sc_env     : EcEnv.env;
  sc_top     : scenv option;
  sc_loca    : is_local;
  sc_name    : sc_name;
  sc_insec   : bool;
  sc_items   : sc_items;
}

and sc_item =
  | SC_th_item  of EcTheory.theory_item
  | SC_decl_mod of EcIdent.t * module_type * mod_restr

and sc_items =
  sc_item list

let initial env =
  { sc_env     = env;
    sc_top     = None;
    sc_loca    = `Global;
    sc_name    = Top;
    sc_insec   = false;
    sc_items   = [];
  }

let env scenv = scenv.sc_env

(* -------------------------------------------------------------------- *)

let is_declared (env : EcEnv.env) (who : cbarg) =
  match who with
  | `Type p -> (EcEnv.Ty.by_path p env).tyd_loca = `Declare
  | `Op   p -> (EcEnv.Op.by_path p env).op_loca  = `Declare
  | `Ax p   -> (EcEnv.Ax.by_path p env).ax_loca  = `Declare
  | `ModuleType _ -> false
  | `Module    mp ->
    begin match mp.m_top with
    | `Local id   -> EcEnv.Mod.is_declared id env
    | `Concrete _ -> false
    end


let is_local (env : EcEnv.env) (who : cbarg) =
  match who with
  | `Type       p -> (EcEnv.Ty.by_path p env).tyd_loca = `Local
  | `Op         p -> (EcEnv.Op.by_path p env).op_loca  = `Local
  | `Ax         p -> (EcEnv.Ax.by_path p env).ax_loca  = `Local
  | `Module mp    ->
    begin match EcEnv.Mod.by_mpath_opt mp env with
    | Some (_, lc) -> lc = Some `Local
     (* it this case it should be a quantified module *)
    | None         -> false
    end
  | `ModuleType p -> (EcEnv.ModTy.by_path p env).tms_loca = `Local

(* -------------------------------------------------------------------- *)
type to_clear =
  { lc_theory    : Sp.t;
    lc_axioms    : Sp.t;
    lc_baserw    : Sp.t;
  }

type to_gen = {
    tg_env    : EcEnv.env;
    tg_params  : (EcIdent.t * Sp.t) list;
    tg_binds  : bind list;
    tg_subst : EcSubst.subst;
    tg_clear : to_clear;
  }

and bind =
  | Binding of binding
  | Imply    of form

let empty_locals =
  { lc_theory    = Sp.empty;
    lc_axioms    = Sp.empty;
    lc_baserw    = Sp.empty;
  }

let add_clear to_gen who =
  let tg_clear = to_gen.tg_clear in
  let tg_clear =
    match who with
    | `Th         p -> {tg_clear with lc_theory = Sp.add p tg_clear.lc_theory }
    | `Ax         p -> {tg_clear with lc_axioms = Sp.add p tg_clear.lc_axioms }
    | `Baserw     p -> {tg_clear with lc_baserw = Sp.add p tg_clear.lc_baserw } in
  { to_gen with tg_clear }

let add_bind binds bd = binds @ [Binding bd]
let add_imp binds f   = binds @ [Imply f]


let to_clear to_gen who =
  match who with
  | `Th p -> Sp.mem p to_gen.tg_clear.lc_theory
  | `Ax p -> Sp.mem p to_gen.tg_clear.lc_axioms
  | `Baserw p -> Sp.mem p to_gen.tg_clear.lc_baserw

let to_keep to_gen who = not (to_clear to_gen who)

let generalize_type to_gen ty =
  EcSubst.subst_ty to_gen.tg_subst ty

let add_declared_mod to_gen id modty restr =
  { to_gen with
    tg_binds  = add_bind to_gen.tg_binds (id, gtmodty modty restr);
    tg_subst  = EcSubst.add_module to_gen.tg_subst id (mpath_abs id [])
  }

let add_declared_ty to_gen path tydecl =
  assert (
      tydecl.tyd_params = [] &&
      match tydecl.tyd_type with
      | `Abstract _ -> true
      | _ -> false );

  let name = "'" ^ basename path in
  let id = EcIdent.create name in
  { to_gen with
    tg_params = to_gen.tg_params @ [id, Sp.empty];
    tg_subst  = EcSubst.add_tydef to_gen.tg_subst path ([], tvar id);
  }

let add_declared_op to_gen path opdecl =
  assert (
      opdecl.op_tparams = [] &&
      match opdecl.op_kind with
      | OB_oper None | OB_pred None -> true
      | _ -> false);
  let name = basename path in
  let id = EcIdent.create name in
  let ty = generalize_type to_gen opdecl.op_ty in
  {
    to_gen with
    tg_binds = add_bind to_gen.tg_binds (id, gtty ty);
    tg_subst =
      match opdecl.op_kind with
      | OB_oper _ -> EcSubst.add_opdef to_gen.tg_subst path ([], e_local id ty)
      | OB_pred _ ->  EcSubst.add_pddef to_gen.tg_subst path ([], f_local id ty)
      | _ -> assert false }

let tydecl_fv tyd =
  let fv =
    match tyd.tyd_type with
    | `Concrete ty -> ty.ty_fv
    | `Abstract _ -> Mid.empty
    | `Datatype tydt ->
      List.fold_left (fun fv (_, l) ->
        List.fold_left (fun fv ty ->
            EcIdent.fv_union fv ty.ty_fv) fv l) Mid.empty tydt.tydt_ctors
    | `Record (_f, l) ->
      List.fold_left (fun fv (_, ty) ->
          EcIdent.fv_union fv ty.ty_fv) Mid.empty l in
  List.fold_left (fun fv (id, _) -> Mid.remove id fv) fv tyd.tyd_params

let op_body_fv body ty =
  let fv = ty.ty_fv in
  match body with
  | OP_Plain (e, _) -> EcIdent.fv_union fv e.e_fv
  | OP_Constr _ | OP_Record _ | OP_Proj _ | OP_TC -> fv
  | OP_Fix opfix ->
    let fv =
      List.fold_left (fun fv (_, ty) -> EcIdent.fv_union fv ty.ty_fv)
        fv opfix.opf_args in
    let fv = EcIdent.fv_union fv opfix.opf_resty.ty_fv in
    let rec fv_branches fv = function
      | OPB_Leaf (l, e) ->
        let fv = EcIdent.fv_union fv e.e_fv in
        List.fold_left (fun fv l ->
            List.fold_left (fun fv (_, ty) ->
                EcIdent.fv_union fv ty.ty_fv) fv l) fv l
      | OPB_Branch p ->
        Parray.fold_left (fun fv ob -> fv_branches fv ob.opb_sub) fv p in
    fv_branches fv opfix.opf_branches

let pr_body_fv body ty =
  let fv = ty.ty_fv in
  match body with
  | PR_Plain f -> EcIdent.fv_union fv f.f_fv
  | PR_Ind pri ->
    let fv =
      List.fold_left (fun fv (_, ty) -> EcIdent.fv_union fv ty.ty_fv)
        fv pri.pri_args in
    let fv_prctor fv ctor =
      let fv1 =
        List.fold_left (fun fv f -> EcIdent.fv_union fv f.f_fv)
          Mid.empty ctor.prc_spec in
      let fv1 = List.fold_left (fun fv (id, gty) ->
          EcIdent.fv_union (Mid.remove id fv) (gty_fv gty)) fv1 ctor.prc_bds in
      EcIdent.fv_union fv fv1 in
    List.fold_left fv_prctor fv pri.pri_ctors

let notation_fv nota =
  let fv = EcIdent.fv_union nota.ont_body.e_fv nota.ont_resty.ty_fv in
  List.fold_left (fun fv (id,ty) ->
      EcIdent.fv_union (Mid.remove id fv) ty.ty_fv) fv nota.ont_args

let generalize_extra_ty to_gen fv =
  List.filter (fun (id,_) -> Mid.mem id fv) to_gen.tg_params

let rec generalize_extra_args binds fv =
  match binds with
  | [] -> []
  | Binding (id, gt) :: binds ->
    let args = generalize_extra_args binds fv in
    if Mid.mem id fv then
      match gt with
      | GTty ty -> (id, ty) :: args
      | GTmodty  _ -> assert false
      | GTmem _    -> assert false
    else args
  | Imply _ :: binds -> generalize_extra_args binds fv

let rec generalize_extra_forall ~imply binds f =
  match binds with
  | [] -> f
  | Binding (id,gt) :: binds ->
    let f = generalize_extra_forall ~imply binds f in
    if Mid.mem id f.f_fv then
      f_forall [id,gt] f
    else f
  | Imply f1 :: binds ->
    let f = generalize_extra_forall ~imply binds f in
    if imply then f_imp f1 f else f

let generalize_tydecl to_gen prefix (name, tydecl) =
  let path = pqname prefix name in
  match tydecl.tyd_loca with
  | `Local -> to_gen, None
  | `Global ->
    let tydecl = EcSubst.subst_tydecl to_gen.tg_subst tydecl in
    let fv = tydecl_fv tydecl in
    let extra = generalize_extra_ty to_gen fv in
    let tyd_params = extra @ tydecl.tyd_params in
    let args = List.map (fun (id, _) -> tvar id) tyd_params in
    let fst_params = List.map fst tydecl.tyd_params in
    let tosubst = fst_params, tconstr path args in
    let tg_subst, tyd_type =
      match tydecl.tyd_type with
      | `Concrete _ | `Abstract _ ->
        EcSubst.add_tydef to_gen.tg_subst path tosubst, tydecl.tyd_type
      | `Record (f, prs) ->
        let subst    = EcSubst.empty ~freshen:false () in
        let tg_subst = to_gen.tg_subst in
        let subst    = EcSubst.add_tydef subst path tosubst in
        let tg_subst = EcSubst.add_tydef tg_subst path tosubst in
        let rsubst   = ref subst in
        let rtg_subst = ref tg_subst in
        let tin = tconstr path args in
        let add_op (s, ty) =
          let p = pqname prefix s in
          let tosubst = fst_params, e_op p args (tfun tin ty) in
          rsubst := EcSubst.add_opdef !rsubst p tosubst;
          rtg_subst := EcSubst.add_opdef !rtg_subst p tosubst;
          s, ty
        in
        let prs = List.map add_op prs in
        let f = EcSubst.subst_form !rsubst f in
        !rtg_subst, `Record (f, prs)
      | `Datatype dt ->
        let subst    = EcSubst.empty ~freshen:false () in
        let tg_subst = to_gen.tg_subst in
        let subst    = EcSubst.add_tydef subst path tosubst in
        let tg_subst = EcSubst.add_tydef tg_subst path tosubst in
        let subst_ty = EcSubst.subst_ty subst in
        let rsubst   = ref subst in
        let rtg_subst = ref tg_subst in
        let tout = tconstr path args in
        let add_op (s,tys) =
          let tys = List.map subst_ty tys in
          let p = pqname prefix s in
          let pty = toarrow tys tout in
          let tosubst = fst_params, e_op p args pty in
          rsubst := EcSubst.add_opdef !rsubst p tosubst;
          rtg_subst := EcSubst.add_opdef !rtg_subst p tosubst ;
          s, tys in
        let tydt_ctors   = List.map add_op dt.tydt_ctors in
        let tydt_schelim = EcSubst.subst_form !rsubst dt.tydt_schelim in
        let tydt_schcase = EcSubst.subst_form !rsubst dt.tydt_schcase in
        !rtg_subst, `Datatype {tydt_ctors; tydt_schelim; tydt_schcase }

    in

    let to_gen = { to_gen with tg_subst} in
    let tydecl = { tyd_params; tyd_type; tyd_loca = `Global } in
    to_gen, Some (Th_type (name, tydecl))

  | `Declare ->
    let to_gen = add_declared_ty to_gen path tydecl in
    to_gen, None

let generalize_opdecl to_gen prefix (name, operator) =
  let path = pqname prefix name in
  match operator.op_loca with
  | `Local -> to_gen, None
  | `Global ->
    let operator = EcSubst.subst_op to_gen.tg_subst operator in
    let tg_subst, operator =
      match operator.op_kind with
      | OB_oper None ->
        let fv = operator.op_ty.ty_fv in
        let extra = generalize_extra_ty to_gen fv in
        let op_tparams = extra @ operator.op_tparams in
        let op_ty = operator.op_ty in
        let args = List.map (fun (id, _) -> tvar id) op_tparams in
        let tosubst = (List.map fst operator.op_tparams,
                       e_op path args op_ty) in
        let tg_subst =
          EcSubst.add_opdef to_gen.tg_subst path tosubst in
        tg_subst, {op_tparams; op_ty; op_kind = OB_oper None; op_loca = `Global}

      | OB_pred None ->
        let fv = operator.op_ty.ty_fv in
        let extra = generalize_extra_ty to_gen fv in
        let op_tparams = extra @ operator.op_tparams in
        let op_ty = operator.op_ty in
        let args = List.map (fun (id, _) -> tvar id) op_tparams in
        let tosubst = (List.map fst operator.op_tparams,
                       f_op path args op_ty) in
        let tg_subst =
          EcSubst.add_pddef to_gen.tg_subst path tosubst in
        tg_subst, {op_tparams; op_ty; op_kind = OB_pred None; op_loca = `Global }

      | OB_oper (Some body) ->
        let fv = op_body_fv body operator.op_ty in
        let extra_t = generalize_extra_ty to_gen fv in
        let op_tparams = extra_t @ operator.op_tparams in
        let extra_a = generalize_extra_args to_gen.tg_binds fv in
        let op_ty = toarrow (List.map snd extra_a) operator.op_ty in
        let t_args = List.map (fun (id, _) -> tvar id) op_tparams in
        let eop = e_op path t_args op_ty in
        let e   =
          e_app eop (List.map (fun (id,ty) -> e_local id ty) extra_a)
            operator.op_ty in
        let tosubst =
          (List.map fst operator.op_tparams, e) in
        let tg_subst =
          EcSubst.add_opdef to_gen.tg_subst path tosubst in
        let body =
          match body with
          | OP_Constr _ | OP_Record _ | OP_Proj _ -> assert false
          | OP_TC -> assert false (* ??? *)
          | OP_Plain (e,nosmt) ->
            OP_Plain (e_lam extra_a e, nosmt)
          | OP_Fix opfix ->
            let subst = EcSubst.add_opdef (EcSubst.empty ~freshen:false ()) path tosubst in
            let nb_extra = List.length extra_a in
            let opf_struct =
              let (l,i) = opfix.opf_struct in
              (List.map (fun i -> i + nb_extra) l, i + nb_extra) in
            OP_Fix {
                opf_args     = extra_a @ opfix.opf_args;
                opf_resty    = opfix.opf_resty;
                opf_struct;
                opf_branches = EcSubst.subst_branches subst opfix.opf_branches;
                opf_nosmt    = opfix.opf_nosmt;
              }
        in
        let operator =
          {op_tparams; op_ty;
           op_kind = OB_oper (Some body); op_loca = `Global } in
        tg_subst, operator

      | OB_pred (Some body) ->
        let fv = pr_body_fv body operator.op_ty in
        let extra_t = generalize_extra_ty to_gen fv in
        let op_tparams = extra_t @ operator.op_tparams in
        let extra_a = generalize_extra_args to_gen.tg_binds fv in
        let op_ty   = toarrow (List.map snd extra_a) operator.op_ty in
        let t_args  = List.map (fun (id, _) -> tvar id) op_tparams in
        let fop = f_op path t_args op_ty in
        let f   =
          f_app fop (List.map (fun (id,ty) -> f_local id ty) extra_a)
            operator.op_ty in
        let tosubst =
          (List.map fst operator.op_tparams, f) in
        let tg_subst =
          EcSubst.add_pddef to_gen.tg_subst path tosubst in
        let body =
          match body with
          | PR_Plain f ->
            PR_Plain (f_lambda (List.map (fun (x,ty) -> (x,GTty ty)) extra_a) f)
          | PR_Ind pri ->
            let pri_args = extra_a @ pri.pri_args in
            PR_Ind { pri with pri_args }
        in
        let operator =
          {op_tparams; op_ty;
           op_kind = OB_pred (Some body); op_loca = `Global } in
        tg_subst, operator


      | OB_nott nott ->
        let fv = notation_fv nott in
        let extra_t = generalize_extra_ty to_gen fv in
        let op_tparams = extra_t @ operator.op_tparams in
        let extra_a = generalize_extra_args to_gen.tg_binds fv in
        let op_ty   = toarrow (List.map snd extra_a) operator.op_ty in
        let nott = { nott with ont_args = extra_a @ nott.ont_args; } in
        to_gen.tg_subst,
          { op_tparams; op_ty; op_kind = OB_nott nott; op_loca = `Global }
    in
    let to_gen = {to_gen with tg_subst} in
    to_gen, Some (Th_operator (name, operator))


  | `Declare ->
    let to_gen = add_declared_op to_gen path operator in
    to_gen, None

let generalize_axiom to_gen prefix (name, ax) =
  let ax = EcSubst.subst_ax to_gen.tg_subst ax in
  let path = pqname prefix name in
  match ax.ax_loca with
  | `Local ->
    assert (not (is_axiom ax.ax_kind));
    add_clear to_gen (`Ax path), None
  | `Global ->
    let ax_spec =
      match ax.ax_kind with
      | `Axiom _ ->
        generalize_extra_forall ~imply:false to_gen.tg_binds ax.ax_spec
      | `Lemma   ->
        generalize_extra_forall ~imply:true to_gen.tg_binds ax.ax_spec
    in
    let extra_t = generalize_extra_ty to_gen ax_spec.f_fv in
    let ax_tparams = extra_t @ ax.ax_tparams in
    to_gen, Some (Th_axiom (name, {ax with ax_tparams; ax_spec}))
  | `Declare ->
    assert (is_axiom ax.ax_kind);
    let to_gen = add_clear to_gen (`Ax path) in
    let to_gen =
      { to_gen with tg_binds = add_imp to_gen.tg_binds ax.ax_spec } in
    to_gen, None

let generalize_modtype to_gen (name, ms) =
  match ms.tms_loca with
  | `Local -> to_gen, None
  | `Global ->
    let ms = EcSubst.subst_top_modsig to_gen.tg_subst ms in
    to_gen, Some (Th_modtype (name, ms))

let generalize_module to_gen me =
  match me.tme_loca with
  | `Local -> to_gen, None
  | `Global ->
    (* FIXME section: we can generalize declare module *)
    let me = EcSubst.subst_top_module to_gen.tg_subst me in
    to_gen, Some (Th_module me)
  | `Declare -> assert false (* should be a LC_decl_mod *)

let generalize_export to_gen (p,lc) =
  if lc = `Local || to_clear to_gen (`Th p) then to_gen, None
  else to_gen, Some (Th_export (p,lc))

let generalize_instance to_gen (ty,tci, lc) =
  if lc = `Local then to_gen, None
  (* FIXME: be sure that we have no dep to declare or local,
     or fix this code *)
  else to_gen, Some (Th_instance (ty,tci,lc))

let generalize_baserw to_gen prefix (s,lc) =
  if lc = `Local then
    add_clear to_gen (`Baserw (pqname prefix s)), None
  else to_gen, Some (Th_baserw (s,lc))

let generalize_addrw to_gen (p, ps, lc) =
  if lc = `Local || to_clear to_gen (`Baserw p) then
    to_gen, None
  else
    let ps = List.filter (fun p -> to_keep to_gen (`Ax p)) ps in
    if ps = [] then to_gen, None
    else to_gen, Some (Th_addrw (p, ps, lc))

let generalize_reduction to_gen _rl = to_gen, None

let generalize_auto to_gen (n,s,ps,lc) =
  if lc = `Local then to_gen, None
  else
    let ps = List.filter (fun p -> to_keep to_gen (`Ax p)) ps in
    if ps = [] then to_gen, None
    else to_gen, Some (Th_auto (n,s,ps,lc))

let rec generalize_th_item to_gen prefix th_item =
  match th_item with
  | Th_type tydecl     -> generalize_tydecl to_gen prefix tydecl
  | Th_operator opdecl -> generalize_opdecl to_gen prefix opdecl
  | Th_axiom  ax       -> generalize_axiom  to_gen prefix ax
  | Th_modtype ms      -> generalize_modtype to_gen ms
  | Th_module me       -> generalize_module  to_gen me
  | Th_theory cth      -> generalize_ctheory to_gen prefix cth
  | Th_export (p,lc)   -> generalize_export to_gen (p,lc)
  | Th_instance (ty,i,lc) -> generalize_instance to_gen (ty,i,lc)
  | Th_typeclass _     -> assert false
  | Th_baserw (s,lc)   -> generalize_baserw to_gen prefix (s,lc)
  | Th_addrw (p,ps,lc) -> generalize_addrw to_gen (p, ps, lc)
  | Th_reduction rl    -> generalize_reduction to_gen rl
  | Th_auto hints      -> generalize_auto to_gen hints

and generalize_ctheory to_gen prefix (name, (cth, thmode)) =
  let path = pqname prefix name in
  let to_gen, cth_items =
    generalize_ctheory_struct to_gen path cth.cth_items in
  if cth_items = [] then
    add_clear to_gen (`Th path), None
  else
    let cth = { cth with cth_items } in
    to_gen, Some (Th_theory (name, (cth, thmode)))

and generalize_ctheory_struct to_gen prefix cth_struct =
  match cth_struct with
  | [] -> to_gen, []
  | item::items ->
    let to_gen, item = generalize_th_item to_gen prefix item in
    let to_gen, items =
      generalize_ctheory_struct to_gen prefix items in
    match item with
    | None -> to_gen, items
    | Some item -> to_gen, item :: items

let generalize_lc_item to_gen prefix item =
  match item with
  | SC_decl_mod (id, modty, restr) ->
    let to_gen = add_declared_mod to_gen id modty restr in
    to_gen, None
  | SC_th_item th_item ->
    generalize_th_item to_gen prefix th_item

let rec generalize_lc_items to_gen prefix items =
  match items with
  | [] -> []
  | item::items ->
    let to_gen, item = generalize_lc_item to_gen prefix item in
    let items = generalize_lc_items to_gen prefix items in
    match item with
    | None -> items
    | Some item -> item :: items

let generalize_lc_items scenv =
  let to_gen = {
      tg_env    = scenv.sc_env;
      tg_params = [];
      tg_binds  = [];
      tg_subst  = (EcSubst.empty ~freshen:false ());
      tg_clear  = empty_locals;
    } in
  generalize_lc_items to_gen (EcEnv.root scenv.sc_env) (List.rev scenv.sc_items)

(* --------------------------------------------------------------- *)
let get_locality scenv = scenv.sc_loca

let set_local l =
  match l with
  | `Global -> `Local
  | _ -> l

let rec set_local_item  = function
  | Th_type         (s,ty) -> Th_type      (s, { ty with tyd_loca = set_local ty.tyd_loca })
  | Th_operator     (s,op) -> Th_operator  (s, { op with op_loca  = set_local op.op_loca   })
  | Th_axiom        (s,ax) -> Th_axiom     (s, { ax with ax_loca  = set_local ax.ax_loca   })
  | Th_modtype      (s,ms) -> Th_modtype   (s, { ms with tms_loca = set_local ms.tms_loca  })
  | Th_module          me  -> Th_module        { me with tme_loca = set_local me.tme_loca  }
  | Th_typeclass    (s,tc) -> Th_typeclass (s, { tc with tc_loca  = set_local tc.tc_loca   })
  | Th_theory   (s,(th,m)) -> Th_theory    (s, (set_local_th th, m))
  | Th_export       (p,lc) -> Th_export    (p, set_local lc)
  | Th_instance (ty,ti,lc) -> Th_instance  (ty,ti, set_local lc)
  | Th_baserw       (s,lc) -> Th_baserw    (s, set_local lc)
  | Th_addrw     (p,ps,lc) -> Th_addrw     (p, ps, set_local lc)
  | Th_reduction       r   -> Th_reduction r
  | Th_auto     (i,s,p,lc) -> Th_auto      (i, s, p, set_local lc)

and set_local_th th =
  { th with cth_items = List.map set_local_item th.cth_items }

let sc_th_item t item =
  let item =
    match get_locality t with
    | `Global -> item
    | `Local  -> set_local_item item in
  SC_th_item item

let sc_decl_mod (id,mt,mr) = SC_decl_mod (id,mt,mr)


(* ---------------------------------------------------------------- *)

let is_abstract_ty = function
  | `Abstract _ -> true
  | _           -> false

let rec check_glob_mp_ty s scenv mp =
  let mtop = `Module (mastrip mp) in
  if is_declared scenv mtop then
    hierror "global %s can't depend on declared module" s;
  if is_local scenv mtop then
    hierror "global %s can't depend on local module" s;
  List.iter (check_glob_mp_ty s scenv) mp.m_args

let rec check_glob_mp scenv mp =
  let mtop = `Module (mastrip mp) in
  if is_local scenv mtop then
    hierror "global definition can't depend on local module";
  List.iter (check_glob_mp scenv) mp.m_args

let check_local scenv =
  if not (scenv.sc_insec) then
    hierror "local are only allowed in section"

let check_declare scenv =
  if not (scenv.sc_insec) then
    hierror "declare are only allowed in section"

let check_tyd scenv name tyd =
  match tyd.tyd_loca with
  | `Local ->
    check_local scenv

  | `Declare ->
    check_declare scenv;
    if tyd.tyd_params <> [] then
      hierror "declared type can not be polymorphic";
    if not (is_abstract_ty tyd.tyd_type) then
      hierror "only abstract type can be declared"
  | `Global ->
    let cb env (who:cbarg) =
      match who with
      | `Type p ->
        if is_local env who then
          hierror "global definition can't depend of local type %s"
            (EcPath.tostring p)
      | `Module mp -> check_glob_mp_ty "type" env mp
      | `Op _ ->
        (* This case can occur because of elim/case scheme *)
        assert (not (is_local env who || is_declared env who))
      | `Ax _  | `ModuleType _ -> assert false in
    on_tydecl scenv.sc_env cb name tyd

let cb_glob scenv (who:cbarg) =
  match who with
  | `Type p ->
    if is_local scenv who then
      hierror "global definition can't depend of local type %s"
        (EcPath.tostring p)
  | `Module mp ->
    check_glob_mp scenv mp
  | `Op p ->
    if is_local scenv who then
      hierror "global definition can't depend of local op %s"
        (EcPath.tostring p)
  | `ModuleType p ->
    if is_local scenv who then
      hierror "global definition can't depend of local module type %s"
        (EcPath.tostring p)
  | `Ax _ -> assert false

let check_op scenv name op =
  match op.op_loca with
  | `Local ->
    check_local scenv
  | `Declare ->
    check_declare scenv;
    if op.op_tparams <> [] then
      hierror "declared op can not be polymorphic";
    begin match op.op_kind with
    | OB_oper (Some _) | OB_pred (Some _) ->
      hierror "declared op can only be abstract"
    | OB_nott _ ->
      hierror "can't declare a notation"
    | _ -> ()
    end
  | `Global ->
    (* FIXME: need to do something special for fixpoint *)
    on_opdecl scenv.sc_env cb_glob name op

let check_ax scenv name ax =
  match ax.ax_loca with
  | `Local ->
    check_local scenv;
    if is_axiom ax.ax_kind then
      hierror "axiom can't be local"
  | `Declare ->
    check_declare scenv;
    if ax.ax_tparams <> [] then
      hierror "declared axiom can not be polymorphic";
    if is_lemma ax.ax_kind then
      hierror "can't declare a lemma";
    on_axiom (cb_glob scenv.sc_env) ax
  | `Global ->
    let as_decl = ref false in
    let env = scenv.sc_env in
    let doit who =
      if is_declared env who then as_decl := true;
      cb_glob env who in
    let doit =
      if is_axiom ax.ax_kind then doit
      else cb_glob env in
    on_axiom doit ax;
    if !as_decl then
      Format.eprintf "[W]Warning global axiom in section@."


let cb_mod scenv s (who : cbarg) =
  match who with
  | `Type p ->
    if is_local scenv who then
      hierror "global %s can't depend of local type %s"
        s (EcPath.tostring p);
    if is_declared scenv who then
      hierror "global %s can't depend of local type %s"
        s (EcPath.tostring p);
  | `Op p ->
    if is_local scenv who then
      hierror "global %s can't depend of local op %s"
        s (EcPath.tostring p);
    if is_declared scenv who then
      hierror "global %s can't depend of declared op %s"
        s (EcPath.tostring p);
  | `ModuleType p ->
    if is_local scenv who then
      hierror "global %s can't depend of local module type %s"
       s (EcPath.tostring p);

  | `Module mp -> check_glob_mp_ty s scenv mp
  | `Ax _      -> assert false


let check_modtype scenv ms =
  match ms.tms_loca with
  | `Local -> check_local scenv
  | `Global ->
    if scenv.sc_insec then on_modsig (cb_mod scenv.sc_env "module type") ms.tms_sig

let check_module scenv me =
  match me.tme_loca with
  | `Local -> check_local scenv
  | `Global ->
    if scenv.sc_insec then on_module (cb_mod scenv.sc_env "module") me.tme_expr
  | `Declare -> (* Should be SC_decl_mod ... *)
    assert false

let check_typeclass scenv tc =
  (* FIXME section *)
  assert false

let rec check_item item scenv =
  match item with
  | Th_type     (s,tyd) -> check_tyd scenv s tyd
  | Th_operator  (s,op) -> check_op  scenv s op
  | Th_axiom    (s, ax) -> check_ax scenv s ax
  | Th_modtype  (_, ms) -> check_modtype scenv ms
  | Th_module        me -> check_module scenv me
  | Th_typeclass (_,tc) -> check_typeclass scenv tc
  | Th_theory (_,(cth, _)) -> check_ctheory scenv cth
  | Th_export   (_, lc) -> assert (lc = `Global || scenv.sc_insec);
  | Th_instance       _ -> () (* FIXME section: what to check *)
  | Th_baserw (_,lc) ->
    if (lc = `Local && not scenv.sc_insec) then
      hierror "local base rewrite can only be declared inside section";
  | Th_addrw (_,_,lc) ->
    if (lc = `Local && not scenv.sc_insec) then
      hierror "local hint rewrite can only be declared inside section";

  | Th_auto (_, _, _, lc) ->
    if (lc = `Local && not scenv.sc_insec) then
      hierror "local hint can only be declared inside section";

  | Th_reduction _ -> ()

and check_ctheory scenv cth =
  check_theory scenv cth.cth_items

and check_theory scenv th = ()
  (* FIXME section : how to check it recursively, need to add stuff in env ? *)

let check_item item scenv =
  if scenv.sc_insec then check_item item scenv

let add_item (item : theory_item) (scenv:scenv) =
  let item = if scenv.sc_loca = `Local then set_local_item item else item in
  let sc_items = SC_th_item item :: scenv.sc_items in
  let doit f =
    { scenv with
      sc_env = f scenv.sc_env;
      sc_items } in
  check_item item scenv;
  match item with
  | Th_type    (s,tyd) -> doit (EcEnv.Ty.bind s tyd)
  | Th_operator (s,op) -> doit (EcEnv.Op.bind s op)
  | Th_axiom   (s, ax) -> doit (EcEnv.Ax.bind s ax)
  | Th_modtype (s, ms) -> doit (EcEnv.ModTy.bind s ms)
  | Th_module       me -> doit (EcEnv.Mod.bind me.tme_expr.me_name me)

  | Th_typeclass (s,tc) -> doit (EcEnv.TypeClass.bind s tc)

  | Th_theory (s,(cth, mode)) ->
    doit (EcEnv.Theory.bind ~mode ?src:cth.cth_source s cth.cth_items);

  | Th_export (p, lc) -> doit (EcEnv.Theory.export p lc)

  | Th_instance (tys,i,lc) -> doit (EcEnv.TypeClass.add_instance tys i lc)

  | Th_baserw (s,lc) -> doit (EcEnv.BaseRw.add s lc)

  | Th_addrw (p,ps,lc) -> doit (EcEnv.BaseRw.addto p ps lc)

  | Th_auto (level, base, ps, lc) -> doit (EcEnv.Auto.add ~level ?base ps lc)

  | Th_reduction r -> doit (EcEnv.Reduction.add r)



let add_decl_mod id mt mr scenv =
  match scenv.sc_name with
  | Th _ | Top ->
    hierror "declare module are only allowed inside section"
  | Sc _ ->
    { scenv with
      sc_env = EcEnv.Mod.declare_local id mt mr scenv.sc_env;
      sc_items = SC_decl_mod (id,mt,mr) :: scenv.sc_items }

let add (item:sc_item) (scenv:scenv) =
  match item with
  | SC_th_item item -> add_item item scenv
  | SC_decl_mod(id,mt,mr) -> add_decl_mod id mt mr scenv

(* -----------------------------------------------------------*)
let enter_section (name : symbol option) (scenv : scenv) =
  { sc_env = scenv.sc_env;
    sc_top = Some scenv;
    sc_loca = `Global;
    sc_name = Sc name;
    sc_insec = true;
    sc_items = []; }

let exit_section (name : symbol option) (scenv:scenv) =
  match scenv.sc_name with
  | Top  -> hierror "no section to close"
  | Th _ -> hierror "cannot close a section containing pending theories"
  | Sc sname ->
    let get = odfl "<empty>" in
    if sname <> name then
      hierror "expecting [%s], not [%s]" (get sname) (get name);
    let items = generalize_lc_items scenv in
    let scenv = oget scenv.sc_top in
    List.fold_left (fun env i -> add_item i env) scenv items

(* -----------------------------------------------------------*)

let enter_theory (name:symbol) (lc:is_local) scenv : scenv =
  if not scenv.sc_insec && lc = `Local then
     hierror "can not start a local theory outside of a section";
  let sc_env = EcEnv.Theory.enter name scenv.sc_env in
  {scenv with
    sc_env;
    sc_top  = Some scenv;
    sc_loca = if lc = `Local then lc else scenv.sc_loca;
    sc_name = Th name;
    sc_items = []; }

let exit_theory ?clears ?pempty scenv =
  match scenv.sc_name with
  | Sc _    -> hierror "cannot close a theory containing pending sections"
  | Top     -> hierror "no theory to close"
  | Th name ->
    let cth = EcEnv.Theory.close ?clears ?pempty scenv.sc_env in
    let scenv = oget scenv.sc_top in
    name, cth, scenv

(* -----------------------------------------------------------*)
let import p scenv =
  { scenv with sc_env = EcEnv.Theory.import p scenv.sc_env }

let import_vars m scenv =
  { scenv with
    sc_env = EcEnv.Mod.import_vars scenv.sc_env m }

let require ?mode x cth scenv =
  { scenv with sc_env = EcEnv.Theory.require ?mode x cth scenv.sc_env }

let astop scenv =
  if scenv.sc_insec then hierror "can not require inside a section";
  { scenv with sc_env = EcEnv.astop scenv.sc_env }
