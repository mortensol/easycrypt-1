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
exception NoSectionOpened

type locality = EcParsetree.locality

type locals = {
  lc_env     : EcEnv.env;
  lc_name    : symbol option;
  lc_declare : declare list;
  lc_items   : lc_item list;
}

and lc_item =
  | LC_th_item of locality * EcTheory.ctheory_item
  | LC_decl_mod of EcIdent.t * module_type * mod_restr


and declare =
  | DC_Module of EcIdent.t
  | DC_Type   of EcPath.path
  | DC_Op     of EcPath.path
  | DC_Pred   of EcPath.path

let is_declared_type (lc: locals) p =
  List.exists (function DC_Type p' -> p_equal p p' | _ -> false) lc.lc_declare

let is_declared_op (lc:locals) p =
  List.exists (function DC_Op p' | DC_Pred p' -> p_equal p p' | _ -> false)
    lc.lc_declare

let env_of_locals (lc : locals) = lc.lc_env

let items_of_locals (lc : locals) = lc.lc_items

let is_local who p (lc : locals) =
  match who with
  | `Lemma  -> Mp.find_opt p (snd lc.lc_lemmas) |> omap fst = Some `Local
  | `Module -> Sp.mem p lc.lc_modules

exception UseLocal of EcPath.mpath

let rec use_mp_local (lc : locals) mp =
  begin match mp.m_top with
  | `Local _ -> ()
  | `Concrete (p, _) -> if is_local `Module p lc then raise (UseLocal mp)
  end;
  List.iter (use_mp_local lc) mp.m_args

let is_mp_local mp (lc : locals) =
  try use_mp_local lc mp; false
  with UseLocal _ -> true

let rec is_mp_abstract mp (lc : locals) =
  let toplocal =
    match mp.m_top with
    | `Concrete _ -> false
    | `Local i -> Sid.mem i (snd lc.lc_abstracts)
  in
    toplocal || (List.exists (is_mp_abstract^~ lc) mp.m_args)

let rec on_mpath_ty cb (ty : ty) =
  match ty.ty_node with
  | Tunivar _        -> ()
  | Tvar    _        -> ()
  | Tglob mp         -> cb mp
  | Ttuple tys       -> List.iter (on_mpath_ty cb) tys
  | Tconstr (_, tys) -> List.iter (on_mpath_ty cb) tys
  | Tfun (ty1, ty2)  -> List.iter (on_mpath_ty cb) [ty1; ty2]

let on_mpath_pv cb (pv : prog_var)=
  cb pv.pv_name.x_top

let on_mpath_lp cb (lp : lpattern) =
  match lp with
  | LSymbol (_, ty) -> on_mpath_ty cb ty
  | LTuple  xs      -> List.iter (fun (_, ty) -> on_mpath_ty cb ty) xs
  | LRecord (_, xs) -> List.iter (on_mpath_ty cb |- snd) xs

let on_mpath_binding cb ((_, ty) : (EcIdent.t * ty)) =
  on_mpath_ty cb ty

let on_mpath_bindings cb bds =
  List.iter (on_mpath_binding cb) bds

let rec on_mpath_expr cb (e : expr) =
  let cbrec = on_mpath_expr cb in

  let rec fornode () =
    match e.e_node with
    | Eint   _            -> ()
    | Elocal _            -> ()
    | Equant (_, bds, e)  -> on_mpath_bindings cb bds; cbrec e
    | Evar   pv           -> on_mpath_pv cb pv
    | Elet   (lp, e1, e2) -> on_mpath_lp cb lp; List.iter cbrec [e1; e2]
    | Etuple es           -> List.iter cbrec es
    | Eop    (_, tys)     -> List.iter (on_mpath_ty cb) tys
    | Eapp   (e, es)      -> List.iter cbrec (e :: es)
    | Eif    (c, e1, e2)  -> List.iter cbrec [c; e1; e2]
    | Ematch (e, es, ty)  -> on_mpath_ty cb ty; List.iter cbrec (e :: es)
    | Eproj  (e, _)       -> cbrec e

  in on_mpath_ty cb e.e_ty; fornode ()

let on_mpath_lv cb (lv : lvalue) =
  let for1 (pv, ty) = on_mpath_pv cb pv; on_mpath_ty cb ty in

    match lv with
    | LvVar   pv  -> for1 pv
    | LvTuple pvs -> List.iter for1 pvs

let rec on_mpath_instr cb (i : instr)=
  match i.i_node with
  | Srnd (lv, e) | Sasgn (lv, e) ->
      on_mpath_lv cb lv;
      on_mpath_expr cb e

  | Sassert e ->
      on_mpath_expr cb e

  | Scall (lv, f, args) ->
      lv |> oiter (on_mpath_lv cb);
      cb f.x_top;
      List.iter (on_mpath_expr cb) args

  | Sif (e, s1, s2) ->
      on_mpath_expr cb e;
      List.iter (on_mpath_stmt cb) [s1; s2]

  | Swhile (e, s) ->
      on_mpath_expr cb e;
      on_mpath_stmt cb s

  | Sabstract _ -> ()

and on_mpath_stmt cb (s : stmt) =
  List.iter (on_mpath_instr cb) s.s_node

let on_mpath_lcmem cb m =
    cb (EcMemory.lmt_xpath m).x_top;
    Msym.iter (fun _ (_,ty) -> on_mpath_ty cb ty) (EcMemory.lmt_bindings m)

let on_mpath_memenv cb (m : EcMemory.memenv) =
  match snd m with
  | None    -> ()
  | Some lm -> on_mpath_lcmem cb lm

let rec on_mpath_modty cb mty =
  List.iter (fun (_, mty) -> on_mpath_modty cb mty) mty.mt_params;
  List.iter cb mty.mt_args

let on_mpath_gbinding cb b =
  match b with
  | EcFol.GTty ty ->
      on_mpath_ty cb ty
  | EcFol.GTmodty (mty, (rx,r)) ->
      on_mpath_modty cb mty;
      Sx.iter (fun x -> cb x.x_top) rx;
      Sm.iter cb r
  | EcFol.GTmem None->
      ()
  | EcFol.GTmem (Some m) ->
      on_mpath_lcmem cb m

let on_mpath_gbindings cb b =
  List.iter (fun (_, b) -> on_mpath_gbinding cb b) b

let rec on_mpath_form cb (f : EcFol.form) =
  let cbrec = on_mpath_form cb in

  let rec fornode () =
    match f.EcFol.f_node with
    | EcFol.Fint      _            -> ()
    | EcFol.Flocal    _            -> ()
    | EcFol.Fquant    (_, b, f)    -> on_mpath_gbindings cb b; cbrec f
    | EcFol.Fif       (f1, f2, f3) -> List.iter cbrec [f1; f2; f3]
    | EcFol.Fmatch    (b, fs, ty)  -> on_mpath_ty cb ty; List.iter cbrec (b :: fs)
    | EcFol.Flet      (lp, f1, f2) -> on_mpath_lp cb lp; List.iter cbrec [f1; f2]
    | EcFol.Fop       (_, tys)     -> List.iter (on_mpath_ty cb) tys
    | EcFol.Fapp      (f, fs)      -> List.iter cbrec (f :: fs)
    | EcFol.Ftuple    fs           -> List.iter cbrec fs
    | EcFol.Fproj     (f, _)       -> cbrec f
    | EcFol.Fpvar     (pv, _)      -> on_mpath_pv  cb pv
    | EcFol.Fglob     (mp, _)      -> cb mp
    | EcFol.FhoareF   hf           -> on_mpath_hf  cb hf
    | EcFol.FhoareS   hs           -> on_mpath_hs  cb hs
    | EcFol.FequivF   ef           -> on_mpath_ef  cb ef
    | EcFol.FequivS   es           -> on_mpath_es  cb es
    | EcFol.FeagerF   eg           -> on_mpath_eg  cb eg
    | EcFol.FbdHoareS bhs          -> on_mpath_bhs cb bhs
    | EcFol.FbdHoareF bhf          -> on_mpath_bhf cb bhf
    | EcFol.Fpr       pr           -> on_mpath_pr  cb pr

  and on_mpath_hf cb hf =
    on_mpath_form cb hf.EcFol.hf_pr;
    on_mpath_form cb hf.EcFol.hf_po;
    cb hf.EcFol.hf_f.x_top

  and on_mpath_hs cb hs =
    on_mpath_form cb hs.EcFol.hs_pr;
    on_mpath_form cb hs.EcFol.hs_po;
    on_mpath_stmt cb hs.EcFol.hs_s;
    on_mpath_memenv cb hs.EcFol.hs_m

  and on_mpath_ef cb ef =
    on_mpath_form cb ef.EcFol.ef_pr;
    on_mpath_form cb ef.EcFol.ef_po;
    cb ef.EcFol.ef_fl.x_top;
    cb ef.EcFol.ef_fr.x_top

  and on_mpath_es cb es =
    on_mpath_form cb es.EcFol.es_pr;
    on_mpath_form cb es.EcFol.es_po;
    on_mpath_stmt cb es.EcFol.es_sl;
    on_mpath_stmt cb es.EcFol.es_sr;
    on_mpath_memenv cb es.EcFol.es_ml;
    on_mpath_memenv cb es.EcFol.es_mr

  and on_mpath_eg cb eg =
    on_mpath_form cb eg.EcFol.eg_pr;
    on_mpath_form cb eg.EcFol.eg_po;
    cb eg.EcFol.eg_fl.x_top;
    cb eg.EcFol.eg_fr.x_top;
    on_mpath_stmt cb eg.EcFol.eg_sl;
    on_mpath_stmt cb eg.EcFol.eg_sr;

  and on_mpath_bhf cb bhf =
    on_mpath_form cb bhf.EcFol.bhf_pr;
    on_mpath_form cb bhf.EcFol.bhf_po;
    on_mpath_form cb bhf.EcFol.bhf_bd;
    cb bhf.EcFol.bhf_f.x_top

  and on_mpath_bhs cb bhs =
    on_mpath_form cb bhs.EcFol.bhs_pr;
    on_mpath_form cb bhs.EcFol.bhs_po;
    on_mpath_form cb bhs.EcFol.bhs_bd;
    on_mpath_stmt cb bhs.EcFol.bhs_s;
    on_mpath_memenv cb bhs.EcFol.bhs_m

  and on_mpath_pr cb pr =
    cb pr.EcFol.pr_fun.x_top;
    List.iter (on_mpath_form cb) [pr.EcFol.pr_event; pr.EcFol.pr_args]

  in
    on_mpath_ty cb f.EcFol.f_ty; fornode ()

let rec on_mpath_module cb (me : module_expr) =
  match me.me_body with
  | ME_Alias (_, mp)  -> cb mp
  | ME_Structure st   -> on_mpath_mstruct cb st
  | ME_Decl (mty, sm) -> on_mpath_mdecl cb (mty, sm)

and on_mpath_mdecl cb (mty,(rx,r)) =
  on_mpath_modty cb mty;
  Sx.iter (fun x -> cb x.x_top) rx;
  Sm.iter cb r

and on_mpath_mstruct cb st =
  List.iter (on_mpath_mstruct1 cb) st.ms_body

and on_mpath_mstruct1 cb item =
  match item with
  | MI_Module   me -> on_mpath_module cb me
  | MI_Variable x  -> on_mpath_ty cb x.v_type
  | MI_Function f  -> on_mpath_fun cb f

and on_mpath_fun cb fun_ =
  on_mpath_fun_sig  cb fun_.f_sig;
  on_mpath_fun_body cb fun_.f_def

and on_mpath_fun_sig cb fsig =
  on_mpath_ty cb fsig.fs_arg;
  on_mpath_ty cb fsig.fs_ret

and on_mpath_fun_body cb fbody =
  match fbody with
  | FBalias xp -> cb xp.x_top
  | FBdef fdef -> on_mpath_fun_def cb fdef
  | FBabs oi   -> on_mpath_fun_oi  cb oi

and on_mpath_fun_def cb fdef =
  List.iter (fun v -> on_mpath_ty cb v.v_type) fdef.f_locals;
  on_mpath_stmt cb fdef.f_body;
  fdef.f_ret |> oiter (on_mpath_expr cb);
  on_mpath_uses cb fdef.f_uses

and on_mpath_uses cb uses =
  List.iter (fun x -> cb x.x_top) uses.us_calls;
  Sx.iter   (fun x -> cb x.x_top) uses.us_reads;
  Sx.iter   (fun x -> cb x.x_top) uses.us_writes

and on_mpath_fun_oi cb oi =
  List.iter (fun x -> cb x.x_top) oi.oi_calls

(* -------------------------------------------------------------------- *)

let check_use_local_or_abs lc mp =
  if is_mp_local mp lc || is_mp_abstract mp lc then
    raise (UseLocal mp)

let form_use_local f lc =
  try  on_mpath_form (use_mp_local lc) f; None
  with UseLocal mp -> Some mp

(* -------------------------------------------------------------------- *)
let form_use_local_or_abs f lc =
  try  on_mpath_form (check_use_local_or_abs lc) f; false
  with UseLocal _ -> true

(* -------------------------------------------------------------------- *)
let module_use_local_or_abs m lc =
  try  on_mpath_module (check_use_local_or_abs lc) m; false
  with UseLocal _ -> true

(* -------------------------------------------------------------------- *)
let opdecl_use_local_or_abs opdecl lc =
  let cb = check_use_local_or_abs lc in

  try
    on_mpath_ty cb opdecl.op_ty;
    (match opdecl.op_kind with
     | OB_pred None -> ()

     | OB_pred (Some (PR_Plain f)) ->
        on_mpath_form cb f

     | OB_pred (Some (PR_Ind pri)) ->
        on_mpath_bindings cb pri.pri_args;
        List.iter (fun ctor ->
          on_mpath_gbindings cb ctor.prc_bds;
          List.iter (on_mpath_form cb) ctor.prc_spec)
        pri.pri_ctors

     | OB_nott nott -> begin
        List.iter (on_mpath_ty cb |- snd) nott.ont_args;
        on_mpath_ty cb nott.ont_resty;
        on_mpath_expr cb nott.ont_body
       end


     | OB_oper None   -> ()
     | OB_oper Some b ->
         match b with
         | OP_Constr _ -> ()
         | OP_Record _ -> ()
         | OP_Proj   _ -> ()
         | OP_TC       -> ()
         | OP_Plain  (e, _) -> on_mpath_expr cb e
         | OP_Fix    f ->
           let rec on_mpath_branches br =
             match br with
             | OPB_Leaf (bds, e) ->
                 List.iter (on_mpath_bindings cb) bds;
                 on_mpath_expr cb e
             | OPB_Branch br ->
                 Parray.iter on_mpath_branch br

           and on_mpath_branch br =
             on_mpath_branches br.opb_sub

           in on_mpath_branches f.opf_branches);
    false

  with UseLocal _ -> true

(* -------------------------------------------------------------------- *)
let tydecl_use_local_or_abs tydecl lc =
  let cb = check_use_local_or_abs lc in

  try
    (match tydecl.tyd_type with
    | `Concrete ty -> on_mpath_ty cb ty
    | `Abstract _  -> ()

    | `Record (f, fds) ->
        on_mpath_form cb f;
        List.iter (on_mpath_ty cb |- snd) fds

    | `Datatype dt ->
        List.iter (List.iter (on_mpath_ty cb) |- snd) dt.tydt_ctors;
        List.iter (on_mpath_form cb) [dt.tydt_schelim; dt.tydt_schcase]);
    false

  with UseLocal _ -> true

(* -------------------------------------------------------------------- *)

type to_gen = {
    tg_params  : (EcIdent.t * Sp.t) list;
    tg_binds  : bind list;
    tg_subst : EcSubst.subst;
    tg_clear : Sp.t;
  }

and bind =
  | Binding of binding
  | Imply    of form


let add_bind binds bd = binds @ [Binding bd]
let add_imp binds f   = binds @ [Imply f]
let add_clear to_gen p =
  { to_gen with tg_clear = Sp.add p to_gen.tg_clear }

let to_keep to_gen p = Sp.mem p to_gen.tg_clear

let generalize_type to_gen ty =
  EcSubst.subst_ty to_gen.tg_subst ty

let add_declared_mod to_gen id modty restr =
  { to_gen with
    tg_binds  = add_bind to_gen.tg_binds (id, gtmodty modty restr);
    tg_subst  = EcSubst.add_module to_gen.tg_subst id (mpath_abs id [])
  }

let add_declared_ty env to_gen path =
  let tydecl = EcEnv.Ty.by_path path env in
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

let add_declared_op env to_gen path =
  let opdecl = EcEnv.Op.by_path path env in
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

let generalize_tydecl env to_gen locality prefix (name, tydecl) =
  let path = pqname prefix name in
  match locality with
  | EcParsetree.Local -> to_gen, None
  | EcParsetree.Global ->
    let tydecl = EcSubst.subst_tydecl to_gen.tg_subst tydecl in
    let fv = tydecl_fv tydecl in
    let extra = generalize_extra_ty to_gen fv in
    let tyd_params = extra @ tydecl.tyd_params in
    let args = List.map (fun (id, _) -> tvar id) tyd_params in
    let tosubst = (List.map fst tydecl.tyd_params, tconstr path args) in
    (* For recursive type *)
    let tyd_type =
      (EcSubst.subst_tydecl (EcSubst.add_tydef EcSubst.empty path tosubst)
        tydecl).tyd_type in
    (* Build the substitution for the remaining *)
    let to_gen =
      {to_gen with
       tg_subst = EcSubst.add_tydef to_gen.tg_subst path tosubst} in

    to_gen, Some (CTh_type (name, { tyd_params; tyd_type }))
  | EcParsetree.Declare ->
    let to_gen = add_declared_ty env to_gen path in
    to_gen, None

let generalize_opdecl env to_gen locality prefix (name, operator) =
  let path = pqname prefix name in
  match locality with
  | EcParsetree.Local -> to_gen, None
  | EcParsetree.Global ->
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
        tg_subst, {op_tparams; op_ty; op_kind = OB_oper None}

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
        tg_subst, {op_tparams; op_ty; op_kind = OB_pred None}

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
          | OP_Fix opfix ->
            let subst = EcSubst.add_opdef EcSubst.empty path tosubst in
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

          | _ -> body in
        tg_subst, {op_tparams; op_ty; op_kind = OB_oper (Some body) }

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
          | PR_Plain _ -> body
          | PR_Ind pri ->
            let subst = EcSubst.add_pddef EcSubst.empty path tosubst in
            let pri_args = extra_a @ pri.pri_args in
            let mk_ctor ctor =
              {ctor with
                (* FIXME should we generalize here *)
                prc_bds =
                  List.map (fun (id,ty) -> id, gtty ty) extra_a @ ctor.prc_bds;
                prc_spec = List.map (EcSubst.subst_form subst) ctor.prc_spec;
              } in
            let pri_ctors = List.map mk_ctor pri.pri_ctors in
            PR_Ind { pri_args; pri_ctors } in
        tg_subst, {op_tparams; op_ty; op_kind = OB_pred (Some body) }


      | OB_nott nott ->
        let fv = notation_fv nott in
        let extra_t = generalize_extra_ty to_gen fv in
        let op_tparams = extra_t @ operator.op_tparams in
        let extra_a = generalize_extra_args to_gen.tg_binds fv in
        let op_ty   = toarrow (List.map snd extra_a) operator.op_ty in
        let nott = { nott with ont_args = extra_a @ nott.ont_args; } in
        to_gen.tg_subst,
          { op_tparams; op_ty; op_kind = OB_nott nott }
    in
    let to_gen = {to_gen with tg_subst} in
    to_gen, Some (CTh_operator (name, operator))


  | EcParsetree.Declare ->
    let to_gen = add_declared_op env to_gen path in
    to_gen, None

let generalize_axiom _env to_gen locality prefix (name, ax) =
  let ax = EcSubst.subst_ax to_gen.tg_subst ax in
  let path = pqname prefix name in
  match locality with
  | EcParsetree.Local ->
    (* FIXME *)
    assert (not (is_axiom ax.ax_kind));
    add_clear to_gen path , None
  | EcParsetree.Global ->
    let ax_spec =
      match ax.ax_kind with
      | `Axiom _ ->
        generalize_extra_forall ~imply:false to_gen.tg_binds ax.ax_spec
      | `Lemma   ->
        generalize_extra_forall ~imply:true to_gen.tg_binds ax.ax_spec
    in
    let extra_t = generalize_extra_ty to_gen ax_spec.f_fv in
    let ax_tparams = extra_t @ ax.ax_tparams in
    to_gen, Some (CTh_axiom (name, {ax with ax_tparams; ax_spec}))
  | EcParsetree.Declare ->
    assert (is_axiom ax.ax_kind);
    let to_gen = add_clear to_gen path in
    let to_gen =
      { to_gen with tg_binds = add_imp to_gen.tg_binds ax.ax_spec } in
    to_gen, None

let generalize_modtype _env to_gen locality _prefix (name, ms) =
  match locality with
  | EcParsetree.Local ->
    to_gen, None
  | EcParsetree.Global ->
    let ms = EcSubst.subst_modsig to_gen.tg_subst ms in
    to_gen, Some (CTh_modtype (name, ms))
  | EcParsetree.Declare -> assert false

let generalize_modtype _env to_gen locality _prefix (name, ms) =
  match locality with
  | EcParsetree.Local ->
    to_gen, None
  | EcParsetree.Global ->
    let ms = EcSubst.subst_modsig to_gen.tg_subst ms in
    to_gen, Some (CTh_modtype (name, ms))
  | EcParsetree.Declare -> assert false

let generalize_module _env to_gen locality _prefix me =
  match locality with
  | EcParsetree.Local ->
    to_gen, None
  | EcParsetree.Global ->
    (* FIXME: we can generalize declare module *)
    let me = EcSubst.subst_module to_gen.tg_subst me in
    to_gen, Some (CTh_module me)
  | EcParsetree.Declare -> assert false (* should be a LC_decl_mod *)

let generalize_export _env to_gen locality _prefix p =
  assert (locality <> EcParsetree.Declare);
  if locality = EcParsetree.Local then to_gen, None
  else to_gen, Some (CTh_export p)

let generalize_baserw _env to_gen locality prefix s =
  assert (locality <> EcParsetree.Declare);
  if locality = EcParsetree.Local then
    add_clear to_gen (pqname prefix s), None
  else to_gen, Some (CTh_baserw s)

let generalize_addrw _env to_gen locality _prefix p ps =
  assert (locality <> EcParsetree.Declare);
  if locality = EcParsetree.Local || not (to_keep to_gen p) then
    to_gen, None
  else
    let ps = List.filter (to_keep to_gen) ps in
    if ps = [] then to_gen, None
    else to_gen, Some (CTh_addrw (p, ps))

let generalize_reduction _env to_gen locality _prefix rl =
  assert (locality <> EcParsetree.Declare);
  if locality = EcParsetree.Local then
    to_gen, None
  else
    (* FIXME ensure no dependency to local and declare *)
    to_gen, Some(CTh_reduction rl)

let generalize_auto _env to_gen locality _prefix (b,n,s,ps) =
  assert (locality <> EcParsetree.Declare);
  if locality = EcParsetree.Local then
    to_gen, None
  else
    let ps = List.filter (to_keep to_gen) ps in
    if ps = [] then to_gen, None
    else to_gen, Some (CTh_auto (b,n,s,ps))

(* FIXME : add locality for baserw addrw reduction auto *)
let rec generalize_th_item env to_gen locality prefix th_item =
  match th_item with
  | CTh_type tydecl     -> generalize_tydecl env to_gen locality prefix tydecl
  | CTh_operator opdecl -> generalize_opdecl env to_gen locality prefix opdecl
  | CTh_axiom  ax       -> generalize_axiom env to_gen locality prefix ax
  | CTh_modtype ms      -> generalize_modtype env to_gen locality prefix ms
  | CTh_module me       -> generalize_module env to_gen locality prefix me
  | CTh_theory cth      -> generalize_ctheory env to_gen locality prefix cth
  | CTh_export p        -> generalize_export env to_gen locality prefix p
  | CTh_instance  _     -> assert false
  | CTh_typeclass _     -> assert false
  | CTh_baserw  s       -> generalize_baserw env to_gen locality prefix s
  | CTh_addrw  (p,ps)   -> generalize_addrw env to_gen locality prefix p ps
  | CTh_reduction rl    -> generalize_reduction env to_gen locality prefix rl
  | CTh_auto hints      -> generalize_auto env to_gen locality prefix hints

and generalize_ctheory env to_gen locality prefix (name, (cth, thmode)) =
  assert (locality <> EcParsetree.Declare);
  if locality = EcParsetree.Local && thmode = `Abstract then
    to_gen, None
  else
  (* FIXME: c'est quoi ce ctheory_clone ? *)
  let prefix = pqname prefix name in
  let to_gen, cth_struct =
    generalize_ctheory_struct env to_gen locality prefix cth.cth_struct in
  if cth_struct = [] then to_gen, None
  else
    let cth = {cth_desc = CTh_struct cth_struct; cth_struct = cth_struct} in
    to_gen, Some (CTh_theory (name, (cth, thmode)))

and generalize_ctheory_struct env to_gen locality prefix cth_struct =
  match cth_struct with
  | [] -> to_gen, []
  | item::items ->
    let to_gen, item = generalize_th_item env to_gen locality prefix item in
    let to_gen, items =
      generalize_ctheory_struct env to_gen locality prefix items in
    match item with
    | None -> to_gen, items
    | Some item -> to_gen, item :: items

let generalize_lc_item env to_gen prefix item =
  match item with
  | LC_decl_mod (id, modty, restr) ->
    let to_gen = add_declared_mod to_gen id modty restr in
    to_gen, None
  | LC_th_item (locality, th_item) ->
    generalize_th_item env to_gen locality prefix th_item

let rec generalize_lc_items env to_gen prefix items =
  match items with
  | [] -> []
  | item::items ->
    let to_gen, item = generalize_lc_item env to_gen prefix item in
    let items = generalize_lc_items env to_gen prefix items in
    match item with
    | None -> items
    | Some item -> item :: items








(* ---------------------------------------------------------------- *)

let abstracts lc = lc.lc_abstracts

let generalize env lc (f : EcFol.form) =
  let axioms =
    List.pmap
      (fun (p, lvl) ->
         match lvl with `Global, `Axiom -> Some p | _ -> None)
      (fst lc.lc_lemmas)
  in

  match axioms with
  | [] ->
    let mods = Sid.of_list (List.map fst (fst lc.lc_abstracts)) in
      if   Mid.set_disjoint mods f.EcFol.f_fv
      then f
      else begin
        List.fold_right
          (fun (x, (mty, rt)) f ->
             match Mid.mem x f.EcFol.f_fv with
             | false -> f
             | true  -> EcFol.f_forall [(x, EcFol.GTmodty (mty, rt))] f)
          (fst lc.lc_abstracts) f
      end

  | _ ->
    let f =
      let do1 p f =
        let ax = EcEnv.Ax.by_path p env in
        EcFol.f_imp ax.ax_spec f
      in
          List.fold_right do1 axioms f in
    let f =
      let do1 (x, (mty, rt)) f =
        EcFol.f_forall [(x, EcFol.GTmodty (mty, rt))] f
      in
        List.fold_right do1 (fst lc.lc_abstracts) f
    in
      f

let elocals (env : EcEnv.env) (name : symbol option) : locals =
  { lc_env       = env;
    lc_name      = name;
    lc_lemmas    = ([], Mp.empty);
    lc_modules   = Sp.empty;
    lc_abstracts = ([], Sid.empty);
    lc_items     = []; }

type t = locals list

let initial : t = []

let in_section (cs : t) =
  match cs with [] -> false | _ -> true

let enter (env : EcEnv.env) (name : symbol option) (cs : t) : t =
  match List.ohead cs with
  | None    -> [elocals env name]
  | Some ec ->
    let ec =
      { ec with
          lc_items = [];
          lc_abstracts = ([], snd ec.lc_abstracts);
          lc_env = env;
          lc_name = name; }
    in
      ec :: cs

let exit (cs : t) =
  match cs with
  | [] -> raise NoSectionOpened
  | ec :: cs ->
      ({ ec with lc_items     = List.rev ec.lc_items;
                 lc_abstracts = fst_map List.rev ec.lc_abstracts;
                 lc_lemmas    = fst_map List.rev ec.lc_lemmas},
       cs)

let path (cs : t) : symbol option * path =
  match cs with
  | [] -> raise NoSectionOpened
  | ec :: _ -> (ec.lc_name, EcEnv.root ec.lc_env)

let opath (cs : t) =
  try Some (path cs) with NoSectionOpened -> None

let topenv (cs : t) : EcEnv.env =
  match List.rev cs with
  | [] -> raise NoSectionOpened
  | ec :: _ -> ec.lc_env

let locals (cs : t) : locals =
  match cs with
  | [] -> raise NoSectionOpened
  | ec :: _ -> ec

let olocals (cs : t) =
  try Some (locals cs) with NoSectionOpened -> None

let onactive (f : locals -> locals) (cs : t) =
  match cs with
  | []      -> raise NoSectionOpened
  | c :: cs -> (f c) :: cs

let add_local_mod (p : path) (cs : t) : t =
  onactive (fun ec -> { ec with lc_modules = Sp.add p ec.lc_modules }) cs

let add_lemma (p : path) (lvl : lvl) (cs : t) : t =
  onactive (fun ec ->
    let (axs, map) = ec.lc_lemmas in
      { ec with lc_lemmas = ((p, lvl) :: axs, Mp.add p lvl map) })
    cs

let add_item item (cs : t) : t =
  let doit ec = { ec with lc_items = item :: ec.lc_items } in
    onactive doit cs

let add_abstract id mt (cs : t) : t =
  let doit ec =
    match Sid.mem id (snd ec.lc_abstracts) with
    | true  -> assert false
    | false ->
        let (ids, set) = ec.lc_abstracts in
        let (ids, set) = ((id, mt) :: ids, Sid.add id set) in
          { ec with lc_abstracts = (ids, set) }
  in
    onactive doit cs
