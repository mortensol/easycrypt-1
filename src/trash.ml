
(* -------------------------------------------------------------------- *)
let maybe_add_to_section scope item =
  match EcSection.opath scope.sc_section with
  | None -> scope
  | Some (_, sp) -> begin
      match EcPath.p_equal sp (EcEnv.root scope.sc_env) with
      | false -> scope
      | true  ->
        let ec = EcSection.add_item item scope.sc_section in
          { scope with sc_section = ec }
  end


(* AX:
    let scope =
      match EcSection.opath scope.sc_section with
      | None -> scope
      | Some _ ->
          let lvl1 = if local then `Local else `Global in
          let lvl2 = if is_axiom ax.ax_kind then `Axiom else `Lemma in

          if lvl2 = `Axiom && ax.ax_tparams <> [] then
            hierror "axiom must be monomorphic in sections";

          let axpath = EcPath.pqname (path scope) x in
          let ec = EcSection.add_lemma axpath (lvl1, lvl2) scope.sc_section in
            { scope with sc_section = ec }
    in
      scope


(*
    if not (ax.pa_locality = Local) then begin (* FIXME: section *)
      match EcSection.olocals scope.sc_section with
      | None -> ()
      | Some locals ->
        match EcSection.form_use_local concl locals with
        | Some mp ->
          let ppe = EcPrinting.PPEnv.ofenv scope.sc_env in
          hierror "@[<hov>this lemma uses local modules : %a@\n and must be declared as local@]" (EcPrinting.pp_topmod ppe) mp
        | None -> ()
      end;
    if (ax.pa_locality = Local) && EcDecl.is_axiom axd.ax_kind then (* FIXME: section *)
      hierror "an axiom cannot be local";



    if ax.pa_locality = Local && not (EcSection.in_section scope.sc_section) then (* FIXME: section *)
      hierror "cannot declare a local lemma outside of a section";

*)

OP:
(*
    (match EcSection.olocals scope.sc_section with
     | None -> ()
     | Some locals ->
        if EcSection.opdecl_use_local_or_abs op locals then
          hierror "operators cannot use local/abstracts modules");
*)

MOD:
(*
    in
    let scope = maybe_add_to_section scope (EcTheory.Th_module m) in
    let scope =
      match local with
      | false -> scope
      | true  ->
        let mpath = EcPath.pqname (path scope) m.me_name in
        let env = add_local_restr scope.sc_env (path scope) m in
        let ec = EcSection.add_local_mod mpath scope.sc_section in
        { scope with sc_section = ec; sc_env = env }
    in
      scope

add_concrete:
    if (lc = Local) && not (EcSection.in_section scope.sc_section) then (* FIXME: section *)
      hierror "cannot declare a local module outside of a section";


    if not (lc = Local) then begin (* FIXME: section *)
      match EcSection.olocals scope.sc_section with
      | None -> ()
      | Some locals ->
          if EcSection.module_use_local_or_abs m locals then
            hierror
              "this module uses local/abstracts modules and
               must be declared as local";
    end;

declare:
    if not (EcSection.in_section scope.sc_section) then
      hierror "cannot declare an abstract module outside of a section";

      if lc <> Declare then
        hierror ~loc:(loc decl.ptm_name)
          "abstract module must be flagged with `declare`";

*)

TY:
    (match EcSection.olocals scope.sc_section with
     | None -> ()
     | Some locals ->
        if EcSection.tydecl_use_local_or_abs tydecl locals then
          hierror "types cannot use local/abstracts modules");

RED:
    if EcSection.in_section scope.sc_section then
      hierror "cannot add reduction rule in a section";


*)

(*
 Section:
  match EcSection.opath scope.sc_section with
    | None -> hierror "no section to close"
    | Some (sname, sp) ->
        if not (p_equal sp (EcEnv.root (scope.sc_env))) then
          hierror "cannot close a section containing pending theories";
        if sname <> (omap unloc name) then
          hierror "expecting [%s], not [%s]"
            (match sname with None -> "<empty>" | Some x -> x)
            (match  name with None -> "<empty>" | Some x -> unloc x);
