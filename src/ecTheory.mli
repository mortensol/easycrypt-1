(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcPath
open EcSymbols
open EcDecl
open EcModules

(* -------------------------------------------------------------------- *)
type theory = theory_item list

and theory_item =
  | Th_type      of (symbol * tydecl)
  | Th_operator  of (symbol * operator)
  | Th_axiom     of (symbol * axiom)
  | Th_modtype   of (symbol * module_sig)
  | Th_module    of module_expr
  | Th_theory    of (symbol * (ctheory * thmode))
  | Th_export    of EcPath.path
  | Th_instance  of (ty_params * EcTypes.ty) * tcinstance
  | Th_typeclass of (symbol * typeclass)
  | Th_baserw    of symbol
  | Th_addrw     of EcPath.path * EcPath.path list
  | Th_reduction of (EcPath.path * rule_option * rule option) list
  | Th_auto      of (bool * int * symbol option * path list)

and thsource = {
  ths_base : EcPath.path;
}

and ctheory = {
  cth_items  : theory;
  cth_source : thsource option;
}

and tcinstance = [ `Ring of ring | `Field of field | `General of EcPath.path ]
and thmode     = [ `Abstract | `Concrete ]

and rule_pattern =
  | Rule  of top_rule_pattern * rule_pattern list
  | Int   of EcBigInt.zint
  | Var   of EcIdent.t

and top_rule_pattern =
  [`Op of (EcPath.path * EcTypes.ty list) | `Tuple]

and rule = {
  rl_tyd  : EcDecl.ty_params;
  rl_vars : (EcIdent.t * EcTypes.ty) list;
  rl_cond : EcCoreFol.form list;
  rl_ptn  : rule_pattern;
  rl_tg   : EcCoreFol.form;
  rl_prio : int;
}

and rule_option = {
  ur_delta  : bool;
  ur_eqtrue : bool;
}

(* -------------------------------------------------------------------- *)
val module_comps_of_module_sig_comps:
  module_sig_body -> module_item list

val module_expr_of_module_sig:
  EcIdent.t -> module_type -> module_sig -> mod_restr -> module_expr
