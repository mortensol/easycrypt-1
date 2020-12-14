(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcModules
open EcEnv
open EcTheory
(* -------------------------------------------------------------------- *)
(*type sc_item =
  | SC_th_item  of theory_item
  | SC_decl_mod of EcIdent.t * module_type * mod_restr
 *)
type sc_item

type t

val sc_th_item  : t -> theory_item -> sc_item
val sc_decl_mod : t -> EcIdent.t * module_type * mod_restr -> sc_item

val initial : t
val add     : sc_item -> t -> t

val enter : env -> EcSymbols.symbol option -> t -> t
val exit  : t -> EcSymbols.symbol option -> env * t * theory_item list

val enter_theory : t -> EcSymbols.symbol -> EcTypes.is_local -> t
val exit_theory  : t -> t

(*val fix_locality : t -> locality -> locality
  val fix_is_local : t -> is_local -> is_local *)
