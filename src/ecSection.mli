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
type sc_item =
  | SC_th_item  of theory_item
  | SC_decl_mod of EcIdent.t * module_type * mod_restr

(* -------------------------------------------------------------------- *)
type scenv

val env : scenv -> env

val initial : env -> scenv
val add_item : theory_item -> scenv -> scenv
val add_decl_mod :
  EcIdent.t -> EcModules.module_type -> EcModules.mod_restr -> scenv -> scenv
val add     : sc_item -> scenv -> scenv


val enter_section : EcSymbols.symbol option -> scenv -> scenv
val exit_section  : EcSymbols.symbol option -> scenv -> scenv

val enter_theory : EcSymbols.symbol -> EcTypes.is_local -> scenv -> scenv
val exit_theory  :
  ?clears:EcPath.path list ->
  ?pempty:[ `ClearOnly | `Full | `No ] ->
  scenv -> EcSymbols.symbol * EcTheory.ctheory option * scenv

val import : EcPath.path -> scenv -> scenv

val import_vars : EcPath.mpath -> scenv -> scenv
(*val fix_locality : t -> locality -> locality
  val fix_is_local : t -> is_local -> is_local *)

val require : ?mode:thmode -> EcSymbols.symbol -> ctheory -> scenv -> scenv

val astop : scenv -> scenv
