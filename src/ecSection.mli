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
val add     : sc_item -> scenv -> scenv


val enter_section : EcSymbols.symbol option -> scenv -> scenv
val exit_section  : EcSymbols.symbol option -> scenv -> scenv * theory

val enter_theory : EcSymbols.symbol -> EcTypes.is_local -> scenv -> scenv
val exit_theory  :
  ?clears:EcPath.path list ->
  ?pempty:[ `ClearOnly | `Full | `No ] ->
  scenv -> EcSymbols.symbol * EcTheory.ctheory option * scenv


(*val fix_locality : t -> locality -> locality
  val fix_is_local : t -> is_local -> is_local *)
