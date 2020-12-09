(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcModules

(* -------------------------------------------------------------------- *)
type t

type locality = EcParsetree.locality
open EcTheory

type lc_item =
  | LC_th_item  of ctheory_item
  | LC_decl_mod of EcIdent.t * module_type * mod_restr

val initial : t
val add     : locality -> lc_item -> t -> t
