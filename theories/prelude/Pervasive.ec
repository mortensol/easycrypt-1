(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
type unit.

op tt : unit.

(* -------------------------------------------------------------------- *)
type bool.

op false : bool.
op true  : bool.

op [!]  : bool -> bool.
op (||) : bool -> bool -> bool.
op (\/) : bool -> bool -> bool.
op (&&) : bool -> bool -> bool.
op (/\) : bool -> bool -> bool.
op (=>) : bool -> bool -> bool.
op (<=>): bool -> bool -> bool.

(* -------------------------------------------------------------------- *)
op (=) ['a]: 'a -> 'a -> bool.

(* -------------------------------------------------------------------- *)
type int.

(* -------------------------------------------------------------------- *)
type real.

(* -------------------------------------------------------------------- *)
type 'a distr.

op mu: 'a distr -> ('a -> bool) -> real.

(* -------------------------------------------------------------------- *)
op witness : 'a.                (* All types are inhabited in EC *)
