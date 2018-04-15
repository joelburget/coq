(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
(* open Cbytecodes *)

(** Values *)

type values
type vm_env
type vprod
type vfun
type vfix
type vcofix
type vblock
type arguments
type vstack = values array
(* type to_update *)

val fun_val : vfun -> values
val fix_val : vfix -> values
(* val cofix_upd_val : to_update -> values *)

val fun_env : vfun -> vm_env
val fix_env : vfix -> vm_env
val cofix_env : vcofix -> vm_env
(* val cofix_upd_env : to_update -> vm_env *)

(** Cast a value known to be a function, unsafe in general *)
val fun_of_val : values -> vfun

val crazy_val : values
