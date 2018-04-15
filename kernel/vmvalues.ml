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
open Sorts
(* open Cbytecodes *)
open Univ

(*******************************************)
(* Initalization of the abstract machine ***)
(* Necessary for [relaccu_tbl]             *)
(*******************************************)

(*
external init_vm : unit -> unit = "init_coq_vm" [@@bs.call] [@@bs.module "../shims/byterun"]

let _ = init_vm ()
*)

(******************************************************)
(* Abstract data types and utility functions **********)
(******************************************************)

(* Values of the abstract machine *)
type values
let val_of_obj v = ((Obj.obj v):values)
let crazy_val = (val_of_obj (Obj.repr 0))

(* Abstract data *)
type vprod
type vfun
type vfix
type vcofix
type vblock
type arguments

let fun_val v = (Obj.magic v : values)
let fix_val v = (Obj.magic v : values)
let cofix_upd_val v = (Obj.magic v : values)

type vm_env
let fun_env v = (Obj.magic v : vm_env)
let fix_env v = (Obj.magic v : vm_env)
let cofix_env v = (Obj.magic v : vm_env)
let cofix_upd_env v = (Obj.magic v : vm_env)
type vstack = values array

let fun_of_val v = (Obj.magic v : vfun)
