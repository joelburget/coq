(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(*                              EqDecide                               *)
(*   A tactic for deciding propositional equality on inductive types   *)
(*                           by Eduardo Gimenez                        *)
(************************************************************************)

open Eqdecide
open Stdarg

let __coq_plugin_name = "ltac_plugin"

let _ =
  Tacentries.tactic_extend __coq_plugin_name "decide_equality" ~level:0
    Tacentries
    .([TyML
       (TyIdent ("decide", TyIdent ("equality", TyNil)),
        (fun ist -> decideEqualityGoal))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "compare" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("compare",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$c1"),
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                    Names.Id.of_string_soft "$c2"),
                 TyNil))),
        (fun c1 c2 ist -> compare c1 c2))])
