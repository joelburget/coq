(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Genarg
open Stdarg
open Tacarg
open Extraargs
open Pcoq.Prim
open Pltac
open Mod_subst
open Names
open Tacexpr
open Glob_ops
open CErrors
open Util
open Termops
open Equality
open Misctypes
open Proofview.Notations
open Vernacinterp

let __coq_plugin_name = "ltac_plugin"

(**********************************************************************)
(* replace, discriminate, injection, simplify_eq                      *)
(* cutrewrite, dependent rewrite                                      *)

let with_delayed_uconstr ist c tac =
  let flags =
    {Pretyping.use_typeclasses = false; solve_unification_constraints = true;
     use_hook = Pfedit.solve_by_implicit_tactic (); fail_evar = false;
     expand_evars = true}
  in
  let c = Tacinterp.type_uconstr ~flags ist c in
  Tacticals.New.tclDELAYEDWITHHOLES false c tac

let replace_in_clause_maybe_by ist c1 c2 cl tac =
  with_delayed_uconstr ist c1
    (fun c1 ->
       replace_in_clause_maybe_by c1 c2 cl
         (Option.map (Tacinterp.tactic_of_value ist) tac))

let replace_term ist dir_opt c cl =
  with_delayed_uconstr ist c (fun c -> replace_term dir_opt c cl)

let _ =
  Tacentries.tactic_extend __coq_plugin_name "replace" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("replace",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_uconstr),
                 Names.Id.of_string_soft "$c1"),
              TyIdent
                ("with",
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                       Names.Id.of_string_soft "$c2"),
                    TyArg
                      (Loc.tag
                         (Extend.TUentry (Genarg.get_arg_tag wit_clause),
                          Names.Id.of_string_soft "$cl"),
                       TyArg
                         (Loc.tag
                            (Extend.TUentry
                               (Genarg.get_arg_tag wit_by_arg_tac),
                             Names.Id.of_string_soft "$tac"),
                          TyNil)))))),
        (fun c1 c2 cl tac ist ->
           replace_in_clause_maybe_by ist c1 c2 cl tac))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "replace_term_left" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("replace",
           TyIdent
             ("->",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_uconstr),
                    Names.Id.of_string_soft "$c"),
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_clause),
                       Names.Id.of_string_soft "$cl"),
                    TyNil)))),
        (fun c cl ist -> replace_term ist (Some true) c cl))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "replace_term_right" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("replace",
           TyIdent
             ("<-",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_uconstr),
                    Names.Id.of_string_soft "$c"),
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_clause),
                       Names.Id.of_string_soft "$cl"),
                    TyNil)))),
        (fun c cl ist -> replace_term ist (Some false) c cl))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "replace_term" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("replace",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_uconstr),
                 Names.Id.of_string_soft "$c"),
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_clause),
                    Names.Id.of_string_soft "$cl"),
                 TyNil))),
        (fun c cl ist -> replace_term ist None c cl))])

let induction_arg_of_quantified_hyp =
  function
    AnonHyp n -> None, ElimOnAnonHyp n
  | NamedHyp id -> None, ElimOnIdent (CAst.make id)

(* Versions *_main must come first!! so that "1" is interpreted as a
   ElimOnAnonHyp and not as a "constr", and "id" is interpreted as a
   ElimOnIdent and not as "constr" *)

let mytclWithHoles tac with_evars c =
  Proofview.Goal.enter
    (fun gl ->
       let env = Tacmach.New.pf_env gl in
       let sigma = Tacmach.New.project gl in
       let (sigma', c) =
         Tactics.force_destruction_arg with_evars env sigma c
       in
       Tacticals.New.tclWITHHOLES with_evars (tac with_evars (Some c)) sigma')

let elimOnConstrWithHoles tac with_evars c =
  Tacticals.New.tclDELAYEDWITHHOLES with_evars c
    (fun c -> tac with_evars (Some (None, ElimOnConstr c)))

let _ =
  Tacentries.tactic_extend __coq_plugin_name "simplify_eq" ~level:0
    Tacentries
    .([TyML
       (TyIdent ("simplify_eq", TyNil),
        (fun ist -> dEq ~keep_proofs:None false None));
     TyML
       (TyIdent
          ("simplify_eq",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_destruction_arg),
                 Names.Id.of_string_soft "$c"),
              TyNil)),
        (fun c ist -> mytclWithHoles (dEq ~keep_proofs:None) false c))])
let _ =
  Tacentries.tactic_extend __coq_plugin_name "esimplify_eq" ~level:0
    Tacentries
    .([TyML
       (TyIdent ("esimplify_eq", TyNil),
        (fun ist -> dEq ~keep_proofs:None true None));
     TyML
       (TyIdent
          ("esimplify_eq",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_destruction_arg),
                 Names.Id.of_string_soft "$c"),
              TyNil)),
        (fun c ist -> mytclWithHoles (dEq ~keep_proofs:None) true c))])

let discr_main c = elimOnConstrWithHoles discr_tac false c

let _ =
  Tacentries.tactic_extend __coq_plugin_name "discriminate" ~level:0
    Tacentries
    .([TyML
       (TyIdent ("discriminate", TyNil), (fun ist -> discr_tac false None));
     TyML
       (TyIdent
          ("discriminate",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_destruction_arg),
                 Names.Id.of_string_soft "$c"),
              TyNil)),
        (fun c ist -> mytclWithHoles discr_tac false c))])
let _ =
  Tacentries.tactic_extend __coq_plugin_name "ediscriminate" ~level:0
    Tacentries
    .([TyML
       (TyIdent ("ediscriminate", TyNil), (fun ist -> discr_tac true None));
     TyML
       (TyIdent
          ("ediscriminate",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_destruction_arg),
                 Names.Id.of_string_soft "$c"),
              TyNil)),
        (fun c ist -> mytclWithHoles discr_tac true c))])

let discrHyp id =
  (>>=) Proofview.tclEVARMAP
    (fun sigma ->
       discr_main (fun env sigma -> sigma, (EConstr.mkVar id, NoBindings)))

let injection_main with_evars c =
  elimOnConstrWithHoles (injClause None None) with_evars c

let _ =
  Tacentries.tactic_extend __coq_plugin_name "injection" ~level:0
    Tacentries
    .([TyML
       (TyIdent ("injection", TyNil),
        (fun ist -> injClause None None false None));
     TyML
       (TyIdent
          ("injection",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_destruction_arg),
                 Names.Id.of_string_soft "$c"),
              TyNil)),
        (fun c ist -> mytclWithHoles (injClause None None) false c))])
let _ =
  Tacentries.tactic_extend __coq_plugin_name "einjection" ~level:0
    Tacentries
    .([TyML
       (TyIdent ("einjection", TyNil),
        (fun ist -> injClause None None true None));
     TyML
       (TyIdent
          ("einjection",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_destruction_arg),
                 Names.Id.of_string_soft "$c"),
              TyNil)),
        (fun c ist -> mytclWithHoles (injClause None None) true c))])
let _ =
  Tacentries.tactic_extend __coq_plugin_name "injection_as" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("injection",
           TyIdent
             ("as",
              TyArg
                (Loc.tag
                   (Extend.TUlist0
                      (Extend.TUentry (Genarg.get_arg_tag wit_intropattern)),
                    Names.Id.of_string_soft "$ipat"),
                 TyNil))),
        (fun ipat ist -> injClause None (Some ipat) false None));
     TyML
       (TyIdent
          ("injection",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_destruction_arg),
                 Names.Id.of_string_soft "$c"),
              TyIdent
                ("as",
                 TyArg
                   (Loc.tag
                      (Extend.TUlist0
                         (Extend.TUentry
                            (Genarg.get_arg_tag wit_intropattern)),
                       Names.Id.of_string_soft "$ipat"),
                    TyNil)))),
        (fun c ipat ist ->
           mytclWithHoles (injClause None (Some ipat)) false c))])
let _ =
  Tacentries.tactic_extend __coq_plugin_name "einjection_as" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("einjection",
           TyIdent
             ("as",
              TyArg
                (Loc.tag
                   (Extend.TUlist0
                      (Extend.TUentry (Genarg.get_arg_tag wit_intropattern)),
                    Names.Id.of_string_soft "$ipat"),
                 TyNil))),
        (fun ipat ist -> injClause None (Some ipat) true None));
     TyML
       (TyIdent
          ("einjection",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_destruction_arg),
                 Names.Id.of_string_soft "$c"),
              TyIdent
                ("as",
                 TyArg
                   (Loc.tag
                      (Extend.TUlist0
                         (Extend.TUentry
                            (Genarg.get_arg_tag wit_intropattern)),
                       Names.Id.of_string_soft "$ipat"),
                    TyNil)))),
        (fun c ipat ist ->
           mytclWithHoles (injClause None (Some ipat)) true c))])
let _ =
  Tacentries.tactic_extend __coq_plugin_name "simple_injection" ~level:0
    Tacentries
    .([TyML
       (TyIdent ("simple", TyIdent ("injection", TyNil)),
        (fun ist -> simpleInjClause None false None));
     TyML
       (TyIdent
          ("simple",
           TyIdent
             ("injection",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_destruction_arg),
                    Names.Id.of_string_soft "$c"),
                 TyNil))),
        (fun c ist -> mytclWithHoles (simpleInjClause None) false c))])

let injHyp id =
  (>>=) Proofview.tclEVARMAP
    (fun sigma ->
       injection_main false
         (fun env sigma -> sigma, (EConstr.mkVar id, NoBindings)))

let _ =
  Tacentries.tactic_extend __coq_plugin_name "dependent_rewrite" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("dependent",
           TyIdent
             ("rewrite",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_orient),
                    Names.Id.of_string_soft "$b"),
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                       Names.Id.of_string_soft "$c"),
                    TyNil)))),
        (fun b c ist -> rewriteInConcl b c));
     TyML
       (TyIdent
          ("dependent",
           TyIdent
             ("rewrite",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_orient),
                    Names.Id.of_string_soft "$b"),
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                       Names.Id.of_string_soft "$c"),
                    TyIdent
                      ("in",
                       TyArg
                         (Loc.tag
                            (Extend.TUentry (Genarg.get_arg_tag wit_var),
                             Names.Id.of_string_soft "$id"),
                          TyNil)))))),
        (fun b c id ist -> rewriteInHyp b c id))])

(** To be deprecated?, "cutrewrite (t=u) as <-" is equivalent to
    "replace u with t" or "enough (t=u) as <-" and
    "cutrewrite (t=u) as ->" is equivalent to "enough (t=u) as ->". *)

let _ =
  Tacentries.tactic_extend __coq_plugin_name "cut_rewrite" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("cutrewrite",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_orient),
                 Names.Id.of_string_soft "$b"),
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                    Names.Id.of_string_soft "$eqn"),
                 TyNil))),
        (fun b eqn ist -> cutRewriteInConcl b eqn));
     TyML
       (TyIdent
          ("cutrewrite",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_orient),
                 Names.Id.of_string_soft "$b"),
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                    Names.Id.of_string_soft "$eqn"),
                 TyIdent
                   ("in",
                    TyArg
                      (Loc.tag
                         (Extend.TUentry (Genarg.get_arg_tag wit_var),
                          Names.Id.of_string_soft "$id"),
                       TyNil))))),
        (fun b eqn id ist -> cutRewriteInHyp b eqn id))])

(**********************************************************************)
(* Decompose                                                          *)

let _ =
  Tacentries.tactic_extend __coq_plugin_name "decompose_sum" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("decompose",
           TyIdent
             ("sum",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                    Names.Id.of_string_soft "$c"),
                 TyNil))),
        (fun c ist -> Elim.h_decompose_or c))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "decompose_record" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("decompose",
           TyIdent
             ("record",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                    Names.Id.of_string_soft "$c"),
                 TyNil))),
        (fun c ist -> Elim.h_decompose_and c))])

(**********************************************************************)
(* Contradiction                                                      *)

open Contradiction

let _ =
  Tacentries.tactic_extend __coq_plugin_name "absurd" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("absurd",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$c"),
              TyNil)),
        (fun c ist -> absurd c))])

let onSomeWithHoles tac =
  function
    None -> tac None
  | Some c ->
      Tacticals.New.tclDELAYEDWITHHOLES false c (fun c -> tac (Some c))

let _ =
  Tacentries.tactic_extend __coq_plugin_name "contradiction" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("contradiction",
           TyArg
             (Loc.tag
                (Extend.TUopt
                   (Extend.TUentry
                      (Genarg.get_arg_tag wit_constr_with_bindings)),
                 Names.Id.of_string_soft "$c"),
              TyNil)),
        (fun c ist -> onSomeWithHoles contradiction c))])

(**********************************************************************)
(* AutoRewrite                                                        *)

open Autorewrite

let pr_orient _prc _prlc _prt =
  function
    true -> Pp.mt ()
  | false -> Pp.str " <-"

let pr_orient_string _prc _prlc _prt (orient, s) =
  (++) ((++) (pr_orient _prc _prlc _prt orient) (Pp.spc ())) (Pp.str s)

let wit_orient_string = Genarg.make0 "orient_string"
let _ =
  Genintern.register_intern0 wit_orient_string
    (fun ist v ->
       let ans =
         out_gen (Genarg.glbwit (Genarg.wit_pair wit_bool wit_string))
           (Tacintern.intern_genarg ist
              (Genarg.in_gen
                 (Genarg.rawwit (Genarg.wit_pair wit_bool wit_string)) v))
       in
       ist, ans)
let _ =
  Genintern.register_subst0 wit_orient_string
    (fun s x ->
       out_gen (Genarg.glbwit (Genarg.wit_pair wit_bool wit_string))
         (Tacsubst.subst_genarg s
            (Genarg.in_gen
               (Genarg.glbwit (Genarg.wit_pair wit_bool wit_string)) x)))
let _ =
  Geninterp.register_interp0 wit_orient_string
    (fun ist x ->
       Tacinterp.interp_genarg ist
         (Genarg.in_gen (Genarg.glbwit (Genarg.wit_pair wit_bool wit_string))
            x))
let _ =
  Geninterp.register_val0 wit_orient_string
    (Some
       (Geninterp.val_tag
          (Genarg.topwit (Genarg.wit_pair wit_bool wit_string))))
let orient_string =
  let orient_string =
    Pcoq.create_generic_entry Pcoq.utactic "orient_string"
      (Genarg.rawwit wit_orient_string)
  in
  let () =
    Pcoq.grammar_extend orient_string None
      (None,
       [None, None,
        [Extend.Rule
           (Extend.Next
              (Extend.Next (Extend.Stop, Extend.Aentry orient),
               Extend.Aentry preident),
            (fun i r loc -> r, i))]])
  in
  orient_string
let _ =
  Pptactic.declare_extra_genarg_pprule wit_orient_string pr_orient_string
    pr_orient_string pr_orient_string;
  Tacentries.create_ltac_quotation "orient_string"
    (fun (loc, v) ->
       Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit_orient_string) v))
    (orient_string, None)

let _ =
  Tacentries.tactic_extend __coq_plugin_name "autorewrite" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("autorewrite",
           TyIdent
             ("with",
              TyArg
                (Loc.tag
                   (Extend.TUlist1
                      (Extend.TUentry (Genarg.get_arg_tag wit_preident)),
                    Names.Id.of_string_soft "$l"),
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_clause),
                       Names.Id.of_string_soft "$cl"),
                    TyNil)))),
        (fun l cl ist -> auto_multi_rewrite l cl));
     TyML
       (TyIdent
          ("autorewrite",
           TyIdent
             ("with",
              TyArg
                (Loc.tag
                   (Extend.TUlist1
                      (Extend.TUentry (Genarg.get_arg_tag wit_preident)),
                    Names.Id.of_string_soft "$l"),
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_clause),
                       Names.Id.of_string_soft "$cl"),
                    TyIdent
                      ("using",
                       TyArg
                         (Loc.tag
                            (Extend.TUentry (Genarg.get_arg_tag wit_tactic),
                             Names.Id.of_string_soft "$t"),
                          TyNil)))))),
        (fun l cl t ist ->
           auto_multi_rewrite_with (Tacinterp.tactic_of_value ist t) l cl))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "autorewrite_star" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("autorewrite",
           TyIdent
             ("*",
              TyIdent
                ("with",
                 TyArg
                   (Loc.tag
                      (Extend.TUlist1
                         (Extend.TUentry (Genarg.get_arg_tag wit_preident)),
                       Names.Id.of_string_soft "$l"),
                    TyArg
                      (Loc.tag
                         (Extend.TUentry (Genarg.get_arg_tag wit_clause),
                          Names.Id.of_string_soft "$cl"),
                       TyNil))))),
        (fun l cl ist -> auto_multi_rewrite ~conds:AllMatches l cl));
     TyML
       (TyIdent
          ("autorewrite",
           TyIdent
             ("*",
              TyIdent
                ("with",
                 TyArg
                   (Loc.tag
                      (Extend.TUlist1
                         (Extend.TUentry (Genarg.get_arg_tag wit_preident)),
                       Names.Id.of_string_soft "$l"),
                    TyArg
                      (Loc.tag
                         (Extend.TUentry (Genarg.get_arg_tag wit_clause),
                          Names.Id.of_string_soft "$cl"),
                       TyIdent
                         ("using",
                          TyArg
                            (Loc.tag
                               (Extend.TUentry
                                  (Genarg.get_arg_tag wit_tactic),
                                Names.Id.of_string_soft "$t"),
                             TyNil))))))),
        (fun l cl t ist ->
           auto_multi_rewrite_with ~conds:AllMatches
             (Tacinterp.tactic_of_value ist t) l cl))])

(**********************************************************************)
(* Rewrite star                                                       *)

let rewrite_star ist clause orient occs c (tac : Geninterp.Val.t option) =
  let tac' =
    Option.map (fun t -> Tacinterp.tactic_of_value ist t, FirstSolved) tac
  in
  with_delayed_uconstr ist c
    (fun c ->
       general_rewrite_ebindings_clause clause orient occs ?tac:tac' true true
         (c, NoBindings) true)

let _ =
  Tacentries.tactic_extend __coq_plugin_name "rewrite_star" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("rewrite",
           TyIdent
             ("*",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_orient),
                    Names.Id.of_string_soft "$o"),
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_uconstr),
                       Names.Id.of_string_soft "$c"),
                    TyIdent
                      ("in",
                       TyArg
                         (Loc.tag
                            (Extend.TUentry (Genarg.get_arg_tag wit_var),
                             Names.Id.of_string_soft "$id"),
                          TyIdent
                            ("at",
                             TyArg
                               (Loc.tag
                                  (Extend.TUentry
                                     (Genarg.get_arg_tag wit_occurrences),
                                   Names.Id.of_string_soft "$occ"),
                                TyArg
                                  (Loc.tag
                                     (Extend.TUentry
                                        (Genarg.get_arg_tag wit_by_arg_tac),
                                      Names.Id.of_string_soft "$tac"),
                                   TyNil))))))))),
        (fun o c id occ tac ist ->
           rewrite_star ist (Some id) o (occurrences_of occ) c tac));
     TyML
       (TyIdent
          ("rewrite",
           TyIdent
             ("*",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_orient),
                    Names.Id.of_string_soft "$o"),
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_uconstr),
                       Names.Id.of_string_soft "$c"),
                    TyIdent
                      ("at",
                       TyArg
                         (Loc.tag
                            (Extend.TUentry
                               (Genarg.get_arg_tag wit_occurrences),
                             Names.Id.of_string_soft "$occ"),
                          TyIdent
                            ("in",
                             TyArg
                               (Loc.tag
                                  (Extend.TUentry
                                     (Genarg.get_arg_tag wit_var),
                                   Names.Id.of_string_soft "$id"),
                                TyArg
                                  (Loc.tag
                                     (Extend.TUentry
                                        (Genarg.get_arg_tag wit_by_arg_tac),
                                      Names.Id.of_string_soft "$tac"),
                                   TyNil))))))))),
        (fun o c occ id tac ist ->
           rewrite_star ist (Some id) o (occurrences_of occ) c tac));
     TyML
       (TyIdent
          ("rewrite",
           TyIdent
             ("*",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_orient),
                    Names.Id.of_string_soft "$o"),
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_uconstr),
                       Names.Id.of_string_soft "$c"),
                    TyIdent
                      ("in",
                       TyArg
                         (Loc.tag
                            (Extend.TUentry (Genarg.get_arg_tag wit_var),
                             Names.Id.of_string_soft "$id"),
                          TyArg
                            (Loc.tag
                               (Extend.TUentry
                                  (Genarg.get_arg_tag wit_by_arg_tac),
                                Names.Id.of_string_soft "$tac"),
                             TyNil))))))),
        (fun o c id tac ist ->
           rewrite_star ist (Some id) o Locus.AllOccurrences c tac));
     TyML
       (TyIdent
          ("rewrite",
           TyIdent
             ("*",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_orient),
                    Names.Id.of_string_soft "$o"),
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_uconstr),
                       Names.Id.of_string_soft "$c"),
                    TyIdent
                      ("at",
                       TyArg
                         (Loc.tag
                            (Extend.TUentry
                               (Genarg.get_arg_tag wit_occurrences),
                             Names.Id.of_string_soft "$occ"),
                          TyArg
                            (Loc.tag
                               (Extend.TUentry
                                  (Genarg.get_arg_tag wit_by_arg_tac),
                                Names.Id.of_string_soft "$tac"),
                             TyNil))))))),
        (fun o c occ tac ist ->
           rewrite_star ist None o (occurrences_of occ) c tac));
     TyML
       (TyIdent
          ("rewrite",
           TyIdent
             ("*",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_orient),
                    Names.Id.of_string_soft "$o"),
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_uconstr),
                       Names.Id.of_string_soft "$c"),
                    TyArg
                      (Loc.tag
                         (Extend.TUentry (Genarg.get_arg_tag wit_by_arg_tac),
                          Names.Id.of_string_soft "$tac"),
                       TyNil))))),
        (fun o c tac ist ->
           rewrite_star ist None o Locus.AllOccurrences c tac))])

(**********************************************************************)
(* Hint Rewrite                                                       *)

let add_rewrite_hint ~poly bases ort t lcsr =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let f ce =
    let (c, ctx) = Constrintern.interp_constr env sigma ce in
    let c = EConstr.to_constr sigma c in
    let ctx =
      let ctx = UState.context_set ctx in
      if poly then ctx
      else
        begin
          Declare.declare_universe_context false ctx;
          Univ.ContextSet.empty
        end
    in
    CAst.make ?loc:(Constrexpr_ops.constr_loc ce)
      ((c, ctx), ort, Option.map (in_gen (rawwit wit_ltac)) t)
  in
  let eqs = List.map f lcsr in
  let add_hints base = add_rew_rules base eqs in List.iter add_hints bases

let classify_hint _ = Vernacexpr.VtSideff [], Vernacexpr.VtLater

let _ =
  CList.iteri
    (fun i (depr, f) -> Vernacinterp.vinterp_add depr ("HintRewrite", i) f)
    [false,
     (function
        [o; l; bl] ->
          let o = Genarg.out_gen (Genarg.rawwit wit_orient) o in
          let l =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_list wit_constr)) l
          in
          let bl =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_list wit_preident)) bl
          in
          (fun ~atts ~st ->
             add_rewrite_hint ~poly:atts.polymorphic bl o None l; st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [o; l; t; bl] ->
          let o = Genarg.out_gen (Genarg.rawwit wit_orient) o in
          let l =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_list wit_constr)) l
          in
          let t = Genarg.out_gen (Genarg.rawwit wit_tactic) t in
          let bl =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_list wit_preident)) bl
          in
          (fun ~atts ~st ->
             add_rewrite_hint ~poly:atts.polymorphic bl o (Some t) l; st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [o; l] ->
          let o = Genarg.out_gen (Genarg.rawwit wit_orient) o in
          let l =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_list wit_constr)) l
          in
          (fun ~atts ~st ->
             add_rewrite_hint ~poly:atts.polymorphic ["core"] o None l; st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [o; l; t] ->
          let o = Genarg.out_gen (Genarg.rawwit wit_orient) o in
          let l =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_list wit_constr)) l
          in
          let t = Genarg.out_gen (Genarg.rawwit wit_tactic) t in
          (fun ~atts ~st ->
             add_rewrite_hint ~poly:atts.polymorphic ["core"] o (Some t) l;
             st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("HintRewrite", i) f)
    [(function
        [o; l; bl] -> (fun loc -> classify_hint "HintRewrite")
      | _ -> failwith "Extension: cannot occur");
     (function
        [o; l; t; bl] -> (fun loc -> classify_hint "HintRewrite")
      | _ -> failwith "Extension: cannot occur");
     (function
        [o; l] -> (fun loc -> classify_hint "HintRewrite")
      | _ -> failwith "Extension: cannot occur");
     (function
        [o; l; t] -> (fun loc -> classify_hint "HintRewrite")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("HintRewrite", i) None r)
    [[Egramml.GramTerminal "Hint"; Egramml.GramTerminal "Rewrite";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_orient),
            Extend.Aentry (Pcoq.genarg_grammar wit_orient)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_list wit_constr)),
            Extend.Alist1 (Extend.Aentry (Pcoq.genarg_grammar wit_constr))));
      Egramml.GramTerminal ":";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_list wit_preident)),
            Extend.Alist0
              (Extend.Aentry (Pcoq.genarg_grammar wit_preident))))];
     [Egramml.GramTerminal "Hint"; Egramml.GramTerminal "Rewrite";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_orient),
            Extend.Aentry (Pcoq.genarg_grammar wit_orient)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_list wit_constr)),
            Extend.Alist1 (Extend.Aentry (Pcoq.genarg_grammar wit_constr))));
      Egramml.GramTerminal "using";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_tactic),
            Extend.Aentry (Pcoq.genarg_grammar wit_tactic)));
      Egramml.GramTerminal ":";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_list wit_preident)),
            Extend.Alist0
              (Extend.Aentry (Pcoq.genarg_grammar wit_preident))))];
     [Egramml.GramTerminal "Hint"; Egramml.GramTerminal "Rewrite";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_orient),
            Extend.Aentry (Pcoq.genarg_grammar wit_orient)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_list wit_constr)),
            Extend.Alist1 (Extend.Aentry (Pcoq.genarg_grammar wit_constr))))];
     [Egramml.GramTerminal "Hint"; Egramml.GramTerminal "Rewrite";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_orient),
            Extend.Aentry (Pcoq.genarg_grammar wit_orient)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_list wit_constr)),
            Extend.Alist1 (Extend.Aentry (Pcoq.genarg_grammar wit_constr))));
      Egramml.GramTerminal "using";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_tactic),
            Extend.Aentry (Pcoq.genarg_grammar wit_tactic)))]]

(**********************************************************************)
(* Hint Resolve                                                       *)

open Term
open EConstr
open Vars
open Coqlib

let project_hint ~poly pri l2r r =
  let gr = Smartlocate.global_with_alias r in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, c) = Evd.fresh_global env sigma gr in
  let c = EConstr.of_constr c in
  let t = Retyping.get_type_of env sigma c in
  let t =
    Tacred.reduce_to_quantified_ref env sigma (Lazy.force coq_iff_ref) t
  in
  let (sign, ccl) = decompose_prod_assum sigma t in
  let (a, b) =
    match snd (decompose_app sigma ccl) with
      [a; b] -> a, b
    | _ -> assert false
  in
  let p =
    if l2r then build_coq_iff_left_proj () else build_coq_iff_right_proj ()
  in
  let (sigma, p) = Evd.fresh_global env sigma p in
  let p = EConstr.of_constr p in
  let c =
    Reductionops.whd_beta sigma
      (mkApp (c, Context.Rel.to_extended_vect mkRel 0 sign))
  in
  let c =
    it_mkLambda_or_LetIn
      (mkApp (p, [| mkArrow a (lift 1 b); mkArrow b (lift 1 a); c |])) sign
  in
  let id =
    Nameops.add_suffix (Nametab.basename_of_global gr)
      ("_proj_" ^ (if l2r then "l2r" else "r2l"))
  in
  let ctx = Evd.const_univ_entry ~poly sigma in
  let c = EConstr.to_constr sigma c in
  let c =
    Declare.declare_definition ~internal:Declare.InternalTacticRequest id
      (c, ctx)
  in
  let info = {Vernacexpr.hint_priority = pri; hint_pattern = None} in
  info, false, true, Hints.PathAny, Hints.IsGlobRef (Globnames.ConstRef c)

let add_hints_iff ~atts l2r lc n bl =
  let open Vernacinterp in
  Hints.add_hints (Locality.make_module_locality atts.locality) bl
    (Hints.HintsResolveEntry
       (List.map (project_hint ~poly:atts.polymorphic n l2r) lc))

let _ =
  CList.iteri
    (fun i (depr, f) ->
       Vernacinterp.vinterp_add depr ("HintResolveIffLR", i) f)
    [false,
     (function
        [lc; n; bl] ->
          let lc =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_list wit_global)) lc
          in
          let n =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_opt wit_natural)) n
          in
          let bl =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_list wit_preident)) bl
          in
          (fun ~atts ~st -> add_hints_iff ~atts true lc n bl; st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [lc; n] ->
          let lc =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_list wit_global)) lc
          in
          let n =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_opt wit_natural)) n
          in
          (fun ~atts ~st -> add_hints_iff ~atts true lc n ["core"]; st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("HintResolveIffLR", i) f)
    [(function
        [lc; n; bl] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "HintResolveIffLR")
      | _ -> failwith "Extension: cannot occur");
     (function
        [lc; n] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "HintResolveIffLR")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("HintResolveIffLR", i) None r)
    [[Egramml.GramTerminal "Hint"; Egramml.GramTerminal "Resolve";
      Egramml.GramTerminal "->";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_list wit_global)),
            Extend.Alist1 (Extend.Aentry (Pcoq.genarg_grammar wit_global))));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_opt wit_natural)),
            Extend.Aopt (Extend.Aentry (Pcoq.genarg_grammar wit_natural))));
      Egramml.GramTerminal ":";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_list wit_preident)),
            Extend.Alist0
              (Extend.Aentry (Pcoq.genarg_grammar wit_preident))))];
     [Egramml.GramTerminal "Hint"; Egramml.GramTerminal "Resolve";
      Egramml.GramTerminal "->";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_list wit_global)),
            Extend.Alist1 (Extend.Aentry (Pcoq.genarg_grammar wit_global))));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_opt wit_natural)),
            Extend.Aopt (Extend.Aentry (Pcoq.genarg_grammar wit_natural))))]]

let _ =
  CList.iteri
    (fun i (depr, f) ->
       Vernacinterp.vinterp_add depr ("HintResolveIffRL", i) f)
    [false,
     (function
        [lc; n; bl] ->
          let lc =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_list wit_global)) lc
          in
          let n =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_opt wit_natural)) n
          in
          let bl =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_list wit_preident)) bl
          in
          (fun ~atts ~st -> add_hints_iff ~atts false lc n bl; st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [lc; n] ->
          let lc =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_list wit_global)) lc
          in
          let n =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_opt wit_natural)) n
          in
          (fun ~atts ~st -> add_hints_iff ~atts false lc n ["core"]; st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("HintResolveIffRL", i) f)
    [(function
        [lc; n; bl] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "HintResolveIffRL")
      | _ -> failwith "Extension: cannot occur");
     (function
        [lc; n] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "HintResolveIffRL")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("HintResolveIffRL", i) None r)
    [[Egramml.GramTerminal "Hint"; Egramml.GramTerminal "Resolve";
      Egramml.GramTerminal "<-";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_list wit_global)),
            Extend.Alist1 (Extend.Aentry (Pcoq.genarg_grammar wit_global))));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_opt wit_natural)),
            Extend.Aopt (Extend.Aentry (Pcoq.genarg_grammar wit_natural))));
      Egramml.GramTerminal ":";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_list wit_preident)),
            Extend.Alist0
              (Extend.Aentry (Pcoq.genarg_grammar wit_preident))))];
     [Egramml.GramTerminal "Hint"; Egramml.GramTerminal "Resolve";
      Egramml.GramTerminal "<-";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_list wit_global)),
            Extend.Alist1 (Extend.Aentry (Pcoq.genarg_grammar wit_global))));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_opt wit_natural)),
            Extend.Aopt (Extend.Aentry (Pcoq.genarg_grammar wit_natural))))]]

(**********************************************************************)
(* Refine                                                             *)

open EConstr
open Vars

let constr_flags () =
  {Pretyping.use_typeclasses = true;
   Pretyping.solve_unification_constraints = true;
   Pretyping.use_hook = Pfedit.solve_by_implicit_tactic ();
   Pretyping.fail_evar = false; Pretyping.expand_evars = true}

let refine_tac ist simple with_classes c =
  Proofview.Goal.enter
    (fun gl ->
       let concl = Proofview.Goal.concl gl in
       let env = Proofview.Goal.env gl in
       let flags =
         {(constr_flags ()) with Pretyping.use_typeclasses = with_classes}
       in
       let expected_type = Pretyping.OfType concl in
       let c = Tacinterp.type_uconstr ~flags ~expected_type ist c in
       let update sigma = c env sigma in
       let refine = Refine.refine ~typecheck:false update in
       if simple then refine
       else
         (<*>) ((<*>) refine Tactics.New.reduce_after_refine)
           Proofview.shelve_unifiable)

let _ =
  Tacentries.tactic_extend __coq_plugin_name "refine" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("refine",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_uconstr),
                 Names.Id.of_string_soft "$c"),
              TyNil)),
        (fun c ist -> refine_tac ist false true c))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "simple_refine" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("simple",
           TyIdent
             ("refine",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_uconstr),
                    Names.Id.of_string_soft "$c"),
                 TyNil))),
        (fun c ist -> refine_tac ist true true c))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "notcs_refine" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("notypeclasses",
           TyIdent
             ("refine",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_uconstr),
                    Names.Id.of_string_soft "$c"),
                 TyNil))),
        (fun c ist -> refine_tac ist false false c))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "notcs_simple_refine" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("simple",
           TyIdent
             ("notypeclasses",
              TyIdent
                ("refine",
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_uconstr),
                       Names.Id.of_string_soft "$c"),
                    TyNil)))),
        (fun c ist -> refine_tac ist true false c))])

(* Solve unification constraints using heuristics or fail if any remain *)
let _ =
  Tacentries.tactic_extend __coq_plugin_name "solve_constraints" ~level:0
    Tacentries
    .([TyML
       (TyIdent ("solve_constraints", TyNil),
        (fun ist -> Refine.solve_constraints))])

(**********************************************************************)
(* Inversion lemmas (Leminv)                                          *)

open Inv
open Leminv

let seff id = Vernacexpr.VtSideff [id], Vernacexpr.VtLater

(*VERNAC ARGUMENT EXTEND sort_family
| [ "Set" ] -> [ InSet ]
| [ "Prop" ] -> [ InProp ]
| [ "Type" ] -> [ InType ]
END*)

let _ =
  (*VERNAC ARGUMENT EXTEND sort_family
  | [ "Set" ] -> [ InSet ]
  | [ "Prop" ] -> [ InProp ]
  | [ "Type" ] -> [ InType ]
  END*)

  CList.iteri
    (fun i (depr, f) ->
       (*VERNAC ARGUMENT EXTEND sort_family
       | [ "Set" ] -> [ InSet ]
       | [ "Prop" ] -> [ InProp ]
       | [ "Type" ] -> [ InType ]
       END*)

       Vernacinterp.vinterp_add depr ("DeriveInversionClear", i) f)
    [(*VERNAC ARGUMENT EXTEND sort_family
     | [ "Set" ] -> [ InSet ]
     | [ "Prop" ] -> [ InProp ]
     | [ "Type" ] -> [ InType ]
     END*)

     false,
     (function
        [na; c; s] ->
          let na = Genarg.out_gen (Genarg.rawwit wit_ident) na in
          let c = Genarg.out_gen (Genarg.rawwit wit_constr) c in
          let s = Genarg.out_gen (Genarg.rawwit wit_sort_family) s in
          (fun ~atts ~st ->
             let open Vernacinterp in
             begin
               add_inversion_lemma_exn ~poly:atts.polymorphic na c s false
                 inv_clear_tac;
               st
             end)
      | _ ->
          (*VERNAC ARGUMENT EXTEND sort_family
          | [ "Set" ] -> [ InSet ]
          | [ "Prop" ] -> [ InProp ]
          | [ "Type" ] -> [ InType ]
          END*)

          failwith "Extension: cannot occur");
     (*VERNAC ARGUMENT EXTEND sort_family
     | [ "Set" ] -> [ InSet ]
     | [ "Prop" ] -> [ InProp ]
     | [ "Type" ] -> [ InType ]
     END*)

     false,
     (function
        [na; c] ->
          let na = Genarg.out_gen (Genarg.rawwit wit_ident) na in
          let c = Genarg.out_gen (Genarg.rawwit wit_constr) c in
          (fun ~atts ~st ->
             let open Vernacinterp in
             begin
               add_inversion_lemma_exn ~poly:atts.polymorphic na c
                 Sorts.InProp false inv_clear_tac;
               st
             end)
      | _ ->
          (*VERNAC ARGUMENT EXTEND sort_family
          | [ "Set" ] -> [ InSet ]
          | [ "Prop" ] -> [ InProp ]
          | [ "Type" ] -> [ InType ]
          END*)

          failwith "Extension: cannot occur")];
  (*VERNAC ARGUMENT EXTEND sort_family
  | [ "Set" ] -> [ InSet ]
  | [ "Prop" ] -> [ InProp ]
  | [ "Type" ] -> [ InType ]
  END*)

  CList.iteri
    (fun i f ->
       (*VERNAC ARGUMENT EXTEND sort_family
       | [ "Set" ] -> [ InSet ]
       | [ "Prop" ] -> [ InProp ]
       | [ "Type" ] -> [ InType ]
       END*)

       Vernac_classifier.declare_vernac_classifier ("DeriveInversionClear", i)
         f)
    [(*VERNAC ARGUMENT EXTEND sort_family
     | [ "Set" ] -> [ InSet ]
     | [ "Prop" ] -> [ InProp ]
     | [ "Type" ] -> [ InType ]
     END*)

     (function
        [na; c; s] ->
          let na = Genarg.out_gen (Genarg.rawwit wit_ident) na in
          let c = Genarg.out_gen (Genarg.rawwit wit_constr) c in
          let s = Genarg.out_gen (Genarg.rawwit wit_sort_family) s in
          let _ = let _ = na in let _ = c in let _ = s in () in
          (fun loc -> seff na)
      | _ ->
          (*VERNAC ARGUMENT EXTEND sort_family
          | [ "Set" ] -> [ InSet ]
          | [ "Prop" ] -> [ InProp ]
          | [ "Type" ] -> [ InType ]
          END*)

          failwith "Extension: cannot occur");
     (*VERNAC ARGUMENT EXTEND sort_family
     | [ "Set" ] -> [ InSet ]
     | [ "Prop" ] -> [ InProp ]
     | [ "Type" ] -> [ InType ]
     END*)

     (function
        [na; c] ->
          let na = Genarg.out_gen (Genarg.rawwit wit_ident) na in
          let c = Genarg.out_gen (Genarg.rawwit wit_constr) c in
          let _ = let _ = na in let _ = c in () in (fun loc -> seff na)
      | _ ->
          (*VERNAC ARGUMENT EXTEND sort_family
          | [ "Set" ] -> [ InSet ]
          | [ "Prop" ] -> [ InProp ]
          | [ "Type" ] -> [ InType ]
          END*)

          failwith "Extension: cannot occur")];
  (*VERNAC ARGUMENT EXTEND sort_family
  | [ "Set" ] -> [ InSet ]
  | [ "Prop" ] -> [ InProp ]
  | [ "Type" ] -> [ InType ]
  END*)

  CList.iteri
    (fun i r ->
       (*VERNAC ARGUMENT EXTEND sort_family
       | [ "Set" ] -> [ InSet ]
       | [ "Prop" ] -> [ InProp ]
       | [ "Type" ] -> [ InType ]
       END*)

       Egramml.extend_vernac_command_grammar ("DeriveInversionClear", i) None
         r)
    [[Egramml.GramTerminal "Derive"; Egramml.GramTerminal "Inversion_clear";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)));
      Egramml.GramTerminal "with";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "Sort";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_sort_family),
            Extend.Aentry (Pcoq.genarg_grammar wit_sort_family)))];
     [Egramml.GramTerminal "Derive"; Egramml.GramTerminal "Inversion_clear";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)));
      Egramml.GramTerminal "with";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)))]]

let _ =
  CList.iteri
    (fun i (depr, f) ->
       Vernacinterp.vinterp_add depr ("DeriveInversion", i) f)
    [false,
     (function
        [na; c; s] ->
          let na = Genarg.out_gen (Genarg.rawwit wit_ident) na in
          let c = Genarg.out_gen (Genarg.rawwit wit_constr) c in
          let s = Genarg.out_gen (Genarg.rawwit wit_sort_family) s in
          (fun ~atts ~st ->
             let open Vernacinterp in
             begin
               add_inversion_lemma_exn ~poly:atts.polymorphic na c s false
                 inv_tac;
               st
             end)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [na; c] ->
          let na = Genarg.out_gen (Genarg.rawwit wit_ident) na in
          let c = Genarg.out_gen (Genarg.rawwit wit_constr) c in
          (fun ~atts ~st ->
             let open Vernacinterp in
             begin
               add_inversion_lemma_exn ~poly:atts.polymorphic na c
                 Sorts.InProp false inv_tac;
               st
             end)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("DeriveInversion", i) f)
    [(function
        [na; c; s] ->
          let na = Genarg.out_gen (Genarg.rawwit wit_ident) na in
          let c = Genarg.out_gen (Genarg.rawwit wit_constr) c in
          let s = Genarg.out_gen (Genarg.rawwit wit_sort_family) s in
          let _ = let _ = na in let _ = c in let _ = s in () in
          (fun loc -> seff na)
      | _ -> failwith "Extension: cannot occur");
     (function
        [na; c] ->
          let na = Genarg.out_gen (Genarg.rawwit wit_ident) na in
          let c = Genarg.out_gen (Genarg.rawwit wit_constr) c in
          let _ = let _ = na in let _ = c in () in (fun loc -> seff na)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("DeriveInversion", i) None r)
    [[Egramml.GramTerminal "Derive"; Egramml.GramTerminal "Inversion";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)));
      Egramml.GramTerminal "with";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "Sort";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_sort_family),
            Extend.Aentry (Pcoq.genarg_grammar wit_sort_family)))];
     [Egramml.GramTerminal "Derive"; Egramml.GramTerminal "Inversion";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)));
      Egramml.GramTerminal "with";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)))]]

let _ =
  CList.iteri
    (fun i (depr, f) ->
       Vernacinterp.vinterp_add depr ("DeriveDependentInversion", i) f)
    [false,
     (function
        [na; c; s] ->
          let na = Genarg.out_gen (Genarg.rawwit wit_ident) na in
          let c = Genarg.out_gen (Genarg.rawwit wit_constr) c in
          let s = Genarg.out_gen (Genarg.rawwit wit_sort_family) s in
          (fun ~atts ~st ->
             let open Vernacinterp in
             begin
               add_inversion_lemma_exn ~poly:atts.polymorphic na c s true
                 dinv_tac;
               st
             end)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier
         ("DeriveDependentInversion", i) f)
    [(function
        [na; c; s] ->
          let na = Genarg.out_gen (Genarg.rawwit wit_ident) na in
          let c = Genarg.out_gen (Genarg.rawwit wit_constr) c in
          let s = Genarg.out_gen (Genarg.rawwit wit_sort_family) s in
          let _ = let _ = na in let _ = c in let _ = s in () in
          (fun loc -> seff na)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("DeriveDependentInversion", i)
         None r)
    [[Egramml.GramTerminal "Derive"; Egramml.GramTerminal "Dependent";
      Egramml.GramTerminal "Inversion";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)));
      Egramml.GramTerminal "with";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "Sort";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_sort_family),
            Extend.Aentry (Pcoq.genarg_grammar wit_sort_family)))]]

let _ =
  CList.iteri
    (fun i (depr, f) ->
       Vernacinterp.vinterp_add depr ("DeriveDependentInversionClear", i) f)
    [false,
     (function
        [na; c; s] ->
          let na = Genarg.out_gen (Genarg.rawwit wit_ident) na in
          let c = Genarg.out_gen (Genarg.rawwit wit_constr) c in
          let s = Genarg.out_gen (Genarg.rawwit wit_sort_family) s in
          (fun ~atts ~st ->
             let open Vernacinterp in
             begin
               add_inversion_lemma_exn ~poly:atts.polymorphic na c s true
                 dinv_clear_tac;
               st
             end)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier
         ("DeriveDependentInversionClear", i) f)
    [(function
        [na; c; s] ->
          let na = Genarg.out_gen (Genarg.rawwit wit_ident) na in
          let c = Genarg.out_gen (Genarg.rawwit wit_constr) c in
          let s = Genarg.out_gen (Genarg.rawwit wit_sort_family) s in
          let _ = let _ = na in let _ = c in let _ = s in () in
          (fun loc -> seff na)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar
         ("DeriveDependentInversionClear", i) None r)
    [[Egramml.GramTerminal "Derive"; Egramml.GramTerminal "Dependent";
      Egramml.GramTerminal "Inversion_clear";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)));
      Egramml.GramTerminal "with";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "Sort";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_sort_family),
            Extend.Aentry (Pcoq.genarg_grammar wit_sort_family)))]]

(**********************************************************************)
(* Subst                                                              *)

let _ =
  Tacentries.tactic_extend __coq_plugin_name "subst" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("subst",
           TyArg
             (Loc.tag
                (Extend.TUlist1 (Extend.TUentry (Genarg.get_arg_tag wit_var)),
                 Names.Id.of_string_soft "$l"),
              TyNil)),
        (fun l ist -> subst l));
     TyML (TyIdent ("subst", TyNil), (fun ist -> subst_all ()))])

let simple_subst_tactic_flags =
  {only_leibniz = true; rewrite_dependent_proof = false}

let _ =
  Tacentries.tactic_extend __coq_plugin_name "simple_subst" ~level:0
    Tacentries
    .([TyML
       (TyIdent ("simple", TyIdent ("subst", TyNil)),
        (fun ist -> subst_all ~flags:simple_subst_tactic_flags ()))])

open Evar_tactics

(**********************************************************************)
(* Evar creation                                                      *)

(* TODO: add support for some test similar to g_constr.name_colon so that
   expressions like "evar (list A)" do not raise a syntax error *)
let _ =
  Tacentries.tactic_extend __coq_plugin_name "evar" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("evar",
           TyAnonArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_test_lpar_id_colon)),
              TyIdent
                ("(",
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_ident),
                       Names.Id.of_string_soft "$id"),
                    TyIdent
                      (":",
                       TyArg
                         (Loc.tag
                            (Extend.TUentry (Genarg.get_arg_tag wit_lconstr),
                             Names.Id.of_string_soft "$typ"),
                          TyIdent (")", TyNil))))))),
        (fun id typ ist -> let_evar (Name.Name id) typ));
     TyML
       (TyIdent
          ("evar",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$typ"),
              TyNil)),
        (fun typ ist -> let_evar Name.Anonymous typ))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "instantiate" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("instantiate",
           TyIdent
             ("(",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_ident),
                    Names.Id.of_string_soft "$id"),
                 TyIdent
                   (":=",
                    TyArg
                      (Loc.tag
                         (Extend.TUentry (Genarg.get_arg_tag wit_lglob),
                          Names.Id.of_string_soft "$c"),
                       TyIdent (")", TyNil)))))),
        (fun id c ist ->
           Tacticals.New.tclTHEN (instantiate_tac_by_name id c)
             Proofview.V82.nf_evar_goals));
     TyML
       (TyIdent
          ("instantiate",
           TyIdent
             ("(",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_integer),
                    Names.Id.of_string_soft "$i"),
                 TyIdent
                   (":=",
                    TyArg
                      (Loc.tag
                         (Extend.TUentry (Genarg.get_arg_tag wit_lglob),
                          Names.Id.of_string_soft "$c"),
                       TyIdent
                         (")",
                          TyArg
                            (Loc.tag
                               (Extend.TUentry (Genarg.get_arg_tag wit_hloc),
                                Names.Id.of_string_soft "$hl"),
                             TyNil))))))),
        (fun i c hl ist ->
           Tacticals.New.tclTHEN (instantiate_tac i c hl)
             Proofview.V82.nf_evar_goals));
     TyML
       (TyIdent ("instantiate", TyNil),
        (fun ist -> Proofview.V82.nf_evar_goals))])

(**********************************************************************)
(** Nijmegen "step" tactic for setoid rewriting                       *)

open Tactics
open Glob_term
open Libobject
open Lib

(* Registered lemmas are expected to be of the form
     x R y -> y == z -> x R z    (in the right table)
     x R y -> x == z -> z R y    (in the left table)
*)

let transitivity_right_table = Summary.ref [] ~name:"transitivity-steps-r"
let transitivity_left_table = Summary.ref [] ~name:"transitivity-steps-l"

(* [step] tries to apply a rewriting lemma; then apply [tac] intended to
   complete to proof of the last hypothesis (assumed to state an equality) *)

let step left x tac =
  let l =
    List.map
      (fun lem ->
         let lem = EConstr.of_constr lem in
         Tacticals.New.tclTHENLAST
           (apply_with_bindings (lem, ImplicitBindings [x])) tac)
      !(if left then transitivity_left_table else transitivity_right_table)
  in
  Tacticals.New.tclFIRST l

(* Main function to push lemmas in persistent environment *)

let cache_transitivity_lemma (_, (left, lem)) =
  if left then transitivity_left_table := lem :: !transitivity_left_table
  else transitivity_right_table := lem :: !transitivity_right_table

let subst_transitivity_lemma (subst, (b, ref)) = b, subst_mps subst ref

let inTransitivity : bool * Constr.t -> obj =
  declare_object
    {(default_object "TRANSITIVITY-STEPS") with cache_function =
      cache_transitivity_lemma;
     open_function =
       (fun i o -> if Int.equal i 1 then cache_transitivity_lemma o);
     subst_function = subst_transitivity_lemma;
     classify_function = fun o -> Substitute o}

(* Main entry points *)

let add_transitivity_lemma left lem =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (lem', ctx) = Constrintern.interp_constr env sigma lem in
  let lem' = EConstr.to_constr sigma lem' in
  add_anonymous_leaf (inTransitivity (left, lem'))

(* Vernacular syntax *)

let _ =
  Tacentries.tactic_extend __coq_plugin_name "stepl" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("stepl",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$c"),
              TyIdent
                ("by",
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_tactic),
                       Names.Id.of_string_soft "$tac"),
                    TyNil)))),
        (fun c tac ist -> step true c (Tacinterp.tactic_of_value ist tac)));
     TyML
       (TyIdent
          ("stepl",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$c"),
              TyNil)),
        (fun c ist -> step true c (Proofview.tclUNIT ())))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "stepr" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("stepr",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$c"),
              TyIdent
                ("by",
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_tactic),
                       Names.Id.of_string_soft "$tac"),
                    TyNil)))),
        (fun c tac ist -> step false c (Tacinterp.tactic_of_value ist tac)));
     TyML
       (TyIdent
          ("stepr",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$c"),
              TyNil)),
        (fun c ist -> step false c (Proofview.tclUNIT ())))])

let _ =
  CList.iteri
    (fun i (depr, f) -> Vernacinterp.vinterp_add depr ("AddStepl", i) f)
    [false,
     (function
        [t] ->
          let t = Genarg.out_gen (Genarg.rawwit wit_constr) t in
          (fun ~atts ~st -> let () = add_transitivity_lemma true t in st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f -> Vernac_classifier.declare_vernac_classifier ("AddStepl", i) f)
    [(function
        [t] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff) "AddStepl")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r -> Egramml.extend_vernac_command_grammar ("AddStepl", i) None r)
    [[Egramml.GramTerminal "Declare"; Egramml.GramTerminal "Left";
      Egramml.GramTerminal "Step";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)))]]

let _ =
  CList.iteri
    (fun i (depr, f) -> Vernacinterp.vinterp_add depr ("AddStepr", i) f)
    [false,
     (function
        [t] ->
          let t = Genarg.out_gen (Genarg.rawwit wit_constr) t in
          (fun ~atts ~st -> let () = add_transitivity_lemma false t in st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f -> Vernac_classifier.declare_vernac_classifier ("AddStepr", i) f)
    [(function
        [t] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff) "AddStepr")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r -> Egramml.extend_vernac_command_grammar ("AddStepr", i) None r)
    [[Egramml.GramTerminal "Declare"; Egramml.GramTerminal "Right";
      Egramml.GramTerminal "Step";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)))]]

let cache_implicit_tactic (_, tac) =
  match tac with
    Some tac -> Pfedit.declare_implicit_tactic (Tacinterp.eval_tactic tac)
  | None -> Pfedit.clear_implicit_tactic ()

let subst_implicit_tactic (subst, tac) =
  Option.map (Tacsubst.subst_tactic subst) tac

let inImplicitTactic : glob_tactic_expr option -> obj =
  declare_object
    {(default_object "IMPLICIT-TACTIC") with open_function =
      (fun i o -> if Int.equal i 1 then cache_implicit_tactic o);
     cache_function = cache_implicit_tactic;
     subst_function = subst_implicit_tactic;
     classify_function = fun o -> Dispose}

let declare_implicit_tactic tac =
  Lib.add_anonymous_leaf (inImplicitTactic (Some (Tacintern.glob_tactic tac)))

let clear_implicit_tactic () = Lib.add_anonymous_leaf (inImplicitTactic None)

let _ =
  CList.iteri
    (fun i (depr, f) -> Vernacinterp.vinterp_add depr ("ImplicitTactic", i) f)
    [false,
     (function
        [tac] ->
          let tac = Genarg.out_gen (Genarg.rawwit wit_tactic) tac in
          (fun ~atts ~st -> let () = declare_implicit_tactic tac in st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [] -> (fun ~atts ~st -> let () = clear_implicit_tactic () in st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("ImplicitTactic", i) f)
    [(function
        [tac] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "ImplicitTactic")
      | _ -> failwith "Extension: cannot occur");
     (function
        [] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "ImplicitTactic")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("ImplicitTactic", i) None r)
    [[Egramml.GramTerminal "Declare"; Egramml.GramTerminal "Implicit";
      Egramml.GramTerminal "Tactic";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_tactic),
            Extend.Aentry (Pcoq.genarg_grammar wit_tactic)))];
     [Egramml.GramTerminal "Clear"; Egramml.GramTerminal "Implicit";
      Egramml.GramTerminal "Tactic"]]




(*
(**********************************************************************)
(*spiwack : Vernac commands for retroknowledge                        *)

let _ =
  (**********************************************************************)
  (*spiwack : Vernac commands for retroknowledge                        *)

  CList.iteri
    (fun i (depr, f) ->
       (**********************************************************************)
       (*spiwack : Vernac commands for retroknowledge                        *)

       Vernacinterp.vinterp_add depr ("RetroknowledgeRegister", i) f)
    [(**********************************************************************)
     (*spiwack : Vernac commands for retroknowledge                        *)

     false,
     (function
        [c; f; b] ->
          let c = Genarg.out_gen (Genarg.rawwit wit_constr) c in
          let f = Genarg.out_gen (Genarg.rawwit wit_retroknowledge_field) f in
          let b = Genarg.out_gen (Genarg.rawwit wit_constr) b in
          (fun ~atts ~st ->
             let () =
               let (tc, _ctx) =
                 Constrintern.interp_constr (Global.env ()) Evd.empty c
               in
               let (tb, _ctx) =
                 Constrintern.interp_constr (Global.env ()) Evd.empty b
               in
               let tc = EConstr.to_constr Evd.empty tc in
               let tb = EConstr.to_constr Evd.empty tb in
               Global.register f tc tb
             in
             st)
      | _ ->
          (**********************************************************************)
          (*spiwack : Vernac commands for retroknowledge                        *)

          failwith "Extension: cannot occur")];
  (**********************************************************************)
  (*spiwack : Vernac commands for retroknowledge                        *)

  CList.iteri
    (fun i f ->
       (**********************************************************************)
       (*spiwack : Vernac commands for retroknowledge                        *)

       Vernac_classifier.declare_vernac_classifier
         ("RetroknowledgeRegister", i) f)
    [(**********************************************************************)
     (*spiwack : Vernac commands for retroknowledge                        *)

     (function
        [c; f; b] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "RetroknowledgeRegister")
      | _ ->
          (**********************************************************************)
          (*spiwack : Vernac commands for retroknowledge                        *)

          failwith "Extension: cannot occur")];
  (**********************************************************************)
  (*spiwack : Vernac commands for retroknowledge                        *)

  CList.iteri
    (fun i r ->
       (**********************************************************************)
       (*spiwack : Vernac commands for retroknowledge                        *)

       Egramml.extend_vernac_command_grammar ("RetroknowledgeRegister", i)
         None r)
    [[Egramml.GramTerminal "Register";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "as";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_retroknowledge_field),
            Extend.Aentry (Pcoq.genarg_grammar wit_retroknowledge_field)));
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)))]]
*)


(**********************************************************************)
(* sozeau: abs/gen for induction on instantiated dependent inductives, using "Ford" induction as
  defined by Conor McBride *)
let _ =
  Tacentries.tactic_extend __coq_plugin_name "generalize_eqs" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("generalize_eqs",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_var),
                 Names.Id.of_string_soft "$id"),
              TyNil)),
        (fun id ist -> abstract_generalize ~generalize_vars:false id))])
let _ =
  Tacentries.tactic_extend __coq_plugin_name "dep_generalize_eqs" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("dependent",
           TyIdent
             ("generalize_eqs",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_var),
                    Names.Id.of_string_soft "$id"),
                 TyNil))),
        (fun id ist ->
           abstract_generalize ~generalize_vars:false ~force_dep:true id))])
let _ =
  Tacentries.tactic_extend __coq_plugin_name "generalize_eqs_vars" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("generalize_eqs_vars",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_var),
                 Names.Id.of_string_soft "$id"),
              TyNil)),
        (fun id ist -> abstract_generalize ~generalize_vars:true id))])
let _ =
  Tacentries.tactic_extend __coq_plugin_name "dep_generalize_eqs_vars"
    ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("dependent",
           TyIdent
             ("generalize_eqs_vars",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_var),
                    Names.Id.of_string_soft "$id"),
                 TyNil))),
        (fun id ist ->
           abstract_generalize ~force_dep:true ~generalize_vars:true id))])

(** Tactic to automatically simplify hypotheses of the form [Π Δ, x_i = t_i -> T]
    where [t_i] is closed w.r.t. Δ. Such hypotheses are automatically generated
    during dependent induction. For internal use. *)

let _ =
  Tacentries.tactic_extend __coq_plugin_name "specialize_eqs" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("specialize_eqs",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_var),
                 Names.Id.of_string_soft "$id"),
              TyNil)),
        (fun id ist -> specialize_eqs id))])

(**********************************************************************)
(* A tactic that considers a given occurrence of [c] in [t] and       *)
(* abstract the minimal set of all the occurrences of [c] so that the *)
(* abstraction [fun x -> t[x/c]] is well-typed                        *)
(*                                                                    *)
(* Contributed by Chung-Kil Hur (Winter 2009)                         *)
(**********************************************************************)

let subst_var_with_hole occ tid t =
  let occref =
    if occ > 0 then ref occ else Find_subterm.error_invalid_occurrence [occ]
  in
  let locref = ref 0 in
  let rec substrec x =
    match DAst.get x with
      GVar id ->
        if Id.equal id tid then
          begin
            decr occref;
            if Int.equal !occref 0 then x
            else
              begin
                incr locref;
                (@@) (DAst.make ~loc:(Loc.make_loc (!locref, 0)))
                  (GHole
                     (Evar_kinds.QuestionMark
                        (Evar_kinds.Define true, Anonymous),
                      Misctypes.IntroAnonymous, None))
              end
          end
        else x
    | _ -> map_glob_constr_left_to_right substrec x
  in
  let t' = substrec t in
  if !occref > 0 then Find_subterm.error_invalid_occurrence [occ] else t'

let subst_hole_with_term occ tc t =
  let locref = ref 0 in
  let occref = ref occ in
  let rec substrec c =
    match DAst.get c with
      GHole
        (Evar_kinds.QuestionMark (Evar_kinds.Define true, Anonymous),
         Misctypes.IntroAnonymous, s) ->
        decr occref;
        if Int.equal !occref 0 then tc
        else
          begin
            incr locref;
            (@@) (DAst.make ~loc:(Loc.make_loc (!locref, 0)))
              (GHole
                 (Evar_kinds.QuestionMark (Evar_kinds.Define true, Anonymous),
                  Misctypes.IntroAnonymous, s))
          end
    | _ -> map_glob_constr_left_to_right substrec c
  in
  substrec t

open Tacmach

let hResolve id c occ t =
  Proofview.Goal.enter
    (fun gl ->
       let sigma = Proofview.Goal.sigma gl in
       let env = Termops.clear_named_body id (Proofview.Goal.env gl) in
       let concl = Proofview.Goal.concl gl in
       let env_ids = Termops.vars_of_env env in
       let c_raw = Detyping.detype Detyping.Now true env_ids env sigma c in
       let t_raw = Detyping.detype Detyping.Now true env_ids env sigma t in
       let rec resolve_hole t_hole =
         try Pretyping.understand env sigma t_hole with
           Pretype_errors.PretypeError
             (_, _, Pretype_errors.UnsolvableImplicit _) as e ->
             let (e, info) = CErrors.push e in
             let loc_begin =
               Option.cata (fun l -> fst (Loc.unloc l)) 0 (Loc.get_loc info)
             in
             resolve_hole (subst_hole_with_term loc_begin c_raw t_hole)
       in
       let (t_constr, ctx) =
         resolve_hole (subst_var_with_hole occ id t_raw)
       in
       let sigma = Evd.merge_universe_context sigma ctx in
       let t_constr_type = Retyping.get_type_of env sigma t_constr in
       Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
         (change_concl
            (mkLetIn (Name.Anonymous, t_constr, t_constr_type, concl))))

let hResolve_auto id c t =
  let rec resolve_auto n =
    try hResolve id c n t with
      UserError _ as e -> raise e
    | e when CErrors.noncritical e -> resolve_auto (n + 1)
  in
  resolve_auto 1

let _ =
  Tacentries.tactic_extend __coq_plugin_name "hresolve_core" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("hresolve_core",
           TyIdent
             ("(",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_ident),
                    Names.Id.of_string_soft "$id"),
                 TyIdent
                   (":=",
                    TyArg
                      (Loc.tag
                         (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                          Names.Id.of_string_soft "$c"),
                       TyIdent
                         (")",
                          TyIdent
                            ("at",
                             TyArg
                               (Loc.tag
                                  (Extend.TUentry
                                     (Genarg.get_arg_tag wit_int_or_var),
                                   Names.Id.of_string_soft "$occ"),
                                TyIdent
                                  ("in",
                                   TyArg
                                     (Loc.tag
                                        (Extend.TUentry
                                           (Genarg.get_arg_tag wit_constr),
                                         Names.Id.of_string_soft "$t"),
                                      TyNil)))))))))),
        (fun id c occ t ist -> hResolve id c occ t));
     TyML
       (TyIdent
          ("hresolve_core",
           TyIdent
             ("(",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_ident),
                    Names.Id.of_string_soft "$id"),
                 TyIdent
                   (":=",
                    TyArg
                      (Loc.tag
                         (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                          Names.Id.of_string_soft "$c"),
                       TyIdent
                         (")",
                          TyIdent
                            ("in",
                             TyArg
                               (Loc.tag
                                  (Extend.TUentry
                                     (Genarg.get_arg_tag wit_constr),
                                   Names.Id.of_string_soft "$t"),
                                TyNil)))))))),
        (fun id c t ist -> hResolve_auto id c t))])

(**
   hget_evar
*)

let _ =
  Tacentries.tactic_extend __coq_plugin_name "hget_evar" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("hget_evar",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var),
                 Names.Id.of_string_soft "$n"),
              TyNil)),
        (fun n ist -> Evar_tactics.hget_evar n))])

(**********************************************************************)

(**********************************************************************)
(* A tactic that reduces one match t with ... by doing destruct t.    *)
(* if t is not a variable, the tactic does                            *)
(* case_eq t;intros ... heq;rewrite heq in *|-. (but heq itself is    *)
(* preserved).                                                        *)
(* Contributed by Julien Forest and Pierre Courtieu (july 2010)       *)
(**********************************************************************)

exception Found of unit Proofview.tactic

let rewrite_except h =
  Proofview.Goal.enter
    (fun gl ->
       let hyps = Tacmach.New.pf_ids_of_hyps gl in
       Tacticals.New.tclMAP
         (fun id ->
            if Id.equal id h then Proofview.tclUNIT ()
            else
              Tacticals.New.tclTRY
                (Equality.general_rewrite_in true Locus.AllOccurrences true
                   true id (mkVar h) false))
         hyps)


let refl_equal =
  let coq_base_constant s =
    Coqlib.gen_reference_in_modules "RecursiveDefinition"
      (Coqlib.init_modules @ [["Coq"; "Arith"; "Le"]; ["Coq"; "Arith"; "Lt"]])
      s
  in
  fun () -> coq_base_constant "eq_refl"


(* This is simply an implementation of the case_eq tactic.  this code
  should be replaced by a call to the tactic but I don't know how to
  call it before it is defined. *)
let mkCaseEq a : unit Proofview.tactic =
  Proofview.Goal.enter
    (fun gl ->
       let type_of_a = Tacmach.New.pf_unsafe_type_of gl a in
       (>>=) (Tacticals.New.pf_constr_of_global (delayed_force refl_equal))
         (fun req ->
            Tacticals.New.tclTHENLIST
              [Tactics.generalize [mkApp (req, [| type_of_a; a |])];
               Proofview.Goal.enter
                 (fun gl ->
                    let concl = Proofview.Goal.concl gl in
                    let env = Proofview.Goal.env gl in
                    (** FIXME: this looks really wrong. Does anybody really use this tactic? *)
                    let (_, c) =
                      Tacred.pattern_occs [Locus.OnlyOccurrences [1], a] env
                        Evd.empty concl
                    in
                    change_concl c);
               simplest_case a]))


let case_eq_intros_rewrite x =
  Proofview.Goal.enter
    (fun gl ->
       let n = nb_prod (Tacmach.New.project gl) (Proofview.Goal.concl gl) in
       (* Pp.msgnl (Printer.pr_lconstr x); *)
       Tacticals.New.tclTHENLIST
         [mkCaseEq x;
          Proofview.Goal.enter
            (fun gl ->
               let concl = Proofview.Goal.concl gl in
               let hyps = Tacmach.New.pf_ids_set_of_hyps gl in
               let n' = nb_prod (Tacmach.New.project gl) concl in
               let h =
                 fresh_id_in_env hyps (Id.of_string "heq")
                   (Proofview.Goal.env gl)
               in
               Tacticals.New.tclTHENLIST
                 [Tacticals.New.tclDO (n' - n - 1) intro; introduction h;
                  rewrite_except h])])

let rec find_a_destructable_match sigma t =
  let cl = induction_arg_of_quantified_hyp (NamedHyp (Id.of_string "x")) in
  let cl = [cl, (None, None), None], None in
  let dest =
    TacAtom ((@@) Loc.tag (TacInductionDestruct (false, false, cl)))
  in
  match EConstr.kind sigma t with
    Case (_, _, x, _) when closed0 sigma x ->
      if isVar sigma x then raise (Found (Tacinterp.eval_tactic dest))
      else raise (Found (case_eq_intros_rewrite x))
  | _ -> EConstr.iter sigma (fun c -> find_a_destructable_match sigma c) t


let destauto t =
  (>>=) Proofview.tclEVARMAP
    (fun sigma ->
       try
         find_a_destructable_match sigma t;
         Tacticals.New.tclZEROMSG (str "No destructable match found")
       with Found tac -> tac)

let destauto_in id =
  Proofview.Goal.enter
    (fun gl ->
       let ctype = Tacmach.New.pf_unsafe_type_of gl (mkVar id) in
       (*  Pp.msgnl (Printer.pr_lconstr (mkVar id)); *)
       (*  Pp.msgnl (Printer.pr_lconstr (ctype)); *)
       destauto ctype)

let _ =
  Tacentries.tactic_extend __coq_plugin_name "destauto" ~level:0
    Tacentries
    .([TyML
       (TyIdent ("destauto", TyNil),
        (fun ist ->
           Proofview.Goal.enter
             (fun gl -> destauto (Proofview.Goal.concl gl))));
     TyML
       (TyIdent
          ("destauto",
           TyIdent
             ("in",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_var),
                    Names.Id.of_string_soft "$id"),
                 TyNil))),
        (fun id ist -> destauto_in id))])

(**********************************************************************)

(**********************************************************************)
(* A version of abstract constructing transparent terms               *)
(* Introduced by Jason Gross and Benjamin Delaware in June 2016       *)
(**********************************************************************)

let _ =
  Tacentries.tactic_extend __coq_plugin_name "transparent_abstract" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("transparent_abstract",
           TyArg
             (Loc.tag
                (Extend.TUentryl (Genarg.get_arg_tag wit_tactic, 3),
                 Names.Id.of_string_soft "$t"),
              TyNil)),
        (fun t ist ->
           Proofview.Goal.nf_enter
             (fun gl ->
                Tactics.tclABSTRACT ~opaque:false None
                  (Tacinterp.tactic_of_value ist t))));
     TyML
       (TyIdent
          ("transparent_abstract",
           TyArg
             (Loc.tag
                (Extend.TUentryl (Genarg.get_arg_tag wit_tactic, 3),
                 Names.Id.of_string_soft "$t"),
              TyIdent
                ("using",
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_ident),
                       Names.Id.of_string_soft "$id"),
                    TyNil)))),
        (fun t id ist ->
           Proofview.Goal.nf_enter
             (fun gl ->
                Tactics.tclABSTRACT ~opaque:false (Some id)
                  (Tacinterp.tactic_of_value ist t))))])

(* ********************************************************************* *)

let eq_constr x y =
  Proofview.Goal.enter
    (fun gl ->
       let env = Tacmach.New.pf_env gl in
       let evd = Tacmach.New.project gl in
       match EConstr.eq_constr_universes env evd x y with
         Some _ -> Proofview.tclUNIT ()
       | None -> Tacticals.New.tclFAIL 0 (str "Not equal"))

let _ =
  Tacentries.tactic_extend __coq_plugin_name "constr_eq" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("constr_eq",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$x"),
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                    Names.Id.of_string_soft "$y"),
                 TyNil))),
        (fun x y ist -> eq_constr x y))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "constr_eq_nounivs" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("constr_eq_nounivs",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$x"),
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                    Names.Id.of_string_soft "$y"),
                 TyNil))),
        (fun x y ist ->
           (>>=) Proofview.tclEVARMAP
             (fun sigma ->
                if eq_constr_nounivs sigma x y then Proofview.tclUNIT ()
                else Tacticals.New.tclFAIL 0 (str "Not equal"))))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "is_evar" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("is_evar",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$x"),
              TyNil)),
        (fun x ist ->
           (>>=) Proofview.tclEVARMAP
             (fun sigma ->
                match EConstr.kind sigma x with
                  Evar _ -> Proofview.tclUNIT ()
                | _ -> Tacticals.New.tclFAIL 0 (str "Not an evar"))))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "has_evar" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("has_evar",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$x"),
              TyNil)),
        (fun x ist ->
           (>>=) Proofview.tclEVARMAP
             (fun sigma ->
                if Evarutil.has_undefined_evars sigma x then
                  Proofview.tclUNIT ()
                else Tacticals.New.tclFAIL 0 (str "No evars"))))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "is_hyp" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("is_var",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$x"),
              TyNil)),
        (fun x ist ->
           (>>=) Proofview.tclEVARMAP
             (fun sigma ->
                match EConstr.kind sigma x with
                  Var _ -> Proofview.tclUNIT ()
                | _ ->
                    Tacticals.New.tclFAIL 0
                      (str "Not a variable or hypothesis"))))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "is_fix" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("is_fix",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$x"),
              TyNil)),
        (fun x ist ->
           (>>=) Proofview.tclEVARMAP
             (fun sigma ->
                match EConstr.kind sigma x with
                  Fix _ -> Proofview.tclUNIT ()
                | _ ->
                    Tacticals.New.tclFAIL 0
                      (Pp.str "not a fix definition"))))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "is_cofix" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("is_cofix",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$x"),
              TyNil)),
        (fun x ist ->
           (>>=) Proofview.tclEVARMAP
             (fun sigma ->
                match EConstr.kind sigma x with
                  CoFix _ -> Proofview.tclUNIT ()
                | _ ->
                    Tacticals.New.tclFAIL 0
                      (Pp.str "not a cofix definition"))))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "is_ind" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("is_ind",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$x"),
              TyNil)),
        (fun x ist ->
           (>>=) Proofview.tclEVARMAP
             (fun sigma ->
                match EConstr.kind sigma x with
                  Ind _ -> Proofview.tclUNIT ()
                | _ ->
                    Tacticals.New.tclFAIL 0
                      (Pp.str "not an (co)inductive datatype"))))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "is_constructor" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("is_constructor",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$x"),
              TyNil)),
        (fun x ist ->
           (>>=) Proofview.tclEVARMAP
             (fun sigma ->
                match EConstr.kind sigma x with
                  Construct _ -> Proofview.tclUNIT ()
                | _ ->
                    Tacticals.New.tclFAIL 0 (Pp.str "not a constructor"))))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "is_proj" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("is_proj",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$x"),
              TyNil)),
        (fun x ist ->
           (>>=) Proofview.tclEVARMAP
             (fun sigma ->
                match EConstr.kind sigma x with
                  Proj _ -> Proofview.tclUNIT ()
                | _ ->
                    Tacticals.New.tclFAIL 0
                      (Pp.str "not a primitive projection"))))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "is_const" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("is_const",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$x"),
              TyNil)),
        (fun x ist ->
           (>>=) Proofview.tclEVARMAP
             (fun sigma ->
                match EConstr.kind sigma x with
                  Const _ -> Proofview.tclUNIT ()
                | _ -> Tacticals.New.tclFAIL 0 (Pp.str "not a constant"))))])

(* Command to grab the evars left unresolved at the end of a proof. *)
(* spiwack: I put it in extratactics because it is somewhat tied with
   the semantics of the LCF-style tactics, hence with the classic tactic
   mode. *)
let _ =
  (* Command to grab the evars left unresolved at the end of a proof. *)
  (* spiwack: I put it in extratactics because it is somewhat tied with
     the semantics of the LCF-style tactics, hence with the classic tactic
     mode. *)
  CList.iteri
    (fun i (depr, f) ->
       (* Command to grab the evars left unresolved at the end of a proof. *)
       (* spiwack: I put it in extratactics because it is somewhat tied with
          the semantics of the LCF-style tactics, hence with the classic tactic
          mode. *)
       Vernacinterp.vinterp_add depr ("GrabEvars", i) f)
    [(* Command to grab the evars left unresolved at the end of a proof. *)
     (* spiwack: I put it in extratactics because it is somewhat tied with
        the semantics of the LCF-style tactics, hence with the classic tactic
        mode. *)
     false,
     (function
        [] ->
          (fun ~atts ~st ->
             let () =
               Proof_global.simple_with_current_proof
                 (fun _ p -> Proof.V82.grab_evars p)
             in
             st)
      | _ ->
          (* Command to grab the evars left unresolved at the end of a proof. *)
          (* spiwack: I put it in extratactics because it is somewhat tied with
             the semantics of the LCF-style tactics, hence with the classic tactic
             mode. *)
          failwith "Extension: cannot occur")];
  (* Command to grab the evars left unresolved at the end of a proof. *)
  (* spiwack: I put it in extratactics because it is somewhat tied with
     the semantics of the LCF-style tactics, hence with the classic tactic
     mode. *)
  CList.iteri
    (fun i f ->
       (* Command to grab the evars left unresolved at the end of a proof. *)
       (* spiwack: I put it in extratactics because it is somewhat tied with
          the semantics of the LCF-style tactics, hence with the classic tactic
          mode. *)
       Vernac_classifier.declare_vernac_classifier ("GrabEvars", i) f)
    [(* Command to grab the evars left unresolved at the end of a proof. *)
     (* spiwack: I put it in extratactics because it is somewhat tied with
        the semantics of the LCF-style tactics, hence with the classic tactic
        mode. *)
     (function
        [] ->
          let _ = () in (fun loc -> Vernac_classifier.classify_as_proofstep)
      | _ ->
          (* Command to grab the evars left unresolved at the end of a proof. *)
          (* spiwack: I put it in extratactics because it is somewhat tied with
             the semantics of the LCF-style tactics, hence with the classic tactic
             mode. *)
          failwith "Extension: cannot occur")];
  (* Command to grab the evars left unresolved at the end of a proof. *)
  (* spiwack: I put it in extratactics because it is somewhat tied with
     the semantics of the LCF-style tactics, hence with the classic tactic
     mode. *)
  CList.iteri
    (fun i r ->
       (* Command to grab the evars left unresolved at the end of a proof. *)
       (* spiwack: I put it in extratactics because it is somewhat tied with
          the semantics of the LCF-style tactics, hence with the classic tactic
          mode. *)
       Egramml.extend_vernac_command_grammar ("GrabEvars", i) None r)
    [[Egramml.GramTerminal "Grab"; Egramml.GramTerminal "Existential";
      Egramml.GramTerminal "Variables"]]

(* Shelves all the goals under focus. *)
let _ =
  Tacentries.tactic_extend __coq_plugin_name "shelve" ~level:0
    Tacentries
    .([TyML (TyIdent ("shelve", TyNil), (fun ist -> Proofview.shelve))])

(* Shelves the unifiable goals under focus, i.e. the goals which
   appear in other goals under focus (the unfocused goals are not
   considered). *)
let _ =
  Tacentries.tactic_extend __coq_plugin_name "shelve_unifiable" ~level:0
    Tacentries
    .([TyML
       (TyIdent ("shelve_unifiable", TyNil),
        (fun ist -> Proofview.shelve_unifiable))])

(* Unshelves the goal shelved by the tactic. *)
let _ =
  Tacentries.tactic_extend __coq_plugin_name "unshelve" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("unshelve",
           TyArg
             (Loc.tag
                (Extend.TUentryl (Genarg.get_arg_tag wit_tactic, 1),
                 Names.Id.of_string_soft "$t"),
              TyNil)),
        (fun t ist ->
           (>>=) (Proofview.with_shelf (Tacinterp.tactic_of_value ist t))
             (fun (gls, ()) ->
                let gls = List.map Proofview.with_empty_state gls in
                (>>=) Proofview.Unsafe.tclGETGOALS
                  (fun ogls -> Proofview.Unsafe.tclSETGOALS (gls @ ogls)))))])

(* Command to add every unshelved variables to the focus *)
let _ =
  (* Command to add every unshelved variables to the focus *)
  CList.iteri
    (fun i (depr, f) ->
       (* Command to add every unshelved variables to the focus *)
       Vernacinterp.vinterp_add depr ("Unshelve", i) f)
    [(* Command to add every unshelved variables to the focus *)
     false,
     (function
        [] ->
          (fun ~atts ~st ->
             let () =
               Proof_global.simple_with_current_proof
                 (fun _ p -> Proof.unshelve p)
             in
             st)
      | _ ->
          (* Command to add every unshelved variables to the focus *)
          failwith "Extension: cannot occur")];
  (* Command to add every unshelved variables to the focus *)
  CList.iteri
    (fun i f ->
       (* Command to add every unshelved variables to the focus *)
       Vernac_classifier.declare_vernac_classifier ("Unshelve", i) f)
    [(* Command to add every unshelved variables to the focus *)
     (function
        [] ->
          let _ = () in (fun loc -> Vernac_classifier.classify_as_proofstep)
      | _ ->
          (* Command to add every unshelved variables to the focus *)
          failwith "Extension: cannot occur")];
  (* Command to add every unshelved variables to the focus *)
  CList.iteri
    (fun i r ->
       (* Command to add every unshelved variables to the focus *)
       Egramml.extend_vernac_command_grammar ("Unshelve", i) None r)
    [[Egramml.GramTerminal "Unshelve"]]

(* Gives up on the goals under focus: the goals are considered solved,
   but the proof cannot be closed until the user goes back and solve
   these goals. *)
let _ =
  Tacentries.tactic_extend __coq_plugin_name "give_up" ~level:0
    Tacentries
    .([TyML (TyIdent ("give_up", TyNil), (fun ist -> Proofview.give_up))])

(* cycles [n] goals *)
let _ =
  Tacentries.tactic_extend __coq_plugin_name "cycle" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("cycle",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var),
                 Names.Id.of_string_soft "$n"),
              TyNil)),
        (fun n ist -> Proofview.cycle n))])

(* swaps goals number [i] and [j] *)
let _ =
  Tacentries.tactic_extend __coq_plugin_name "swap" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("swap",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var),
                 Names.Id.of_string_soft "$i"),
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var),
                    Names.Id.of_string_soft "$j"),
                 TyNil))),
        (fun i j ist -> Proofview.swap i j))])

(* reverses the list of focused goals *)
let _ =
  Tacentries.tactic_extend __coq_plugin_name "revgoals" ~level:0
    Tacentries
    .([TyML (TyIdent ("revgoals", TyNil), (fun ist -> Proofview.revgoals))])

type cmp = Eq | Lt | Le | Gt | Ge

type 'i test =
    Test of cmp * 'i * 'i

let pr_cmp =
  function
    Eq -> Pp.str "="
  | Lt -> Pp.str "<"
  | Le -> Pp.str "<="
  | Gt -> Pp.str ">"
  | Ge -> Pp.str ">="

let pr_cmp' _prc _prlc _prt = pr_cmp

let pr_test_gen f =
  function
    Test (c, x, y) -> Pp.((++) ((++) (f x) (pr_cmp c)) (f y))

let pr_test = pr_test_gen (Pputils.pr_or_var Pp.int)

let pr_test' _prc _prlc _prt = pr_test

let pr_itest = pr_test_gen Pp.int

let pr_itest' _prc _prlc _prt = pr_itest



let wit_comparison = Genarg.make0 "comparison"
let _ = Genintern.register_intern0 wit_comparison (fun ist v -> ist, v)
let _ = Genintern.register_subst0 wit_comparison (fun s v -> v)
let _ =
  Geninterp.register_interp0 wit_comparison
    (fun ist v ->
       Ftactic.return
         (Geninterp.Val.inject
            (Geninterp.val_tag (Genarg.topwit wit_comparison)) v))
let _ = Geninterp.register_val0 wit_comparison None
let comparison =
  let comparison =
    Pcoq.create_generic_entry Pcoq.utactic "comparison"
      (Genarg.rawwit wit_comparison)
  in
  let () =
    Pcoq.grammar_extend comparison None
      (None,
       [None, None,
        [Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Atoken (CLexer.terminal ">=")),
            (fun _ loc -> Ge));
         Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Atoken (CLexer.terminal ">")),
            (fun _ loc -> Gt));
         Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Atoken (CLexer.terminal "<=")),
            (fun _ loc -> Le));
         Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Atoken (CLexer.terminal "<")),
            (fun _ loc -> Lt));
         Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Atoken (CLexer.terminal "=")),
            (fun _ loc -> Eq))]])
  in
  comparison
let _ =
  Pptactic.declare_extra_genarg_pprule wit_comparison pr_cmp' pr_cmp' pr_cmp';
  Tacentries.create_ltac_quotation "comparison"
    (fun (loc, v) ->
       Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit_comparison) v))
    (comparison, None)

let interp_test ist gls =
  function
    Test (c, x, y) ->
      project gls,
      Test
        (c, Tacinterp.interp_int_or_var ist x,
         Tacinterp.interp_int_or_var ist y)

let wit_test = Genarg.make0 "test"
let _ = Genintern.register_intern0 wit_test (fun ist v -> ist, v)
let _ = Genintern.register_subst0 wit_test (fun s v -> v)
let _ =
  Geninterp.register_interp0 wit_test
    (let f = interp_test in
     fun ist v ->
       Ftactic.enter
         (fun gl ->
            let (sigma, v) = Tacmach.New.of_old (fun gl -> f ist gl v) gl in
            let v =
              Geninterp.Val.inject
                (Geninterp.val_tag (Genarg.topwit wit_test)) v
            in
            Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
              (Ftactic.return v)))
let _ = Geninterp.register_val0 wit_test None
let test =
  let test =
    Pcoq.create_generic_entry Pcoq.utactic "test" (Genarg.rawwit wit_test)
  in
  let () =
    Pcoq.grammar_extend test None
      (None,
       [None, None,
        [Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next (Extend.Stop, Extend.Aentry int_or_var),
                  Extend.Aentry comparison),
               Extend.Aentry int_or_var),
            (fun y c x loc -> Test (c, x, y)))]])
  in
  test
let _ =
  Pptactic.declare_extra_genarg_pprule wit_test pr_test' pr_test' pr_itest';
  Tacentries.create_ltac_quotation "test"
    (fun (loc, v) ->
       Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit_test) v))
    (test, None)

let interp_cmp =
  function
    Eq -> Int.equal
  | Lt -> ((<) : int -> int -> bool)
  | Le -> ((<=) : int -> int -> bool)
  | Gt -> ((>) : int -> int -> bool)
  | Ge -> ((>=) : int -> int -> bool)

let run_test =
  function
    Test (c, x, y) -> interp_cmp c x y

let guard tst =
  if run_test tst then Proofview.tclUNIT ()
  else
    let msg =
      Pp.((++) ((++) (str "Condition not satisfied:") (ws 1)) (pr_itest tst))
    in
    Tacticals.New.tclZEROMSG msg


let _ =
  Tacentries.tactic_extend __coq_plugin_name "guard" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("guard",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_test),
                 Names.Id.of_string_soft "$tst"),
              TyNil)),
        (fun tst ist -> guard tst))])

let decompose l c =
  Proofview.Goal.enter
    (fun gl ->
       let sigma = Tacmach.New.project gl in
       let to_ind c =
         if isInd sigma c then fst (destInd sigma c)
         else user_err Pp.(str "not an inductive type")
       in
       let l = List.map to_ind l in Elim.h_decompose l c)

let _ =
  Tacentries.tactic_extend __coq_plugin_name "decompose" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("decompose",
           TyIdent
             ("[",
              TyArg
                (Loc.tag
                   (Extend.TUlist1
                      (Extend.TUentry (Genarg.get_arg_tag wit_constr)),
                    Names.Id.of_string_soft "$l"),
                 TyIdent
                   ("]",
                    TyArg
                      (Loc.tag
                         (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                          Names.Id.of_string_soft "$c"),
                       TyNil))))),
        (fun l c ist -> decompose l c))])

(** library/keys *)

let _ =
  (** library/keys *)

  CList.iteri
    (fun i (depr, f) ->
       (** library/keys *)

       Vernacinterp.vinterp_add depr ("Declare_keys", i) f)
    [(** library/keys *)

     false,
     (function
        [c; c'] ->
          let c = Genarg.out_gen (Genarg.rawwit wit_constr) c in
          let c' = Genarg.out_gen (Genarg.rawwit wit_constr) c' in
          (fun ~atts ~st ->
             let () =
               let get_key c =
                 let (evd, c) =
                   Constrintern.interp_open_constr (Global.env ()) Evd.empty c
                 in
                 let kind c = EConstr.kind evd c in Keys.constr_key kind c
               in
               let k1 = get_key c in
               let k2 = get_key c' in
               match k1, k2 with
                 Some k1, Some k2 -> Keys.declare_equiv_keys k1 k2
               | _ -> ()
             in
             st)
      | _ ->
          (** library/keys *)

          failwith "Extension: cannot occur")];
  (** library/keys *)

  CList.iteri
    (fun i f ->
       (** library/keys *)

       Vernac_classifier.declare_vernac_classifier ("Declare_keys", i) f)
    [(** library/keys *)

     (function
        [c; c'] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff) "Declare_keys")
      | _ ->
          (** library/keys *)

          failwith "Extension: cannot occur")];
  (** library/keys *)

  CList.iteri
    (fun i r ->
       (** library/keys *)

       Egramml.extend_vernac_command_grammar ("Declare_keys", i) None r)
    [[Egramml.GramTerminal "Declare"; Egramml.GramTerminal "Equivalent";
      Egramml.GramTerminal "Keys";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)))]]

let _ =
  CList.iteri
    (fun i (depr, f) -> Vernacinterp.vinterp_add depr ("Print_keys", i) f)
    [false,
     (function
        [] ->
          (fun ~atts ~st ->
             let () = Feedback.msg_info (Keys.pr_keys Printer.pr_global) in
             st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("Print_keys", i) f)
    [(function
        [] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_query) "Print_keys")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("Print_keys", i) None r)
    [[Egramml.GramTerminal "Print"; Egramml.GramTerminal "Equivalent";
      Egramml.GramTerminal "Keys"]]


let _ =
  CList.iteri
    (fun i (depr, f) -> Vernacinterp.vinterp_add depr ("OptimizeProof", i) f)
    [false,
     (function
        [] ->
          (fun ~atts ~st -> let () = Proof_global.compact_the_proof () in st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [] -> (fun ~atts ~st -> let () = Gc.compact () in st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("OptimizeProof", i) f)
    [(function
        [] ->
          let _ = () in (fun loc -> Vernac_classifier.classify_as_proofstep)
      | _ -> failwith "Extension: cannot occur");
     (function
        [] ->
          let _ = () in (fun loc -> Vernac_classifier.classify_as_proofstep)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("OptimizeProof", i) None r)
    [[Egramml.GramTerminal "Optimize"; Egramml.GramTerminal "Proof"];
     [Egramml.GramTerminal "Optimize"; Egramml.GramTerminal "Heap"]]

(** tactic analogous to "OPTIMIZE HEAP" *)

let tclOPTIMIZE_HEAP =
  Proofview.tclLIFT (Proofview.NonLogical.make (fun () -> Gc.compact ()))

let _ =
  Tacentries.tactic_extend __coq_plugin_name "optimize_heap" ~level:0
    Tacentries
    .([TyML
       (TyIdent ("optimize_heap", TyNil), (fun ist -> tclOPTIMIZE_HEAP))])
