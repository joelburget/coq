(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Syntax for rewriting with strategies *)

open Names
open Misctypes
open Locus
open Constrexpr
open Glob_term
open Geninterp
open Extraargs
open Tacmach
open Rewrite
open Stdarg
open Pcoq.Vernac_
open Pcoq.Prim
open Pcoq.Constr
open Pltac

let __coq_plugin_name = "ltac_plugin"

type constr_expr_with_bindings = constr_expr with_bindings
type glob_constr_with_bindings = Tacexpr.glob_constr_and_expr with_bindings
type glob_constr_with_bindings_sign =
  interp_sign * Tacexpr.glob_constr_and_expr with_bindings

let pr_glob_constr_with_bindings_sign _ _ _
    (ge : glob_constr_with_bindings_sign) =
  let (_, env) = Pfedit.get_current_context () in
  Printer.pr_glob_constr_env env (fst (fst (snd ge)))
let pr_glob_constr_with_bindings _ _ _ (ge : glob_constr_with_bindings) =
  let (_, env) = Pfedit.get_current_context () in
  Printer.pr_glob_constr_env env (fst (fst ge))
let pr_constr_expr_with_bindings prc _ _ (ge : constr_expr_with_bindings) =
  prc (fst ge)
let interp_glob_constr_with_bindings ist gl c = Tacmach.project gl, (ist, c)
let glob_glob_constr_with_bindings ist l =
  Tacintern.intern_constr_with_bindings ist l
let subst_glob_constr_with_bindings s c =
  Tacsubst.subst_glob_with_bindings s c

let wit_glob_constr_with_bindings = Genarg.make0 "glob_constr_with_bindings"
let _ =
  Genintern.register_intern0 wit_glob_constr_with_bindings
    (fun ist v -> ist, glob_glob_constr_with_bindings ist v)
let _ =
  Genintern.register_subst0 wit_glob_constr_with_bindings
    subst_glob_constr_with_bindings
let _ =
  Geninterp.register_interp0 wit_glob_constr_with_bindings
    (let f = interp_glob_constr_with_bindings in
     fun ist v ->
       Ftactic.enter
         (fun gl ->
            let (sigma, v) = Tacmach.New.of_old (fun gl -> f ist gl v) gl in
            let v =
              Geninterp.Val.inject
                (Geninterp.val_tag
                   (Genarg.topwit wit_glob_constr_with_bindings))
                v
            in
            Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
              (Ftactic.return v)))
let _ = Geninterp.register_val0 wit_glob_constr_with_bindings None
let glob_constr_with_bindings =
  let () =
    Pcoq.register_grammar wit_glob_constr_with_bindings constr_with_bindings
  in
  constr_with_bindings
let _ =
  Pptactic.declare_extra_genarg_pprule wit_glob_constr_with_bindings
    pr_constr_expr_with_bindings pr_glob_constr_with_bindings
    pr_glob_constr_with_bindings_sign;
  Tacentries.create_ltac_quotation "glob_constr_with_bindings"
    (fun (loc, v) ->
       Tacexpr.TacGeneric
         (Genarg.in_gen (Genarg.rawwit wit_glob_constr_with_bindings) v))
    (glob_constr_with_bindings, None)

type raw_strategy = (constr_expr, Tacexpr.raw_red_expr) strategy_ast
type glob_strategy =
  (Tacexpr.glob_constr_and_expr, Tacexpr.raw_red_expr) strategy_ast

let interp_strategy ist gl s =
  let sigma = project gl in sigma, strategy_of_ast s
let glob_strategy ist s =
  map_strategy (Tacintern.intern_constr ist) (fun c -> c) s
let subst_strategy s str = str

let pr_strategy _ _ _ (s : strategy) = Pp.str "<strategy>"
let pr_raw_strategy prc prlc _ (s : raw_strategy) =
  let prr =
    Pptactic.pr_red_expr
      (prc, prlc, Pputils.pr_or_by_notation Libnames.pr_reference, prc)
  in
  Rewrite.pr_strategy prc prr s
let pr_glob_strategy prc prlc _ (s : glob_strategy) =
  let prr =
    Pptactic.pr_red_expr
      (Ppconstr.pr_constr_expr, Ppconstr.pr_lconstr_expr,
       Pputils.pr_or_by_notation Libnames.pr_reference,
       Ppconstr.pr_constr_expr)
  in
  Rewrite.pr_strategy prc prr s

let wit_rewstrategy = Genarg.make0 "rewstrategy"
let _ =
  Genintern.register_intern0 wit_rewstrategy
    (fun ist v -> ist, glob_strategy ist v)
let _ = Genintern.register_subst0 wit_rewstrategy subst_strategy
let _ =
  Geninterp.register_interp0 wit_rewstrategy
    (let f = interp_strategy in
     fun ist v ->
       Ftactic.enter
         (fun gl ->
            let (sigma, v) = Tacmach.New.of_old (fun gl -> f ist gl v) gl in
            let v =
              Geninterp.Val.inject
                (Geninterp.val_tag (Genarg.topwit wit_rewstrategy)) v
            in
            Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
              (Ftactic.return v)))
let _ = Geninterp.register_val0 wit_rewstrategy None
let rewstrategy =
  let rewstrategy =
    Pcoq.create_generic_entry Pcoq.utactic "rewstrategy"
      (Genarg.rawwit wit_rewstrategy)
  in
  let () =
    Pcoq.grammar_extend rewstrategy None
      (None,
       [None, None,
        [Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "fold")),
               Extend.Aentry constr),
            (fun c _ loc -> StratFold c));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "eval")),
               Extend.Aentry red_expr),
            (fun r _ loc -> StratEval r));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "terms")),
               Extend.Alist0 (Extend.Aentry constr)),
            (fun h _ loc -> StratTerms h));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "hints")),
               Extend.Aentry preident),
            (fun h _ loc -> StratHints (false, h)));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "old_hints")),
               Extend.Aentry preident),
            (fun h _ loc -> StratHints (true, h)));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next
                    (Extend.Stop, Extend.Atoken (CLexer.terminal "choice")),
                  Extend.Aentry rewstrategy),
               Extend.Aentry rewstrategy),
            (fun h' h _ loc -> StratBinary (Choice, h, h')));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next
                    (Extend.Stop, Extend.Atoken (CLexer.terminal "(")),
                  Extend.Aentry rewstrategy),
               Extend.Atoken (CLexer.terminal ")")),
            (fun _ h _ loc -> h));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next (Extend.Stop, Extend.Aentry rewstrategy),
                  Extend.Atoken (CLexer.terminal ";")),
               Extend.Aentry rewstrategy),
            (fun h' _ h loc -> StratBinary (Compose, h, h')));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "repeat")),
               Extend.Aentry rewstrategy),
            (fun h _ loc -> StratUnary (Repeat, h)));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "any")),
               Extend.Aentry rewstrategy),
            (fun h _ loc -> StratUnary (Any, h)));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "try")),
               Extend.Aentry rewstrategy),
            (fun h _ loc -> StratUnary (Try, h)));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "progress")),
               Extend.Aentry rewstrategy),
            (fun h _ loc -> StratUnary (Progress, h)));
         Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Atoken (CLexer.terminal "refl")),
            (fun _ loc -> StratRefl));
         Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Atoken (CLexer.terminal "fail")),
            (fun _ loc -> StratFail));
         Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Atoken (CLexer.terminal "id")),
            (fun _ loc -> StratId));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "topdown")),
               Extend.Aentry rewstrategy),
            (fun h _ loc -> StratUnary (Topdown, h)));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "bottomup")),
               Extend.Aentry rewstrategy),
            (fun h _ loc -> StratUnary (Bottomup, h)));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "outermost")),
               Extend.Aentry rewstrategy),
            (fun h _ loc -> StratUnary (Outermost, h)));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "innermost")),
               Extend.Aentry rewstrategy),
            (fun h _ loc -> StratUnary (Innermost, h)));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "subterm")),
               Extend.Aentry rewstrategy),
            (fun h _ loc -> StratUnary (Subterm, h)));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "subterms")),
               Extend.Aentry rewstrategy),
            (fun h _ loc -> StratUnary (Subterms, h)));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "<-")),
               Extend.Aentry constr),
            (fun c _ loc -> StratConstr (c, false)));
         Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Aentry glob),
            (fun c loc -> StratConstr (c, true)))]])
  in
  rewstrategy
let _ =
  Pptactic.declare_extra_genarg_pprule wit_rewstrategy pr_raw_strategy
    pr_glob_strategy pr_strategy;
  Tacentries.create_ltac_quotation "rewstrategy"
    (fun (loc, v) ->
       Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit_rewstrategy) v))
    (rewstrategy, None)

(* By default the strategy for "rewrite_db" is top-down *)

let db_strat db = StratUnary (Topdown, StratHints (false, db))
let cl_rewrite_clause_db db =
  cl_rewrite_clause_strat (strategy_of_ast (db_strat db))

let _ =
  Tacentries.tactic_extend __coq_plugin_name "rewrite_strat" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("rewrite_strat",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_rewstrategy),
                 Names.Id.of_string_soft "$s"),
              TyIdent
                ("in",
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_var),
                       Names.Id.of_string_soft "$id"),
                    TyNil)))),
        (fun s id ist -> cl_rewrite_clause_strat s (Some id)));
     TyML
       (TyIdent
          ("rewrite_strat",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_rewstrategy),
                 Names.Id.of_string_soft "$s"),
              TyNil)),
        (fun s ist -> cl_rewrite_clause_strat s None));
     TyML
       (TyIdent
          ("rewrite_db",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_preident),
                 Names.Id.of_string_soft "$db"),
              TyIdent
                ("in",
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_var),
                       Names.Id.of_string_soft "$id"),
                    TyNil)))),
        (fun db id ist -> cl_rewrite_clause_db db (Some id)));
     TyML
       (TyIdent
          ("rewrite_db",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_preident),
                 Names.Id.of_string_soft "$db"),
              TyNil)),
        (fun db ist -> cl_rewrite_clause_db db None))])

let clsubstitute o c =
  Proofview.Goal.enter
    (fun gl ->
       let is_tac id =
         match DAst.get (fst (fst (snd c))) with
           GVar id' when Id.equal id' id -> true
         | _ -> false
       in
       let hyps = Tacmach.New.pf_ids_of_hyps gl in
       Tacticals.New.tclMAP
         (fun cl ->
            match cl with
              Some id when is_tac id -> Tacticals.New.tclIDTAC
            | _ -> cl_rewrite_clause c o AllOccurrences cl)
         (None :: List.map (fun id -> Some id) hyps))

let _ =
  Tacentries.tactic_extend __coq_plugin_name "substitute" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("substitute",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_orient),
                 Names.Id.of_string_soft "$o"),
              TyArg
                (Loc.tag
                   (Extend.TUentry
                      (Genarg.get_arg_tag wit_glob_constr_with_bindings),
                    Names.Id.of_string_soft "$c"),
                 TyNil))),
        (fun o c ist -> clsubstitute o c))])


(* Compatibility with old Setoids *)

let _ =
  Tacentries.tactic_extend __coq_plugin_name "setoid_rewrite" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("setoid_rewrite",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_orient),
                 Names.Id.of_string_soft "$o"),
              TyArg
                (Loc.tag
                   (Extend.TUentry
                      (Genarg.get_arg_tag wit_glob_constr_with_bindings),
                    Names.Id.of_string_soft "$c"),
                 TyNil))),
        (fun o c ist -> cl_rewrite_clause c o AllOccurrences None));
     TyML
       (TyIdent
          ("setoid_rewrite",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_orient),
                 Names.Id.of_string_soft "$o"),
              TyArg
                (Loc.tag
                   (Extend.TUentry
                      (Genarg.get_arg_tag wit_glob_constr_with_bindings),
                    Names.Id.of_string_soft "$c"),
                 TyIdent
                   ("in",
                    TyArg
                      (Loc.tag
                         (Extend.TUentry (Genarg.get_arg_tag wit_var),
                          Names.Id.of_string_soft "$id"),
                       TyNil))))),
        (fun o c id ist -> cl_rewrite_clause c o AllOccurrences (Some id)));
     TyML
       (TyIdent
          ("setoid_rewrite",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_orient),
                 Names.Id.of_string_soft "$o"),
              TyArg
                (Loc.tag
                   (Extend.TUentry
                      (Genarg.get_arg_tag wit_glob_constr_with_bindings),
                    Names.Id.of_string_soft "$c"),
                 TyIdent
                   ("at",
                    TyArg
                      (Loc.tag
                         (Extend.TUentry (Genarg.get_arg_tag wit_occurrences),
                          Names.Id.of_string_soft "$occ"),
                       TyNil))))),
        (fun o c occ ist -> cl_rewrite_clause c o (occurrences_of occ) None));
     TyML
       (TyIdent
          ("setoid_rewrite",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_orient),
                 Names.Id.of_string_soft "$o"),
              TyArg
                (Loc.tag
                   (Extend.TUentry
                      (Genarg.get_arg_tag wit_glob_constr_with_bindings),
                    Names.Id.of_string_soft "$c"),
                 TyIdent
                   ("at",
                    TyArg
                      (Loc.tag
                         (Extend.TUentry (Genarg.get_arg_tag wit_occurrences),
                          Names.Id.of_string_soft "$occ"),
                       TyIdent
                         ("in",
                          TyArg
                            (Loc.tag
                               (Extend.TUentry (Genarg.get_arg_tag wit_var),
                                Names.Id.of_string_soft "$id"),
                             TyNil))))))),
        (fun o c occ id ist ->
           cl_rewrite_clause c o (occurrences_of occ) (Some id)));
     TyML
       (TyIdent
          ("setoid_rewrite",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_orient),
                 Names.Id.of_string_soft "$o"),
              TyArg
                (Loc.tag
                   (Extend.TUentry
                      (Genarg.get_arg_tag wit_glob_constr_with_bindings),
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
                             TyNil))))))),
        (fun o c id occ ist ->
           cl_rewrite_clause c o (occurrences_of occ) (Some id)))])

let _ =
  CList.iteri
    (fun i (depr, f) -> Vernacinterp.vinterp_add depr ("AddRelation", i) f)
    [false,
     (function
        [a; aeq; lemma1; lemma2; n] ->
          let a = Genarg.out_gen (Genarg.rawwit wit_constr) a in
          let aeq = Genarg.out_gen (Genarg.rawwit wit_constr) aeq in
          let lemma1 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma1 in
          let lemma2 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma2 in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          (fun ~atts ~st ->
             let () =
               declare_relation a aeq n (Some lemma1) (Some lemma2) None
             in
             st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [a; aeq; lemma1; n] ->
          let a = Genarg.out_gen (Genarg.rawwit wit_constr) a in
          let aeq = Genarg.out_gen (Genarg.rawwit wit_constr) aeq in
          let lemma1 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma1 in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          (fun ~atts ~st ->
             let () = declare_relation a aeq n (Some lemma1) None None in st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [a; aeq; n] ->
          let a = Genarg.out_gen (Genarg.rawwit wit_constr) a in
          let aeq = Genarg.out_gen (Genarg.rawwit wit_constr) aeq in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          (fun ~atts ~st ->
             let () = declare_relation a aeq n None None None in st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("AddRelation", i) f)
    [(function
        [a; aeq; lemma1; lemma2; n] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff) "AddRelation")
      | _ -> failwith "Extension: cannot occur");
     (function
        [a; aeq; lemma1; n] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff) "AddRelation")
      | _ -> failwith "Extension: cannot occur");
     (function
        [a; aeq; n] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff) "AddRelation")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("AddRelation", i) None r)
    [[Egramml.GramTerminal "Add"; Egramml.GramTerminal "Relation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "reflexivity"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "symmetry"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "as";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))];
     [Egramml.GramTerminal "Add"; Egramml.GramTerminal "Relation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "reflexivity"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "as";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))];
     [Egramml.GramTerminal "Add"; Egramml.GramTerminal "Relation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "as";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))]]

let _ =
  CList.iteri
    (fun i (depr, f) -> Vernacinterp.vinterp_add depr ("AddRelation2", i) f)
    [false,
     (function
        [a; aeq; lemma2; n] ->
          let a = Genarg.out_gen (Genarg.rawwit wit_constr) a in
          let aeq = Genarg.out_gen (Genarg.rawwit wit_constr) aeq in
          let lemma2 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma2 in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          (fun ~atts ~st ->
             let () = declare_relation a aeq n None (Some lemma2) None in st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [a; aeq; lemma2; lemma3; n] ->
          let a = Genarg.out_gen (Genarg.rawwit wit_constr) a in
          let aeq = Genarg.out_gen (Genarg.rawwit wit_constr) aeq in
          let lemma2 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma2 in
          let lemma3 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma3 in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          (fun ~atts ~st ->
             let () =
               declare_relation a aeq n None (Some lemma2) (Some lemma3)
             in
             st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("AddRelation2", i) f)
    [(function
        [a; aeq; lemma2; n] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff) "AddRelation2")
      | _ -> failwith "Extension: cannot occur");
     (function
        [a; aeq; lemma2; lemma3; n] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff) "AddRelation2")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("AddRelation2", i) None r)
    [[Egramml.GramTerminal "Add"; Egramml.GramTerminal "Relation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "symmetry"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "as";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))];
     [Egramml.GramTerminal "Add"; Egramml.GramTerminal "Relation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "symmetry"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "transitivity"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "as";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))]]

let _ =
  CList.iteri
    (fun i (depr, f) -> Vernacinterp.vinterp_add depr ("AddRelation3", i) f)
    [false,
     (function
        [a; aeq; lemma1; lemma3; n] ->
          let a = Genarg.out_gen (Genarg.rawwit wit_constr) a in
          let aeq = Genarg.out_gen (Genarg.rawwit wit_constr) aeq in
          let lemma1 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma1 in
          let lemma3 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma3 in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          (fun ~atts ~st ->
             let () =
               declare_relation a aeq n (Some lemma1) None (Some lemma3)
             in
             st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [a; aeq; lemma1; lemma2; lemma3; n] ->
          let a = Genarg.out_gen (Genarg.rawwit wit_constr) a in
          let aeq = Genarg.out_gen (Genarg.rawwit wit_constr) aeq in
          let lemma1 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma1 in
          let lemma2 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma2 in
          let lemma3 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma3 in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          (fun ~atts ~st ->
             let () =
               declare_relation a aeq n (Some lemma1) (Some lemma2)
                 (Some lemma3)
             in
             st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [a; aeq; lemma3; n] ->
          let a = Genarg.out_gen (Genarg.rawwit wit_constr) a in
          let aeq = Genarg.out_gen (Genarg.rawwit wit_constr) aeq in
          let lemma3 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma3 in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          (fun ~atts ~st ->
             let () = declare_relation a aeq n None None (Some lemma3) in st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("AddRelation3", i) f)
    [(function
        [a; aeq; lemma1; lemma3; n] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff) "AddRelation3")
      | _ -> failwith "Extension: cannot occur");
     (function
        [a; aeq; lemma1; lemma2; lemma3; n] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff) "AddRelation3")
      | _ -> failwith "Extension: cannot occur");
     (function
        [a; aeq; lemma3; n] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff) "AddRelation3")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("AddRelation3", i) None r)
    [[Egramml.GramTerminal "Add"; Egramml.GramTerminal "Relation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "reflexivity"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "transitivity"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "as";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))];
     [Egramml.GramTerminal "Add"; Egramml.GramTerminal "Relation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "reflexivity"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "symmetry"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "transitivity"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "as";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))];
     [Egramml.GramTerminal "Add"; Egramml.GramTerminal "Relation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "transitivity"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "as";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))]]

type binders_argtype = local_binder_expr list

let wit_binders : binders_argtype Genarg.uniform_genarg_type =
  Genarg.create_arg "binders"

let binders =
  Pcoq.create_generic_entry Pcoq.utactic "binders" (Genarg.rawwit wit_binders)

let () =
  let raw_printer _ _ _ l = Pp.pr_non_empty_arg Ppconstr.pr_binders l in
  Pptactic.declare_extra_vernac_genarg_pprule wit_binders raw_printer

open Pcoq

let _ =
  let _ = (binders : 'binders Gram.Entry.e) in
  Gram.extend (binders : 'binders Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj
            (Pcoq.Constr.binders : 'Pcoq__Constr__binders Gram.Entry.e))],
      Gramext.action
        (fun (b : 'Pcoq__Constr__binders) (loc : Ploc.t) -> (b : 'binders))]]

let _ =
  CList.iteri
    (fun i (depr, f) ->
       Vernacinterp.vinterp_add depr ("AddParametricRelation", i) f)
    [false,
     (function
        [b; a; aeq; lemma1; lemma2; n] ->
          let b = Genarg.out_gen (Genarg.rawwit wit_binders) b in
          let a = Genarg.out_gen (Genarg.rawwit wit_constr) a in
          let aeq = Genarg.out_gen (Genarg.rawwit wit_constr) aeq in
          let lemma1 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma1 in
          let lemma2 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma2 in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          (fun ~atts ~st ->
             let () =
               declare_relation ~binders:b a aeq n (Some lemma1) (Some lemma2)
                 None
             in
             st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [b; a; aeq; lemma1; n] ->
          let b = Genarg.out_gen (Genarg.rawwit wit_binders) b in
          let a = Genarg.out_gen (Genarg.rawwit wit_constr) a in
          let aeq = Genarg.out_gen (Genarg.rawwit wit_constr) aeq in
          let lemma1 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma1 in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          (fun ~atts ~st ->
             let () =
               declare_relation ~binders:b a aeq n (Some lemma1) None None
             in
             st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [b; a; aeq; n] ->
          let b = Genarg.out_gen (Genarg.rawwit wit_binders) b in
          let a = Genarg.out_gen (Genarg.rawwit wit_constr) a in
          let aeq = Genarg.out_gen (Genarg.rawwit wit_constr) aeq in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          (fun ~atts ~st ->
             let () = declare_relation ~binders:b a aeq n None None None in
             st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier
         ("AddParametricRelation", i) f)
    [(function
        [b; a; aeq; lemma1; lemma2; n] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "AddParametricRelation")
      | _ -> failwith "Extension: cannot occur");
     (function
        [b; a; aeq; lemma1; n] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "AddParametricRelation")
      | _ -> failwith "Extension: cannot occur");
     (function
        [b; a; aeq; n] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "AddParametricRelation")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("AddParametricRelation", i) None
         r)
    [[Egramml.GramTerminal "Add"; Egramml.GramTerminal "Parametric";
      Egramml.GramTerminal "Relation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_binders),
            Extend.Aentry (Pcoq.genarg_grammar wit_binders)));
      Egramml.GramTerminal ":";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "reflexivity"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "symmetry"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "as";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))];
     [Egramml.GramTerminal "Add"; Egramml.GramTerminal "Parametric";
      Egramml.GramTerminal "Relation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_binders),
            Extend.Aentry (Pcoq.genarg_grammar wit_binders)));
      Egramml.GramTerminal ":";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "reflexivity"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "as";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))];
     [Egramml.GramTerminal "Add"; Egramml.GramTerminal "Parametric";
      Egramml.GramTerminal "Relation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_binders),
            Extend.Aentry (Pcoq.genarg_grammar wit_binders)));
      Egramml.GramTerminal ":";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "as";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))]]

let _ =
  CList.iteri
    (fun i (depr, f) ->
       Vernacinterp.vinterp_add depr ("AddParametricRelation2", i) f)
    [false,
     (function
        [b; a; aeq; lemma2; n] ->
          let b = Genarg.out_gen (Genarg.rawwit wit_binders) b in
          let a = Genarg.out_gen (Genarg.rawwit wit_constr) a in
          let aeq = Genarg.out_gen (Genarg.rawwit wit_constr) aeq in
          let lemma2 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma2 in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          (fun ~atts ~st ->
             let () =
               declare_relation ~binders:b a aeq n None (Some lemma2) None
             in
             st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [b; a; aeq; lemma2; lemma3; n] ->
          let b = Genarg.out_gen (Genarg.rawwit wit_binders) b in
          let a = Genarg.out_gen (Genarg.rawwit wit_constr) a in
          let aeq = Genarg.out_gen (Genarg.rawwit wit_constr) aeq in
          let lemma2 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma2 in
          let lemma3 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma3 in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          (fun ~atts ~st ->
             let () =
               declare_relation ~binders:b a aeq n None (Some lemma2)
                 (Some lemma3)
             in
             st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier
         ("AddParametricRelation2", i) f)
    [(function
        [b; a; aeq; lemma2; n] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "AddParametricRelation2")
      | _ -> failwith "Extension: cannot occur");
     (function
        [b; a; aeq; lemma2; lemma3; n] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "AddParametricRelation2")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("AddParametricRelation2", i)
         None r)
    [[Egramml.GramTerminal "Add"; Egramml.GramTerminal "Parametric";
      Egramml.GramTerminal "Relation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_binders),
            Extend.Aentry (Pcoq.genarg_grammar wit_binders)));
      Egramml.GramTerminal ":";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "symmetry"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "as";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))];
     [Egramml.GramTerminal "Add"; Egramml.GramTerminal "Parametric";
      Egramml.GramTerminal "Relation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_binders),
            Extend.Aentry (Pcoq.genarg_grammar wit_binders)));
      Egramml.GramTerminal ":";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "symmetry"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "transitivity"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "as";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))]]

let _ =
  CList.iteri
    (fun i (depr, f) ->
       Vernacinterp.vinterp_add depr ("AddParametricRelation3", i) f)
    [false,
     (function
        [b; a; aeq; lemma1; lemma3; n] ->
          let b = Genarg.out_gen (Genarg.rawwit wit_binders) b in
          let a = Genarg.out_gen (Genarg.rawwit wit_constr) a in
          let aeq = Genarg.out_gen (Genarg.rawwit wit_constr) aeq in
          let lemma1 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma1 in
          let lemma3 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma3 in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          (fun ~atts ~st ->
             let () =
               declare_relation ~binders:b a aeq n (Some lemma1) None
                 (Some lemma3)
             in
             st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [b; a; aeq; lemma1; lemma2; lemma3; n] ->
          let b = Genarg.out_gen (Genarg.rawwit wit_binders) b in
          let a = Genarg.out_gen (Genarg.rawwit wit_constr) a in
          let aeq = Genarg.out_gen (Genarg.rawwit wit_constr) aeq in
          let lemma1 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma1 in
          let lemma2 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma2 in
          let lemma3 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma3 in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          (fun ~atts ~st ->
             let () =
               declare_relation ~binders:b a aeq n (Some lemma1) (Some lemma2)
                 (Some lemma3)
             in
             st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [b; a; aeq; lemma3; n] ->
          let b = Genarg.out_gen (Genarg.rawwit wit_binders) b in
          let a = Genarg.out_gen (Genarg.rawwit wit_constr) a in
          let aeq = Genarg.out_gen (Genarg.rawwit wit_constr) aeq in
          let lemma3 = Genarg.out_gen (Genarg.rawwit wit_constr) lemma3 in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          (fun ~atts ~st ->
             let () =
               declare_relation ~binders:b a aeq n None None (Some lemma3)
             in
             st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier
         ("AddParametricRelation3", i) f)
    [(function
        [b; a; aeq; lemma1; lemma3; n] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "AddParametricRelation3")
      | _ -> failwith "Extension: cannot occur");
     (function
        [b; a; aeq; lemma1; lemma2; lemma3; n] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "AddParametricRelation3")
      | _ -> failwith "Extension: cannot occur");
     (function
        [b; a; aeq; lemma3; n] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "AddParametricRelation3")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("AddParametricRelation3", i)
         None r)
    [[Egramml.GramTerminal "Add"; Egramml.GramTerminal "Parametric";
      Egramml.GramTerminal "Relation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_binders),
            Extend.Aentry (Pcoq.genarg_grammar wit_binders)));
      Egramml.GramTerminal ":";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "reflexivity"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "transitivity"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "as";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))];
     [Egramml.GramTerminal "Add"; Egramml.GramTerminal "Parametric";
      Egramml.GramTerminal "Relation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_binders),
            Extend.Aentry (Pcoq.genarg_grammar wit_binders)));
      Egramml.GramTerminal ":";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "reflexivity"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "symmetry"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "transitivity"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "as";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))];
     [Egramml.GramTerminal "Add"; Egramml.GramTerminal "Parametric";
      Egramml.GramTerminal "Relation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_binders),
            Extend.Aentry (Pcoq.genarg_grammar wit_binders)));
      Egramml.GramTerminal ":";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "transitivity"; Egramml.GramTerminal "proved";
      Egramml.GramTerminal "by";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "as";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))]]

let _ =
  CList.iteri
    (fun i (depr, f) -> Vernacinterp.vinterp_add depr ("AddSetoid1", i) f)
    [false,
     (function
        [a; aeq; t; n] ->
          let a = Genarg.out_gen (Genarg.rawwit wit_constr) a in
          let aeq = Genarg.out_gen (Genarg.rawwit wit_constr) aeq in
          let t = Genarg.out_gen (Genarg.rawwit wit_constr) t in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          (fun ~atts ~st ->
             let open Vernacinterp in
             begin
               add_setoid (not (Locality.make_section_locality atts.locality))
                 [] a aeq t n;
               st
             end)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [binders; a; aeq; t; n] ->
          let binders = Genarg.out_gen (Genarg.rawwit wit_binders) binders in
          let a = Genarg.out_gen (Genarg.rawwit wit_constr) a in
          let aeq = Genarg.out_gen (Genarg.rawwit wit_constr) aeq in
          let t = Genarg.out_gen (Genarg.rawwit wit_constr) t in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          (fun ~atts ~st ->
             let open Vernacinterp in
             begin
               add_setoid (not (Locality.make_section_locality atts.locality))
                 binders a aeq t n;
               st
             end)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [m; n] ->
          let m = Genarg.out_gen (Genarg.rawwit wit_constr) m in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          (fun ~atts ~st ->
             let open Vernacinterp in
             begin
               add_morphism_infer
                 (not (Locality.make_section_locality atts.locality)) m n;
               st
             end)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [m; s; n] ->
          let m = Genarg.out_gen (Genarg.rawwit wit_constr) m in
          let s = Genarg.out_gen (Genarg.rawwit wit_lconstr) s in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          (fun ~atts ~st ->
             let open Vernacinterp in
             begin
               add_morphism
                 (not (Locality.make_section_locality atts.locality)) [] m s
                 n;
               st
             end)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [binders; m; s; n] ->
          let binders = Genarg.out_gen (Genarg.rawwit wit_binders) binders in
          let m = Genarg.out_gen (Genarg.rawwit wit_constr) m in
          let s = Genarg.out_gen (Genarg.rawwit wit_lconstr) s in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          (fun ~atts ~st ->
             let open Vernacinterp in
             begin
               add_morphism
                 (not (Locality.make_section_locality atts.locality)) binders
                 m s n;
               st
             end)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("AddSetoid1", i) f)
    [(function
        [a; aeq; t; n] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff) "AddSetoid1")
      | _ -> failwith "Extension: cannot occur");
     (function
        [binders; a; aeq; t; n] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff) "AddSetoid1")
      | _ -> failwith "Extension: cannot occur");
     (function
        [m; n] ->
          let m = Genarg.out_gen (Genarg.rawwit wit_constr) m in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          let _ = let _ = m in let _ = n in () in
          (* This command may or may not open a goal *)
          (fun loc -> Vernacexpr.VtUnknown, Vernacexpr.VtNow)
      | _ -> failwith "Extension: cannot occur");
     (function
        [m; s; n] ->
          let m = Genarg.out_gen (Genarg.rawwit wit_constr) m in
          let s = Genarg.out_gen (Genarg.rawwit wit_lconstr) s in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          let _ = let _ = m in let _ = s in let _ = n in () in
          (fun loc ->
             Vernacexpr
             .(VtStartProof ("Classic", GuaranteesOpacity, [n]), VtLater))
      | _ -> failwith "Extension: cannot occur");
     (function
        [binders; m; s; n] ->
          let binders = Genarg.out_gen (Genarg.rawwit wit_binders) binders in
          let m = Genarg.out_gen (Genarg.rawwit wit_constr) m in
          let s = Genarg.out_gen (Genarg.rawwit wit_lconstr) s in
          let n = Genarg.out_gen (Genarg.rawwit wit_ident) n in
          let _ =
            let _ = binders in let _ = m in let _ = s in let _ = n in ()
          in
          (fun loc ->
             Vernacexpr
             .(VtStartProof ("Classic", GuaranteesOpacity, [n]), VtLater))
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("AddSetoid1", i) None r)
    [[Egramml.GramTerminal "Add"; Egramml.GramTerminal "Setoid";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "as";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))];
     [Egramml.GramTerminal "Add"; Egramml.GramTerminal "Parametric";
      Egramml.GramTerminal "Setoid";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_binders),
            Extend.Aentry (Pcoq.genarg_grammar wit_binders)));
      Egramml.GramTerminal ":";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "as";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))];
     [Egramml.GramTerminal "Add"; Egramml.GramTerminal "Morphism";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal ":";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))];
     [Egramml.GramTerminal "Add"; Egramml.GramTerminal "Morphism";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "with"; Egramml.GramTerminal "signature";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_lconstr),
            Extend.Aentry (Pcoq.genarg_grammar wit_lconstr)));
      Egramml.GramTerminal "as";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))];
     [Egramml.GramTerminal "Add"; Egramml.GramTerminal "Parametric";
      Egramml.GramTerminal "Morphism";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_binders),
            Extend.Aentry (Pcoq.genarg_grammar wit_binders)));
      Egramml.GramTerminal ":";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_constr),
            Extend.Aentry (Pcoq.genarg_grammar wit_constr)));
      Egramml.GramTerminal "with"; Egramml.GramTerminal "signature";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_lconstr),
            Extend.Aentry (Pcoq.genarg_grammar wit_lconstr)));
      Egramml.GramTerminal "as";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))]]

let _ =
  Tacentries.tactic_extend __coq_plugin_name "setoid_symmetry" ~level:0
    Tacentries
    .([TyML
       (TyIdent ("setoid_symmetry", TyNil), (fun ist -> setoid_symmetry));
     TyML
       (TyIdent
          ("setoid_symmetry",
           TyIdent
             ("in",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_var),
                    Names.Id.of_string_soft "$n"),
                 TyNil))),
        (fun n ist -> setoid_symmetry_in n))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "setoid_reflexivity" ~level:0
    Tacentries
    .([TyML
       (TyIdent ("setoid_reflexivity", TyNil),
        (fun ist -> setoid_reflexivity))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "setoid_transitivity" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("setoid_transitivity",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$t"),
              TyNil)),
        (fun t ist -> setoid_transitivity (Some t)));
     TyML
       (TyIdent ("setoid_etransitivity", TyNil),
        (fun ist -> setoid_transitivity None))])

let _ =
  CList.iteri
    (fun i (depr, f) ->
       Vernacinterp.vinterp_add depr ("PrintRewriteHintDb", i) f)
    [false,
     (function
        [s] ->
          let s = Genarg.out_gen (Genarg.rawwit wit_preident) s in
          (fun ~atts ~st ->
             let () =
               let (sigma, env) = Pfedit.get_current_context () in
               Feedback.msg_notice
                 (Autorewrite.print_rewrite_hintdb env sigma s)
             in
             st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("PrintRewriteHintDb", i)
         f)
    [(function
        [s] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_query)
               "PrintRewriteHintDb")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("PrintRewriteHintDb", i) None r)
    [[Egramml.GramTerminal "Print"; Egramml.GramTerminal "Rewrite";
      Egramml.GramTerminal "HintDb";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_preident),
            Extend.Aentry (Pcoq.genarg_grammar wit_preident)))]]
