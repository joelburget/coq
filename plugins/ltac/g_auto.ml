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
open Pcoq.Prim
open Pcoq.Constr
open Pltac
open Hints

let __coq_plugin_name = "ltac_plugin"

(* Hint bases *)


let _ =
  Tacentries.tactic_extend __coq_plugin_name "eassumption" ~level:0
    Tacentries
    .([TyML
       (TyIdent ("eassumption", TyNil), (fun ist -> Eauto.e_assumption))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "eexact" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("eexact",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$c"),
              TyNil)),
        (fun c ist -> Eauto.e_give_exact c))])

let pr_hintbases _prc _prlc _prt = Pptactic.pr_hintbases

let wit_hintbases = Genarg.make0 "hintbases"
let _ =
  Genintern.register_intern0 wit_hintbases
    (fun ist v ->
       let ans =
         out_gen
           (Genarg.glbwit (Genarg.wit_opt (Genarg.wit_list wit_preident)))
           (Tacintern.intern_genarg ist
              (Genarg.in_gen
                 (Genarg.rawwit
                    (Genarg.wit_opt (Genarg.wit_list wit_preident)))
                 v))
       in
       ist, ans)
let _ =
  Genintern.register_subst0 wit_hintbases
    (fun s x ->
       out_gen (Genarg.glbwit (Genarg.wit_opt (Genarg.wit_list wit_preident)))
         (Tacsubst.subst_genarg s
            (Genarg.in_gen
               (Genarg.glbwit (Genarg.wit_opt (Genarg.wit_list wit_preident)))
               x)))
let _ =
  Geninterp.register_interp0 wit_hintbases
    (fun ist x ->
       Tacinterp.interp_genarg ist
         (Genarg.in_gen
            (Genarg.glbwit (Genarg.wit_opt (Genarg.wit_list wit_preident)))
            x))
let _ =
  Geninterp.register_val0 wit_hintbases
    (Some
       (Geninterp.val_tag
          (Genarg.topwit (Genarg.wit_opt (Genarg.wit_list wit_preident)))))
let hintbases =
  let hintbases =
    Pcoq.create_generic_entry Pcoq.utactic "hintbases"
      (Genarg.rawwit wit_hintbases)
  in
  let () =
    Pcoq.grammar_extend hintbases None
      (None,
       [None, None,
        [Extend.Rule (Extend.Stop, (fun loc -> Some []));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "with")),
               Extend.Alist1 (Extend.Aentry preident)),
            (fun l _ loc -> Some l));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "with")),
               Extend.Atoken (CLexer.terminal "*")),
            (fun _ _ loc -> None))]])
  in
  hintbases
let _ =
  Pptactic.declare_extra_genarg_pprule wit_hintbases pr_hintbases pr_hintbases
    pr_hintbases;
  Tacentries.create_ltac_quotation "hintbases"
    (fun (loc, v) ->
       Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit_hintbases) v))
    (hintbases, None)

let eval_uconstrs ist cs =
  let flags =
    {Pretyping.use_typeclasses = false; solve_unification_constraints = true;
     use_hook = Pfedit.solve_by_implicit_tactic (); fail_evar = false;
     expand_evars = true}
  in
  let map c env sigma = c env sigma in
  List.map (fun c -> map (Tacinterp.type_uconstr ~flags ist c)) cs

let pr_auto_using_raw _ _ _ = Pptactic.pr_auto_using Ppconstr.pr_constr_expr
let pr_auto_using_glob _ _ _ =
  Pptactic.pr_auto_using
    (fun (c, _) ->
       let (_, env) = Pfedit.get_current_context () in
       Printer.pr_glob_constr_env env c)
let pr_auto_using _ _ _ =
  Pptactic.pr_auto_using
    (let (sigma, env) = Pfedit.get_current_context () in
     Printer.pr_closed_glob_env env sigma)

let wit_auto_using = Genarg.make0 "auto_using"
let _ =
  Genintern.register_intern0 wit_auto_using
    (fun ist v ->
       let ans =
         out_gen (Genarg.glbwit (Genarg.wit_list wit_uconstr))
           (Tacintern.intern_genarg ist
              (Genarg.in_gen (Genarg.rawwit (Genarg.wit_list wit_uconstr)) v))
       in
       ist, ans)
let _ =
  Genintern.register_subst0 wit_auto_using
    (fun s x ->
       out_gen (Genarg.glbwit (Genarg.wit_list wit_uconstr))
         (Tacsubst.subst_genarg s
            (Genarg.in_gen (Genarg.glbwit (Genarg.wit_list wit_uconstr)) x)))
let _ =
  Geninterp.register_interp0 wit_auto_using
    (fun ist x ->
       Tacinterp.interp_genarg ist
         (Genarg.in_gen (Genarg.glbwit (Genarg.wit_list wit_uconstr)) x))
let _ =
  Geninterp.register_val0 wit_auto_using
    (Some (Geninterp.val_tag (Genarg.topwit (Genarg.wit_list wit_uconstr))))
let auto_using =
  let auto_using =
    Pcoq.create_generic_entry Pcoq.utactic "auto_using"
      (Genarg.rawwit wit_auto_using)
  in
  let () =
    Pcoq.grammar_extend auto_using None
      (None,
       [None, None,
        [Extend.Rule (Extend.Stop, (fun loc -> []));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "using")),
               Extend.Alist1sep
                 (Extend.Aentry uconstr,
                  Extend.Atoken (CLexer.terminal ","))),
            (fun l _ loc -> l))]])
  in
  auto_using
let _ =
  Pptactic.declare_extra_genarg_pprule wit_auto_using pr_auto_using_raw
    pr_auto_using_glob pr_auto_using;
  Tacentries.create_ltac_quotation "auto_using"
    (fun (loc, v) ->
       Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit_auto_using) v))
    (auto_using, None)

(** Auto *)

let _ =
  Tacentries.tactic_extend __coq_plugin_name "trivial" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("trivial",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_auto_using),
                 Names.Id.of_string_soft "$lems"),
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_hintbases),
                    Names.Id.of_string_soft "$db"),
                 TyNil))),
        (fun lems db ist -> Auto.h_trivial (eval_uconstrs ist lems) db))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "info_trivial" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("info_trivial",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_auto_using),
                 Names.Id.of_string_soft "$lems"),
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_hintbases),
                    Names.Id.of_string_soft "$db"),
                 TyNil))),
        (fun lems db ist ->
           Auto.h_trivial ~debug:Info (eval_uconstrs ist lems) db))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "debug_trivial" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("debug",
           TyIdent
             ("trivial",
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_auto_using),
                    Names.Id.of_string_soft "$lems"),
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_hintbases),
                       Names.Id.of_string_soft "$db"),
                    TyNil)))),
        (fun lems db ist ->
           Auto.h_trivial ~debug:Debug (eval_uconstrs ist lems) db))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "auto" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("auto",
           TyArg
             (Loc.tag
                (Extend.TUopt
                   (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var)),
                 Names.Id.of_string_soft "$n"),
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_auto_using),
                    Names.Id.of_string_soft "$lems"),
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_hintbases),
                       Names.Id.of_string_soft "$db"),
                    TyNil)))),
        (fun n lems db ist -> Auto.h_auto n (eval_uconstrs ist lems) db))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "info_auto" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("info_auto",
           TyArg
             (Loc.tag
                (Extend.TUopt
                   (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var)),
                 Names.Id.of_string_soft "$n"),
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_auto_using),
                    Names.Id.of_string_soft "$lems"),
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_hintbases),
                       Names.Id.of_string_soft "$db"),
                    TyNil)))),
        (fun n lems db ist ->
           Auto.h_auto ~debug:Info n (eval_uconstrs ist lems) db))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "debug_auto" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("debug",
           TyIdent
             ("auto",
              TyArg
                (Loc.tag
                   (Extend.TUopt
                      (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var)),
                    Names.Id.of_string_soft "$n"),
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_auto_using),
                       Names.Id.of_string_soft "$lems"),
                    TyArg
                      (Loc.tag
                         (Extend.TUentry (Genarg.get_arg_tag wit_hintbases),
                          Names.Id.of_string_soft "$db"),
                       TyNil))))),
        (fun n lems db ist ->
           Auto.h_auto ~debug:Debug n (eval_uconstrs ist lems) db))])

(** Eauto *)

let _ =
  Tacentries.tactic_extend __coq_plugin_name "prolog" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("prolog",
           TyIdent
             ("[",
              TyArg
                (Loc.tag
                   (Extend.TUlist0
                      (Extend.TUentry (Genarg.get_arg_tag wit_uconstr)),
                    Names.Id.of_string_soft "$l"),
                 TyIdent
                   ("]",
                    TyArg
                      (Loc.tag
                         (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var),
                          Names.Id.of_string_soft "$n"),
                       TyNil))))),
        (fun l n ist -> Eauto.prolog_tac (eval_uconstrs ist l) n))])

let make_depth n = snd (Eauto.make_dimension n None)

let _ =
  Tacentries.tactic_extend __coq_plugin_name "eauto" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("eauto",
           TyArg
             (Loc.tag
                (Extend.TUopt
                   (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var)),
                 Names.Id.of_string_soft "$n"),
              TyArg
                (Loc.tag
                   (Extend.TUopt
                      (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var)),
                    Names.Id.of_string_soft "$p"),
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_auto_using),
                       Names.Id.of_string_soft "$lems"),
                    TyArg
                      (Loc.tag
                         (Extend.TUentry (Genarg.get_arg_tag wit_hintbases),
                          Names.Id.of_string_soft "$db"),
                       TyNil))))),
        (fun n p lems db ist ->
           Eauto.gen_eauto (Eauto.make_dimension n p) (eval_uconstrs ist lems)
             db))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "new_eauto" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("new",
           TyIdent
             ("auto",
              TyArg
                (Loc.tag
                   (Extend.TUopt
                      (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var)),
                    Names.Id.of_string_soft "$n"),
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_auto_using),
                       Names.Id.of_string_soft "$lems"),
                    TyArg
                      (Loc.tag
                         (Extend.TUentry (Genarg.get_arg_tag wit_hintbases),
                          Names.Id.of_string_soft "$db"),
                       TyNil))))),
        (fun n lems db ist ->
           match db with
             None ->
               Auto.new_full_auto (make_depth n) (eval_uconstrs ist lems)
           | Some l ->
               Auto.new_auto (make_depth n) (eval_uconstrs ist lems) l))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "debug_eauto" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("debug",
           TyIdent
             ("eauto",
              TyArg
                (Loc.tag
                   (Extend.TUopt
                      (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var)),
                    Names.Id.of_string_soft "$n"),
                 TyArg
                   (Loc.tag
                      (Extend.TUopt
                         (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var)),
                       Names.Id.of_string_soft "$p"),
                    TyArg
                      (Loc.tag
                         (Extend.TUentry (Genarg.get_arg_tag wit_auto_using),
                          Names.Id.of_string_soft "$lems"),
                       TyArg
                         (Loc.tag
                            (Extend.TUentry
                               (Genarg.get_arg_tag wit_hintbases),
                             Names.Id.of_string_soft "$db"),
                          TyNil)))))),
        (fun n p lems db ist ->
           Eauto.gen_eauto ~debug:Debug (Eauto.make_dimension n p)
             (eval_uconstrs ist lems) db))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "info_eauto" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("info_eauto",
           TyArg
             (Loc.tag
                (Extend.TUopt
                   (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var)),
                 Names.Id.of_string_soft "$n"),
              TyArg
                (Loc.tag
                   (Extend.TUopt
                      (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var)),
                    Names.Id.of_string_soft "$p"),
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_auto_using),
                       Names.Id.of_string_soft "$lems"),
                    TyArg
                      (Loc.tag
                         (Extend.TUentry (Genarg.get_arg_tag wit_hintbases),
                          Names.Id.of_string_soft "$db"),
                       TyNil))))),
        (fun n p lems db ist ->
           Eauto.gen_eauto ~debug:Info (Eauto.make_dimension n p)
             (eval_uconstrs ist lems) db))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "dfs_eauto" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("dfs",
           TyIdent
             ("eauto",
              TyArg
                (Loc.tag
                   (Extend.TUopt
                      (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var)),
                    Names.Id.of_string_soft "$p"),
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_auto_using),
                       Names.Id.of_string_soft "$lems"),
                    TyArg
                      (Loc.tag
                         (Extend.TUentry (Genarg.get_arg_tag wit_hintbases),
                          Names.Id.of_string_soft "$db"),
                       TyNil))))),
        (fun p lems db ist ->
           Eauto.gen_eauto (Eauto.make_dimension p None)
             (eval_uconstrs ist lems) db))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "autounfold" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("autounfold",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_hintbases),
                 Names.Id.of_string_soft "$db"),
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_clause_dft_concl),
                    Names.Id.of_string_soft "$cl"),
                 TyNil))),
        (fun db cl ist -> Eauto.autounfold_tac db cl))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "autounfold_one" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("autounfold_one",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_hintbases),
                 Names.Id.of_string_soft "$db"),
              TyIdent
                ("in",
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_var),
                       Names.Id.of_string_soft "$id"),
                    TyNil)))),
        (fun db id ist ->
           Eauto.autounfold_one
             (match db with
                None -> ["core"]
              | Some x -> "core" :: x)
             (Some (id, Locus.InHyp))));
     TyML
       (TyIdent
          ("autounfold_one",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_hintbases),
                 Names.Id.of_string_soft "$db"),
              TyNil)),
        (fun db ist ->
           Eauto.autounfold_one
             (match db with
                None -> ["core"]
              | Some x -> "core" :: x)
             None))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "unify" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("unify",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$x"),
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                    Names.Id.of_string_soft "$y"),
                 TyNil))),
        (fun x y ist -> Tactics.unify x y));
     TyML
       (TyIdent
          ("unify",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$x"),
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                    Names.Id.of_string_soft "$y"),
                 TyIdent
                   ("with",
                    TyArg
                      (Loc.tag
                         (Extend.TUentry (Genarg.get_arg_tag wit_preident),
                          Names.Id.of_string_soft "$base"),
                       TyNil))))),
        (fun x y base ist ->
           let table =
             try Some (Hints.searchtable_map base) with Not_found -> None
           in
           match table with
             None ->
               let msg =
                 (++) ((++) (str "Hint table ") (str base)) (str " not found")
               in
               Tacticals.New.tclZEROMSG msg
           | Some t ->
               let state = Hints.Hint_db.transparent_state t in
               Tactics.unify ~state x y))])


let _ =
  Tacentries.tactic_extend __coq_plugin_name "convert_concl_no_check" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("convert_concl_no_check",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$x"),
              TyNil)),
        (fun x ist -> Tactics.convert_concl_no_check x Term.DEFAULTcast))])

let pr_pre_hints_path_atom _ _ _ =
  Hints.pp_hints_path_atom Libnames.pr_reference
let pr_hints_path_atom _ _ _ = Hints.pp_hints_path_atom Printer.pr_global
let glob_hints_path_atom ist = Hints.glob_hints_path_atom

let wit_hints_path_atom = Genarg.make0 "hints_path_atom"
let _ =
  Genintern.register_intern0 wit_hints_path_atom
    (fun ist v -> ist, glob_hints_path_atom ist v)
let _ = Genintern.register_subst0 wit_hints_path_atom (fun s v -> v)
let _ =
  Geninterp.register_interp0 wit_hints_path_atom
    (fun ist v ->
       Ftactic.return
         (Geninterp.Val.inject
            (Geninterp.val_tag (Genarg.topwit wit_hints_path_atom)) v))
let _ = Geninterp.register_val0 wit_hints_path_atom None
let hints_path_atom =
  let hints_path_atom =
    Pcoq.create_generic_entry Pcoq.utactic "hints_path_atom"
      (Genarg.rawwit wit_hints_path_atom)
  in
  let () =
    Pcoq.grammar_extend hints_path_atom None
      (None,
       [None, None,
        [Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Atoken (CLexer.terminal "_")),
            (fun _ loc -> Hints.PathAny));
         Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Alist1 (Extend.Aentry global)),
            (fun g loc -> Hints.PathHints g))]])
  in
  hints_path_atom
let _ =
  Pptactic.declare_extra_genarg_pprule wit_hints_path_atom
    pr_pre_hints_path_atom pr_hints_path_atom pr_hints_path_atom;
  Tacentries.create_ltac_quotation "hints_path_atom"
    (fun (loc, v) ->
       Tacexpr.TacGeneric
         (Genarg.in_gen (Genarg.rawwit wit_hints_path_atom) v))
    (hints_path_atom, None)

let pr_hints_path prc prx pry c = Hints.pp_hints_path c
let pr_pre_hints_path prc prx pry c =
  Hints.pp_hints_path_gen Libnames.pr_reference c
let glob_hints_path ist = Hints.glob_hints_path

let wit_hints_path = Genarg.make0 "hints_path"
let _ =
  Genintern.register_intern0 wit_hints_path
    (fun ist v -> ist, glob_hints_path ist v)
let _ = Genintern.register_subst0 wit_hints_path (fun s v -> v)
let _ =
  Geninterp.register_interp0 wit_hints_path
    (fun ist v ->
       Ftactic.return
         (Geninterp.Val.inject
            (Geninterp.val_tag (Genarg.topwit wit_hints_path)) v))
let _ = Geninterp.register_val0 wit_hints_path None
let hints_path =
  let hints_path =
    Pcoq.create_generic_entry Pcoq.utactic "hints_path"
      (Genarg.rawwit wit_hints_path)
  in
  let () =
    Pcoq.grammar_extend hints_path None
      (None,
       [None, None,
        [Extend.Rule
           (Extend.Next
              (Extend.Next (Extend.Stop, Extend.Aentry hints_path),
               Extend.Aentry hints_path),
            (fun q p loc -> Hints.PathSeq (p, q)));
         Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Aentry hints_path_atom),
            (fun a loc -> Hints.PathAtom a));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next (Extend.Stop, Extend.Aentry hints_path),
                  Extend.Atoken (CLexer.terminal "|")),
               Extend.Aentry hints_path),
            (fun q _ p loc -> Hints.PathOr (p, q)));
         Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Atoken (CLexer.terminal "eps")),
            (fun _ loc -> Hints.PathEpsilon));
         Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Atoken (CLexer.terminal "emp")),
            (fun _ loc -> Hints.PathEmpty));
         Extend.Rule
           (Extend.Next
              (Extend.Next (Extend.Stop, Extend.Aentry hints_path),
               Extend.Atoken (CLexer.terminal "*")),
            (fun _ p loc -> Hints.PathStar p));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next
                    (Extend.Stop, Extend.Atoken (CLexer.terminal "(")),
                  Extend.Aentry hints_path),
               Extend.Atoken (CLexer.terminal ")")),
            (fun _ p _ loc -> p))]])
  in
  hints_path
let _ =
  Pptactic.declare_extra_genarg_pprule wit_hints_path pr_pre_hints_path
    pr_hints_path pr_hints_path;
  Tacentries.create_ltac_quotation "hints_path"
    (fun (loc, v) ->
       Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit_hints_path) v))
    (hints_path, None)

let wit_opthints = Genarg.make0 "opthints"
let _ =
  Genintern.register_intern0 wit_opthints
    (fun ist v ->
       let ans =
         out_gen
           (Genarg.glbwit (Genarg.wit_opt (Genarg.wit_list wit_preident)))
           (Tacintern.intern_genarg ist
              (Genarg.in_gen
                 (Genarg.rawwit
                    (Genarg.wit_opt (Genarg.wit_list wit_preident)))
                 v))
       in
       ist, ans)
let _ =
  Genintern.register_subst0 wit_opthints
    (fun s x ->
       out_gen (Genarg.glbwit (Genarg.wit_opt (Genarg.wit_list wit_preident)))
         (Tacsubst.subst_genarg s
            (Genarg.in_gen
               (Genarg.glbwit (Genarg.wit_opt (Genarg.wit_list wit_preident)))
               x)))
let _ =
  Geninterp.register_interp0 wit_opthints
    (fun ist x ->
       Tacinterp.interp_genarg ist
         (Genarg.in_gen
            (Genarg.glbwit (Genarg.wit_opt (Genarg.wit_list wit_preident)))
            x))
let _ =
  Geninterp.register_val0 wit_opthints
    (Some
       (Geninterp.val_tag
          (Genarg.topwit (Genarg.wit_opt (Genarg.wit_list wit_preident)))))
let opthints =
  let opthints =
    Pcoq.create_generic_entry Pcoq.utactic "opthints"
      (Genarg.rawwit wit_opthints)
  in
  let () =
    Pcoq.grammar_extend opthints None
      (None,
       [None, None,
        [Extend.Rule (Extend.Stop, (fun loc -> None));
         Extend.Rule
           (Extend.Next
              (Extend.Next (Extend.Stop, Extend.Atoken (CLexer.terminal ":")),
               Extend.Alist1 (Extend.Aentry preident)),
            (fun l _ loc -> Some l))]])
  in
  opthints
let _ =
  Pptactic.declare_extra_genarg_pprule wit_opthints pr_hintbases pr_hintbases
    pr_hintbases;
  Tacentries.create_ltac_quotation "opthints"
    (fun (loc, v) ->
       Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit_opthints) v))
    (opthints, None)

let _ =
  CList.iteri
    (fun i (depr, f) -> Vernacinterp.vinterp_add depr ("HintCut", i) f)
    [false,
     (function
        [p; dbnames] ->
          let p = Genarg.out_gen (Genarg.rawwit wit_hints_path) p in
          let dbnames = Genarg.out_gen (Genarg.rawwit wit_opthints) dbnames in
          (fun ~atts ~st ->
             let open Vernacinterp in
             let entry = Hints.HintsCutEntry (Hints.glob_hints_path p) in
             Hints.add_hints (Locality.make_section_locality atts.locality)
               (match dbnames with
                  None -> ["core"]
                | Some l -> l)
               entry;
             st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f -> Vernac_classifier.declare_vernac_classifier ("HintCut", i) f)
    [(function
        [p; dbnames] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff) "HintCut")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r -> Egramml.extend_vernac_command_grammar ("HintCut", i) None r)
    [[Egramml.GramTerminal "Hint"; Egramml.GramTerminal "Cut";
      Egramml.GramTerminal "[";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_hints_path),
            Extend.Aentry (Pcoq.genarg_grammar wit_hints_path)));
      Egramml.GramTerminal "]";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_opthints),
            Extend.Aentry (Pcoq.genarg_grammar wit_opthints)))]]

