(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Class_tactics
open Stdarg
open Tacarg

let __coq_plugin_name = "ltac_plugin"

(** Options: depth, debug and transparency settings. *)

let set_transparency cl b =
  List.iter
    (fun r ->
       let gr = Smartlocate.global_with_alias r in
       let ev = Tacred.evaluable_of_global_reference (Global.env ()) gr in
       Classes.set_typeclass_transparency ev
         (Locality.make_section_locality None) b)
    cl

let _ =
  CList.iteri
    (fun i (depr, f) ->
       Vernacinterp.vinterp_add depr ("Typeclasses_Unfold_Settings", i) f)
    [false,
     (function
        [cl] ->
          let cl =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_list wit_reference)) cl
          in
          (fun ~atts ~st -> let () = set_transparency cl true in st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier
         ("Typeclasses_Unfold_Settings", i) f)
    [(function
        [cl] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "Typeclasses_Unfold_Settings")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar
         ("Typeclasses_Unfold_Settings", i) None r)
    [[Egramml.GramTerminal "Typeclasses"; Egramml.GramTerminal "Transparent";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_list wit_reference)),
            Extend.Alist0
              (Extend.Aentry (Pcoq.genarg_grammar wit_reference))))]]

let _ =
  CList.iteri
    (fun i (depr, f) ->
       Vernacinterp.vinterp_add depr ("Typeclasses_Rigid_Settings", i) f)
    [false,
     (function
        [cl] ->
          let cl =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_list wit_reference)) cl
          in
          (fun ~atts ~st -> let () = set_transparency cl false in st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier
         ("Typeclasses_Rigid_Settings", i) f)
    [(function
        [cl] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "Typeclasses_Rigid_Settings")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("Typeclasses_Rigid_Settings", i)
         None r)
    [[Egramml.GramTerminal "Typeclasses"; Egramml.GramTerminal "Opaque";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_list wit_reference)),
            Extend.Alist0
              (Extend.Aentry (Pcoq.genarg_grammar wit_reference))))]]

open Genarg

let pr_debug _prc _prlc _prt b = if b then Pp.str "debug" else Pp.mt ()

let wit_debug = Genarg.make0 "debug"
let _ =
  Genintern.register_intern0 wit_debug
    (fun ist v ->
       let ans =
         out_gen (Genarg.glbwit wit_bool)
           (Tacintern.intern_genarg ist
              (Genarg.in_gen (Genarg.rawwit wit_bool) v))
       in
       ist, ans)
let _ =
  Genintern.register_subst0 wit_debug
    (fun s x ->
       out_gen (Genarg.glbwit wit_bool)
         (Tacsubst.subst_genarg s (Genarg.in_gen (Genarg.glbwit wit_bool) x)))
let _ =
  Geninterp.register_interp0 wit_debug
    (fun ist x ->
       Tacinterp.interp_genarg ist (Genarg.in_gen (Genarg.glbwit wit_bool) x))
let _ =
  Geninterp.register_val0 wit_debug
    (Some (Geninterp.val_tag (Genarg.topwit wit_bool)))
let debug =
  let debug =
    Pcoq.create_generic_entry Pcoq.utactic "debug" (Genarg.rawwit wit_debug)
  in
  let () =
    Pcoq.grammar_extend debug None
      (None,
       [None, None,
        [Extend.Rule (Extend.Stop, (fun loc -> false));
         Extend.Rule
           (Extend.Next
              (Extend.Stop, Extend.Atoken (CLexer.terminal "debug")),
            (fun _ loc -> true))]])
  in
  debug
let _ =
  Pptactic.declare_extra_genarg_pprule wit_debug pr_debug pr_debug pr_debug;
  Tacentries.create_ltac_quotation "debug"
    (fun (loc, v) ->
       Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit_debug) v))
    (debug, None)

let pr_search_strategy _prc _prlc _prt =
  function
    Some Dfs -> Pp.str "dfs"
  | Some Bfs -> Pp.str "bfs"
  | None -> Pp.mt ()

let wit_eauto_search_strategy = Genarg.make0 "eauto_search_strategy"
let _ =
  Genintern.register_intern0 wit_eauto_search_strategy (fun ist v -> ist, v)
let _ = Genintern.register_subst0 wit_eauto_search_strategy (fun s v -> v)
let _ =
  Geninterp.register_interp0 wit_eauto_search_strategy
    (fun ist v ->
       Ftactic.return
         (Geninterp.Val.inject
            (Geninterp.val_tag (Genarg.topwit wit_eauto_search_strategy)) v))
let _ = Geninterp.register_val0 wit_eauto_search_strategy None
let eauto_search_strategy =
  let eauto_search_strategy =
    Pcoq.create_generic_entry Pcoq.utactic "eauto_search_strategy"
      (Genarg.rawwit wit_eauto_search_strategy)
  in
  let () =
    Pcoq.grammar_extend eauto_search_strategy None
      (None,
       [None, None,
        [Extend.Rule (Extend.Stop, (fun loc -> None));
         Extend.Rule
           (Extend.Next
              (Extend.Stop, Extend.Atoken (CLexer.terminal "(dfs)")),
            (fun _ loc -> Some Dfs));
         Extend.Rule
           (Extend.Next
              (Extend.Stop, Extend.Atoken (CLexer.terminal "(bfs)")),
            (fun _ loc -> Some Bfs))]])
  in
  eauto_search_strategy
let _ =
  Pptactic.declare_extra_genarg_pprule wit_eauto_search_strategy
    pr_search_strategy pr_search_strategy pr_search_strategy;
  Tacentries.create_ltac_quotation "eauto_search_strategy"
    (fun (loc, v) ->
       Tacexpr.TacGeneric
         (Genarg.in_gen (Genarg.rawwit wit_eauto_search_strategy) v))
    (eauto_search_strategy, None)

(* true = All transparent, false = Opaque if possible *)

let _ =
  (* true = All transparent, false = Opaque if possible *)

  CList.iteri
    (fun i (depr, f) ->
       (* true = All transparent, false = Opaque if possible *)

       Vernacinterp.vinterp_add depr ("Typeclasses_Settings", i) f)
    [(* true = All transparent, false = Opaque if possible *)

     false,
     (function
        [d; s; depth] ->
          let d = Genarg.out_gen (Genarg.rawwit wit_debug) d in
          let s =
            Genarg.out_gen (Genarg.rawwit wit_eauto_search_strategy) s
          in
          let depth =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_opt wit_int)) depth
          in
          (fun ~atts ~st ->
             let () =
               set_typeclasses_debug d;
               Option.iter set_typeclasses_strategy s;
               set_typeclasses_depth depth
             in
             st)
      | _ ->
          (* true = All transparent, false = Opaque if possible *)

          failwith "Extension: cannot occur")];
  (* true = All transparent, false = Opaque if possible *)

  CList.iteri
    (fun i f ->
       (* true = All transparent, false = Opaque if possible *)

       Vernac_classifier.declare_vernac_classifier ("Typeclasses_Settings", i)
         f)
    [(* true = All transparent, false = Opaque if possible *)

     (function
        [d; s; depth] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "Typeclasses_Settings")
      | _ ->
          (* true = All transparent, false = Opaque if possible *)

          failwith "Extension: cannot occur")];
  (* true = All transparent, false = Opaque if possible *)

  CList.iteri
    (fun i r ->
       (* true = All transparent, false = Opaque if possible *)

       Egramml.extend_vernac_command_grammar ("Typeclasses_Settings", i) None
         r)
    [[Egramml.GramTerminal "Typeclasses"; Egramml.GramTerminal "eauto";
      Egramml.GramTerminal ":=";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_debug),
            Extend.Aentry (Pcoq.genarg_grammar wit_debug)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_eauto_search_strategy),
            Extend.Aentry (Pcoq.genarg_grammar wit_eauto_search_strategy)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_opt wit_int)),
            Extend.Aopt (Extend.Aentry (Pcoq.genarg_grammar wit_int))))]]

(** Compatibility: typeclasses eauto has 8.5 and 8.6 modes *)
let _ =
  Tacentries.tactic_extend __coq_plugin_name "typeclasses_eauto" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("typeclasses",
           TyIdent
             ("eauto",
              TyIdent
                ("bfs",
                 TyArg
                   (Loc.tag
                      (Extend.TUopt
                         (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var)),
                       Names.Id.of_string_soft "$d"),
                    TyIdent
                      ("with",
                       TyArg
                         (Loc.tag
                            (Extend.TUlist1
                               (Extend.TUentry
                                  (Genarg.get_arg_tag wit_preident)),
                             Names.Id.of_string_soft "$l"),
                          TyNil)))))),
        (fun d l ist -> typeclasses_eauto ~strategy:Bfs ~depth:d l));
     TyML
       (TyIdent
          ("typeclasses",
           TyIdent
             ("eauto",
              TyArg
                (Loc.tag
                   (Extend.TUopt
                      (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var)),
                    Names.Id.of_string_soft "$d"),
                 TyIdent
                   ("with",
                    TyArg
                      (Loc.tag
                         (Extend.TUlist1
                            (Extend.TUentry
                               (Genarg.get_arg_tag wit_preident)),
                          Names.Id.of_string_soft "$l"),
                       TyNil))))),
        (fun d l ist -> typeclasses_eauto ~depth:d l));
     TyML
       (TyIdent
          ("typeclasses",
           TyIdent
             ("eauto",
              TyArg
                (Loc.tag
                   (Extend.TUopt
                      (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var)),
                    Names.Id.of_string_soft "$d"),
                 TyNil))),
        (fun d ist ->
           typeclasses_eauto ~only_classes:true ~depth:d
             [Hints.typeclasses_db]))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "head_of_constr" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("head_of_constr",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_ident),
                 Names.Id.of_string_soft "$h"),
              TyArg
                (Loc.tag
                   (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                    Names.Id.of_string_soft "$c"),
                 TyNil))),
        (fun h c ist -> head_of_constr h c))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "not_evar" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("not_evar",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$ty"),
              TyNil)),
        (fun ty ist -> not_evar ty))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "is_ground" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("is_ground",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$ty"),
              TyNil)),
        (fun ty ist -> is_ground ty))])

let _ =
  Tacentries.tactic_extend __coq_plugin_name "autoapply" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("autoapply",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_constr),
                 Names.Id.of_string_soft "$c"),
              TyIdent
                ("using",
                 TyArg
                   (Loc.tag
                      (Extend.TUentry (Genarg.get_arg_tag wit_preident),
                       Names.Id.of_string_soft "$i"),
                    TyNil)))),
        (fun c i ist -> autoapply c i))])

(** TODO: DEPRECATE *)
(* A progress test that allows to see if the evars have changed *)
open Constr
open Proofview.Notations

let rec eq_constr_mod_evars sigma x y =
  let open EConstr in
  match EConstr.kind sigma x, EConstr.kind sigma y with
    Evar (e1, l1), Evar (e2, l2) when not (Evar.equal e1 e2) -> true
  | _, _ ->
      compare_constr sigma (fun x y -> eq_constr_mod_evars sigma x y) x y

let progress_evars t =
  Proofview.Goal.enter
    (fun gl ->
       let concl = Proofview.Goal.concl gl in
       let check =
         Proofview.Goal.enter
           (fun gl' ->
              let sigma = Tacmach.New.project gl' in
              let newconcl = Proofview.Goal.concl gl' in
              if eq_constr_mod_evars sigma concl newconcl then
                Tacticals.New.tclFAIL 0
                  (Pp.str "No progress made (modulo evars)")
              else Proofview.tclUNIT ())
       in
       (<*>) t check)

let _ =
  Tacentries.tactic_extend __coq_plugin_name "progress_evars" ~level:0
    Tacentries
    .([TyML
       (TyIdent
          ("progress_evars",
           TyArg
             (Loc.tag
                (Extend.TUentry (Genarg.get_arg_tag wit_tactic),
                 Names.Id.of_string_soft "$t"),
              TyNil)),
        (fun t ist -> progress_evars (Tacinterp.tactic_of_value ist t)))])
