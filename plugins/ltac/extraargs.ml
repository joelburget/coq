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
open Pcoq.Prim
open Pcoq.Constr
open Names
open Tacmach
open Tacexpr
open Taccoerce
open Tacinterp
open Misctypes
open Locus

(** Adding scopes for generic arguments not defined through ARGUMENT EXTEND *)

let create_generic_quotation name e wit =
  let inject (loc, v) =
    Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit) v)
  in
  Tacentries.create_ltac_quotation name inject (e, None)

let () = create_generic_quotation "integer" Pcoq.Prim.integer Stdarg.wit_int
let () = create_generic_quotation "string" Pcoq.Prim.string Stdarg.wit_string

let () = create_generic_quotation "ident" Pcoq.Prim.ident Stdarg.wit_ident
let () =
  create_generic_quotation "reference" Pcoq.Prim.reference Stdarg.wit_ref
let () =
  create_generic_quotation "uconstr" Pcoq.Constr.lconstr Stdarg.wit_uconstr
let () =
  create_generic_quotation "constr" Pcoq.Constr.lconstr Stdarg.wit_constr
let () =
  create_generic_quotation "ipattern" Pltac.simple_intropattern
    Stdarg.wit_intro_pattern
let () =
  create_generic_quotation "open_constr" Pcoq.Constr.lconstr
    Stdarg.wit_open_constr
let () =
  let inject (loc, v) = Tacexpr.Tacexp v in
  Tacentries.create_ltac_quotation "ltac" inject (Pltac.tactic_expr, Some 5)

(** Backward-compatible tactic notation entry names *)

let () =
  let register name entry =
    Tacentries.register_tactic_notation_entry name entry
  in
  register "hyp" wit_var;
  register "simple_intropattern" wit_intro_pattern;
  register "integer" wit_integer;
  register "reference" wit_ref;
  ()

(* Rewriting orientation *)

let _ = Metasyntax.add_token_obj "<-"
let _ = Metasyntax.add_token_obj "->"

let pr_orient _prc _prlc _prt =
  function
    true -> Pp.mt ()
  | false -> Pp.str " <-"

let wit_orient = Genarg.make0 "orient"
let _ =
  Genintern.register_intern0 wit_orient
    (fun ist v ->
       let ans =
         out_gen (Genarg.glbwit wit_bool)
           (Tacintern.intern_genarg ist
              (Genarg.in_gen (Genarg.rawwit wit_bool) v))
       in
       ist, ans)
let _ =
  Genintern.register_subst0 wit_orient
    (fun s x ->
       out_gen (Genarg.glbwit wit_bool)
         (Tacsubst.subst_genarg s (Genarg.in_gen (Genarg.glbwit wit_bool) x)))
let _ =
  Geninterp.register_interp0 wit_orient
    (fun ist x ->
       Tacinterp.interp_genarg ist (Genarg.in_gen (Genarg.glbwit wit_bool) x))
let _ =
  Geninterp.register_val0 wit_orient
    (Some (Geninterp.val_tag (Genarg.topwit wit_bool)))
let orient =
  let orient =
    Pcoq.create_generic_entry Pcoq.utactic "orient" (Genarg.rawwit wit_orient)
  in
  let () =
    Pcoq.grammar_extend orient None
      (None,
       [None, None,
        [Extend.Rule (Extend.Stop, (fun loc -> true));
         Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Atoken (CLexer.terminal "<-")),
            (fun _ loc -> false));
         Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Atoken (CLexer.terminal "->")),
            (fun _ loc -> true))]])
  in
  orient
let _ =
  Pptactic.declare_extra_genarg_pprule wit_orient pr_orient pr_orient
    pr_orient;
  Tacentries.create_ltac_quotation "orient"
    (fun (loc, v) ->
       Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit_orient) v))
    (orient, None)

let pr_int _ _ _ i = Pp.int i

let _natural = Pcoq.Prim.natural

let wit_natural = Genarg.make0 "natural"
let _ =
  Genintern.register_intern0 wit_natural
    (fun ist v ->
       let ans =
         out_gen (Genarg.glbwit wit_int)
           (Tacintern.intern_genarg ist
              (Genarg.in_gen (Genarg.rawwit wit_int) v))
       in
       ist, ans)
let _ =
  Genintern.register_subst0 wit_natural
    (fun s x ->
       out_gen (Genarg.glbwit wit_int)
         (Tacsubst.subst_genarg s (Genarg.in_gen (Genarg.glbwit wit_int) x)))
let _ =
  Geninterp.register_interp0 wit_natural
    (fun ist x ->
       Tacinterp.interp_genarg ist (Genarg.in_gen (Genarg.glbwit wit_int) x))
let _ =
  Geninterp.register_val0 wit_natural
    (Some (Geninterp.val_tag (Genarg.topwit wit_int)))
let natural = let () = Pcoq.register_grammar wit_natural _natural in _natural
let _ =
  Pptactic.declare_extra_genarg_pprule wit_natural pr_int pr_int pr_int;
  Tacentries.create_ltac_quotation "natural"
    (fun (loc, v) ->
       Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit_natural) v))
    (natural, None)

let pr_orient = pr_orient () () ()


let pr_int_list = Pp.pr_sequence Pp.int
let pr_int_list_full _prc _prlc _prt l = pr_int_list l

let pr_occurrences _prc _prlc _prt l =
  match l with
    ArgArg x -> pr_int_list x
  | ArgVar {CAst.loc = loc; v = id} -> Id.print id

let occurrences_of =
  function
    [] -> NoOccurrences
  | n :: _ as nl when n < 0 -> AllOccurrencesBut (List.map abs nl)
  | nl ->
      if List.exists (fun n -> n < 0) nl then
        CErrors.user_err Pp.(str "Illegal negative occurrence number.");
      OnlyOccurrences nl

let coerce_to_int v =
  match Value.to_int v with
    None -> raise (CannotCoerceTo "an integer")
  | Some n -> n

let int_list_of_VList v =
  match Value.to_list v with
    Some l -> List.map (fun n -> coerce_to_int n) l
  | _ -> raise (CannotCoerceTo "an integer")

let interp_occs ist gl l =
  match l with
    ArgArg x -> x
  | ArgVar ({CAst.v = id} as locid) ->
      try int_list_of_VList (Id.Map.find id ist.lfun) with
        Not_found | CannotCoerceTo _ -> [interp_int ist locid]
let interp_occs ist gl l = Tacmach.project gl, interp_occs ist gl l

let glob_occs ist l = l

let subst_occs evm l = l

let wit_occurrences = Genarg.make0 "occurrences"
let _ =
  Genintern.register_intern0 wit_occurrences
    (fun ist v -> ist, glob_occs ist v)
let _ = Genintern.register_subst0 wit_occurrences subst_occs
let _ =
  Geninterp.register_interp0 wit_occurrences
    (let f = interp_occs in
     fun ist v ->
       Ftactic.enter
         (fun gl ->
            let (sigma, v) = Tacmach.New.of_old (fun gl -> f ist gl v) gl in
            let v =
              Geninterp.Val.inject
                (Geninterp.val_tag (Genarg.topwit wit_occurrences)) v
            in
            Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
              (Ftactic.return v)))
let _ =
  Geninterp.register_val0 wit_occurrences
    (Some (Geninterp.val_tag (Genarg.topwit (Genarg.wit_list wit_int))))
let occurrences =
  let occurrences =
    Pcoq.create_generic_entry Pcoq.utactic "occurrences"
      (Genarg.rawwit wit_occurrences)
  in
  let () =
    Pcoq.grammar_extend occurrences None
      (None,
       [None, None,
        [Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Aentry var),
            (fun id loc -> ArgVar id));
         Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Alist1 (Extend.Aentry integer)),
            (fun l loc -> ArgArg l))]])
  in
  occurrences
let _ =
  Pptactic.declare_extra_genarg_pprule wit_occurrences pr_occurrences
    pr_occurrences pr_int_list_full;
  Tacentries.create_ltac_quotation "occurrences"
    (fun (loc, v) ->
       Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit_occurrences) v))
    (occurrences, None)

let pr_occurrences = pr_occurrences () () ()

let pr_gen prc _prlc _prtac c = prc c

let pr_globc _prc _prlc _prtac (_, glob) =
  let (_, env) = Pfedit.get_current_context () in
  Printer.pr_glob_constr_env env glob

let interp_glob ist gl (t, _) = Tacmach.project gl, (ist, t)

let glob_glob = Tacintern.intern_constr

let pr_lconstr _ prc _ c = prc c

let subst_glob = Tacsubst.subst_glob_constr_and_expr

let wit_glob = Genarg.make0 "glob"
let _ =
  Genintern.register_intern0 wit_glob (fun ist v -> ist, glob_glob ist v)
let _ = Genintern.register_subst0 wit_glob subst_glob
let _ =
  Geninterp.register_interp0 wit_glob
    (let f = interp_glob in
     fun ist v ->
       Ftactic.enter
         (fun gl ->
            let (sigma, v) = Tacmach.New.of_old (fun gl -> f ist gl v) gl in
            let v =
              Geninterp.Val.inject
                (Geninterp.val_tag (Genarg.topwit wit_glob)) v
            in
            Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
              (Ftactic.return v)))
let _ = Geninterp.register_val0 wit_glob None
let glob = let () = Pcoq.register_grammar wit_glob constr in constr
let _ =
  Pptactic.declare_extra_genarg_pprule wit_glob pr_gen pr_gen pr_globc;
  Tacentries.create_ltac_quotation "glob"
    (fun (loc, v) ->
       Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit_glob) v))
    (glob, None)

let l_constr = Pcoq.Constr.lconstr

let wit_lconstr = Genarg.make0 "lconstr"
let _ =
  Genintern.register_intern0 wit_lconstr
    (fun ist v ->
       let ans =
         out_gen (Genarg.glbwit wit_constr)
           (Tacintern.intern_genarg ist
              (Genarg.in_gen (Genarg.rawwit wit_constr) v))
       in
       ist, ans)
let _ =
  Genintern.register_subst0 wit_lconstr
    (fun s x ->
       out_gen (Genarg.glbwit wit_constr)
         (Tacsubst.subst_genarg s
            (Genarg.in_gen (Genarg.glbwit wit_constr) x)))
let _ =
  Geninterp.register_interp0 wit_lconstr
    (fun ist x ->
       Tacinterp.interp_genarg ist
         (Genarg.in_gen (Genarg.glbwit wit_constr) x))
let _ =
  Geninterp.register_val0 wit_lconstr
    (Some (Geninterp.val_tag (Genarg.topwit wit_constr)))
let lconstr = let () = Pcoq.register_grammar wit_lconstr l_constr in l_constr
let _ =
  Pptactic.declare_extra_genarg_pprule wit_lconstr pr_lconstr pr_lconstr
    pr_lconstr;
  Tacentries.create_ltac_quotation "lconstr"
    (fun (loc, v) ->
       Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit_lconstr) v))
    (lconstr, None)

let wit_lglob = Genarg.make0 "lglob"
let _ =
  Genintern.register_intern0 wit_lglob (fun ist v -> ist, glob_glob ist v)
let _ = Genintern.register_subst0 wit_lglob subst_glob
let _ =
  Geninterp.register_interp0 wit_lglob
    (let f = interp_glob in
     fun ist v ->
       Ftactic.enter
         (fun gl ->
            let (sigma, v) = Tacmach.New.of_old (fun gl -> f ist gl v) gl in
            let v =
              Geninterp.Val.inject
                (Geninterp.val_tag (Genarg.topwit wit_lglob)) v
            in
            Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
              (Ftactic.return v)))
let _ =
  Geninterp.register_val0 wit_lglob
    (Some (Geninterp.val_tag (Genarg.topwit wit_glob)))
let lglob = let () = Pcoq.register_grammar wit_lglob lconstr in lconstr
let _ =
  Pptactic.declare_extra_genarg_pprule wit_lglob pr_gen pr_gen pr_globc;
  Tacentries.create_ltac_quotation "lglob"
    (fun (loc, v) ->
       Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit_lglob) v))
    (lglob, None)

let interp_casted_constr ist gl c =
  interp_constr_gen (Pretyping.OfType (pf_concl gl)) ist (pf_env gl)
    (project gl) c

let wit_casted_constr = Genarg.make0 "casted_constr"
let _ =
  Genintern.register_intern0 wit_casted_constr
    (fun ist v ->
       let ans =
         out_gen (Genarg.glbwit wit_constr)
           (Tacintern.intern_genarg ist
              (Genarg.in_gen (Genarg.rawwit wit_constr) v))
       in
       ist, ans)
let _ =
  Genintern.register_subst0 wit_casted_constr
    (fun s x ->
       out_gen (Genarg.glbwit wit_constr)
         (Tacsubst.subst_genarg s
            (Genarg.in_gen (Genarg.glbwit wit_constr) x)))
let _ =
  Geninterp.register_interp0 wit_casted_constr
    (let f = interp_casted_constr in
     fun ist v ->
       Ftactic.enter
         (fun gl ->
            let (sigma, v) = Tacmach.New.of_old (fun gl -> f ist gl v) gl in
            let v =
              Geninterp.Val.inject
                (Geninterp.val_tag (Genarg.topwit wit_constr)) v
            in
            Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
              (Ftactic.return v)))
let _ =
  Geninterp.register_val0 wit_casted_constr
    (Some (Geninterp.val_tag (Genarg.topwit wit_constr)))
let casted_constr =
  let () = Pcoq.register_grammar wit_casted_constr constr in constr
let _ =
  Pptactic.declare_extra_genarg_pprule wit_casted_constr pr_gen pr_gen pr_gen;
  Tacentries.create_ltac_quotation "casted_constr"
    (fun (loc, v) ->
       Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit_casted_constr) v))
    (casted_constr, None)

type 'id gen_place = ('id * hyp_location_flag, unit) location

type loc_place = lident gen_place
type place = Id.t gen_place

let pr_gen_place pr_id =
  function
    ConclLocation () -> Pp.mt ()
  | HypLocation (id, InHyp) -> (++) (str "in ") (pr_id id)
  | HypLocation (id, InHypTypeOnly) ->
      (++) ((++) (str "in (Type of ") (pr_id id)) (str ")")
  | HypLocation (id, InHypValueOnly) ->
      (++) ((++) (str "in (Value of ") (pr_id id)) (str ")")

let pr_loc_place _ _ _ = pr_gen_place (fun {CAst.v = id} -> Id.print id)
let pr_place _ _ _ = pr_gen_place Id.print
let pr_hloc = pr_loc_place () () ()

let intern_place ist =
  function
    ConclLocation () -> ConclLocation ()
  | HypLocation (id, hl) -> HypLocation (Tacintern.intern_hyp ist id, hl)

let interp_place ist env sigma =
  function
    ConclLocation () -> ConclLocation ()
  | HypLocation (id, hl) ->
      HypLocation (Tacinterp.interp_hyp ist env sigma id, hl)

let interp_place ist gl p =
  Tacmach.project gl,
  interp_place ist (Tacmach.pf_env gl) (Tacmach.project gl) p

let subst_place subst pl = pl

let wit_hloc = Genarg.make0 "hloc"
let _ =
  Genintern.register_intern0 wit_hloc (fun ist v -> ist, intern_place ist v)
let _ = Genintern.register_subst0 wit_hloc subst_place
let _ =
  Geninterp.register_interp0 wit_hloc
    (let f = interp_place in
     fun ist v ->
       Ftactic.enter
         (fun gl ->
            let (sigma, v) = Tacmach.New.of_old (fun gl -> f ist gl v) gl in
            let v =
              Geninterp.Val.inject
                (Geninterp.val_tag (Genarg.topwit wit_hloc)) v
            in
            Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
              (Ftactic.return v)))
let _ = Geninterp.register_val0 wit_hloc None
let hloc =
  let hloc =
    Pcoq.create_generic_entry Pcoq.utactic "hloc" (Genarg.rawwit wit_hloc)
  in
  let () =
    Pcoq.grammar_extend hloc None
      (None,
       [None, None,
        [Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next
                    (Extend.Next
                       (Extend.Next
                          (Extend.Next
                             (Extend.Stop,
                              Extend.Atoken (CLexer.terminal "in")),
                           Extend.Atoken (CLexer.terminal "(")),
                        Extend.Atoken (CLexer.terminal "Value")),
                     Extend.Atoken (CLexer.terminal "of")),
                  Extend.Aentry ident),
               Extend.Atoken (CLexer.terminal ")")),
            (fun _ id _ _ _ _ loc ->
               HypLocation (CAst.make id, InHypValueOnly)));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next
                    (Extend.Next
                       (Extend.Next
                          (Extend.Next
                             (Extend.Stop,
                              Extend.Atoken (CLexer.terminal "in")),
                           Extend.Atoken (CLexer.terminal "(")),
                        Extend.Atoken (CLexer.terminal "Type")),
                     Extend.Atoken (CLexer.terminal "of")),
                  Extend.Aentry ident),
               Extend.Atoken (CLexer.terminal ")")),
            (fun _ id _ _ _ _ loc ->
               HypLocation (CAst.make id, InHypTypeOnly)));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "in")),
               Extend.Aentry ident),
            (fun id _ loc -> HypLocation (CAst.make id, InHyp)));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next
                    (Extend.Stop, Extend.Atoken (CLexer.terminal "in")),
                  Extend.Atoken (CLexer.terminal "|-")),
               Extend.Atoken (CLexer.terminal "*")),
            (fun _ _ _ loc -> ConclLocation ()));
         Extend.Rule (Extend.Stop, (fun loc -> ConclLocation ()))]])
  in
  hloc
let _ =
  Pptactic.declare_extra_genarg_pprule wit_hloc pr_loc_place pr_loc_place
    pr_place;
  Tacentries.create_ltac_quotation "hloc"
    (fun (loc, v) ->
       Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit_hloc) v))
    (hloc, None)

let pr_rename _ _ _ (n, m) =
  (++) ((++) (Id.print n) (str " into ")) (Id.print m)

let wit_rename = Genarg.make0 "rename"
let _ =
  Genintern.register_intern0 wit_rename
    (fun ist v ->
       let ans =
         out_gen (Genarg.glbwit (Genarg.wit_pair wit_ident wit_ident))
           (Tacintern.intern_genarg ist
              (Genarg.in_gen
                 (Genarg.rawwit (Genarg.wit_pair wit_ident wit_ident)) v))
       in
       ist, ans)
let _ =
  Genintern.register_subst0 wit_rename
    (fun s x ->
       out_gen (Genarg.glbwit (Genarg.wit_pair wit_ident wit_ident))
         (Tacsubst.subst_genarg s
            (Genarg.in_gen
               (Genarg.glbwit (Genarg.wit_pair wit_ident wit_ident)) x)))
let _ =
  Geninterp.register_interp0 wit_rename
    (fun ist x ->
       Tacinterp.interp_genarg ist
         (Genarg.in_gen (Genarg.glbwit (Genarg.wit_pair wit_ident wit_ident))
            x))
let _ =
  Geninterp.register_val0 wit_rename
    (Some
       (Geninterp.val_tag
          (Genarg.topwit (Genarg.wit_pair wit_ident wit_ident))))
let rename =
  let rename =
    Pcoq.create_generic_entry Pcoq.utactic "rename" (Genarg.rawwit wit_rename)
  in
  let () =
    Pcoq.grammar_extend rename None
      (None,
       [None, None,
        [Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next (Extend.Stop, Extend.Aentry ident),
                  Extend.Atoken (CLexer.terminal "into")),
               Extend.Aentry ident),
            (fun m _ n loc -> n, m))]])
  in
  rename
let _ =
  Pptactic.declare_extra_genarg_pprule wit_rename pr_rename pr_rename
    pr_rename;
  Tacentries.create_ltac_quotation "rename"
    (fun (loc, v) ->
       Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit_rename) v))
    (rename, None)

(* Julien: Mise en commun des differentes version de replace with in by *)

let pr_by_arg_tac _prc _prlc prtac opt_c =
  match opt_c with
    None -> mt ()
  | Some t ->
      hov 2 ((++) ((++) (str "by") (spc ())) (prtac (3, Notation_term.E) t))

let wit_by_arg_tac = Genarg.make0 "by_arg_tac"
let _ =
  Genintern.register_intern0 wit_by_arg_tac
    (fun ist v ->
       let ans =
         out_gen (Genarg.glbwit (Genarg.wit_opt wit_tactic))
           (Tacintern.intern_genarg ist
              (Genarg.in_gen (Genarg.rawwit (Genarg.wit_opt wit_tactic)) v))
       in
       ist, ans)
let _ =
  Genintern.register_subst0 wit_by_arg_tac
    (fun s x ->
       out_gen (Genarg.glbwit (Genarg.wit_opt wit_tactic))
         (Tacsubst.subst_genarg s
            (Genarg.in_gen (Genarg.glbwit (Genarg.wit_opt wit_tactic)) x)))
let _ =
  Geninterp.register_interp0 wit_by_arg_tac
    (fun ist x ->
       Tacinterp.interp_genarg ist
         (Genarg.in_gen (Genarg.glbwit (Genarg.wit_opt wit_tactic)) x))
let _ =
  Geninterp.register_val0 wit_by_arg_tac
    (Some (Geninterp.val_tag (Genarg.topwit (Genarg.wit_opt wit_tactic))))
let by_arg_tac =
  let by_arg_tac =
    Pcoq.create_generic_entry Pcoq.utactic "by_arg_tac"
      (Genarg.rawwit wit_by_arg_tac)
  in
  let () =
    Pcoq.grammar_extend by_arg_tac None
      (None,
       [None, None,
        [Extend.Rule (Extend.Stop, (fun loc -> None));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "by")),
               Extend.Aentryl (Pltac.tactic_expr, 3)),
            (fun c _ loc -> Some c))]])
  in
  by_arg_tac
let _ =
  Pptactic.declare_extra_genarg_pprule wit_by_arg_tac pr_by_arg_tac
    pr_by_arg_tac pr_by_arg_tac;
  Tacentries.create_ltac_quotation "by_arg_tac"
    (fun (loc, v) ->
       Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit_by_arg_tac) v))
    (by_arg_tac, None)

let pr_by_arg_tac prtac opt_c = pr_by_arg_tac () () prtac opt_c

let pr_in_clause _ _ _ cl = Pptactic.pr_in_clause Ppconstr.pr_lident cl
let pr_in_top_clause _ _ _ cl = Pptactic.pr_in_clause Id.print cl
let in_clause' = Pltac.in_clause

let wit_in_clause = Genarg.make0 "in_clause"
let _ =
  Genintern.register_intern0 wit_in_clause
    (fun ist v ->
       let ans =
         out_gen (Genarg.glbwit wit_clause_dft_concl)
           (Tacintern.intern_genarg ist
              (Genarg.in_gen (Genarg.rawwit wit_clause_dft_concl) v))
       in
       ist, ans)
let _ =
  Genintern.register_subst0 wit_in_clause
    (fun s x ->
       out_gen (Genarg.glbwit wit_clause_dft_concl)
         (Tacsubst.subst_genarg s
            (Genarg.in_gen (Genarg.glbwit wit_clause_dft_concl) x)))
let _ =
  Geninterp.register_interp0 wit_in_clause
    (fun ist x ->
       Tacinterp.interp_genarg ist
         (Genarg.in_gen (Genarg.glbwit wit_clause_dft_concl) x))
let _ =
  Geninterp.register_val0 wit_in_clause
    (Some (Geninterp.val_tag (Genarg.topwit wit_clause_dft_concl)))
let in_clause =
  let () = Pcoq.register_grammar wit_in_clause in_clause' in in_clause'
let _ =
  Pptactic.declare_extra_genarg_pprule wit_in_clause pr_in_clause pr_in_clause
    pr_in_top_clause;
  Tacentries.create_ltac_quotation "in_clause"
    (fun (loc, v) ->
       Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit_in_clause) v))
    (in_clause, None)

let local_test_lpar_id_colon =
  let err () = raise Stream.Failure in
  Pcoq.Gram.Entry.of_parser "lpar_id_colon"
    (fun strm ->
       match Util.stream_nth 0 strm with
         Tok.KEYWORD "(" ->
           begin match Util.stream_nth 1 strm with
             Tok.IDENT _ ->
               begin match Util.stream_nth 2 strm with
                 Tok.KEYWORD ":" -> ()
               | _ -> err ()
               end
           | _ -> err ()
           end
       | _ -> err ())

let pr_lpar_id_colon _ _ _ _ = mt ()

let wit_test_lpar_id_colon = Genarg.make0 "test_lpar_id_colon"
let _ =
  Genintern.register_intern0 wit_test_lpar_id_colon
    (fun ist v ->
       let ans =
         out_gen (Genarg.glbwit wit_unit)
           (Tacintern.intern_genarg ist
              (Genarg.in_gen (Genarg.rawwit wit_unit) v))
       in
       ist, ans)
let _ =
  Genintern.register_subst0 wit_test_lpar_id_colon
    (fun s x ->
       out_gen (Genarg.glbwit wit_unit)
         (Tacsubst.subst_genarg s (Genarg.in_gen (Genarg.glbwit wit_unit) x)))
let _ =
  Geninterp.register_interp0 wit_test_lpar_id_colon
    (fun ist x ->
       Tacinterp.interp_genarg ist (Genarg.in_gen (Genarg.glbwit wit_unit) x))
let _ =
  Geninterp.register_val0 wit_test_lpar_id_colon
    (Some (Geninterp.val_tag (Genarg.topwit wit_unit)))
let test_lpar_id_colon =
  let test_lpar_id_colon =
    Pcoq.create_generic_entry Pcoq.utactic "test_lpar_id_colon"
      (Genarg.rawwit wit_test_lpar_id_colon)
  in
  let () =
    Pcoq.grammar_extend test_lpar_id_colon None
      (None,
       [None, None,
        [Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Aentry local_test_lpar_id_colon),
            (fun x loc -> ()))]])
  in
  test_lpar_id_colon
let _ =
  Pptactic.declare_extra_genarg_pprule wit_test_lpar_id_colon pr_lpar_id_colon
    pr_lpar_id_colon pr_lpar_id_colon;
  Tacentries.create_ltac_quotation "test_lpar_id_colon"
    (fun (loc, v) ->
       Tacexpr.TacGeneric
         (Genarg.in_gen (Genarg.rawwit wit_test_lpar_id_colon) v))
    (test_lpar_id_colon, None)

    (*
(* spiwack: the print functions are incomplete, but I don't know what they are
	used for *)
let pr_r_nat_field natf =
  (++) (str "nat ")
    (match natf with
       Retroknowledge.NatType -> str "type"
     | Retroknowledge.NatPlus -> str "plus"
     | Retroknowledge.NatTimes -> str "times")

let pr_r_n_field nf =
  (++) (str "binary N ")
    (match nf with
       Retroknowledge.NPositive -> str "positive"
     | Retroknowledge.NType -> str "type"
     | Retroknowledge.NTwice -> str "twice"
     | Retroknowledge.NTwicePlusOne -> str "twice plus one"
     | Retroknowledge.NPhi -> str "phi"
     | Retroknowledge.NPhiInv -> str "phi inv"
     | Retroknowledge.NPlus -> str "plus"
     | Retroknowledge.NTimes -> str "times")

let pr_r_int31_field i31f =
  (++) (str "int31 ")
    (match i31f with
       Retroknowledge.Int31Bits -> str "bits"
     | Retroknowledge.Int31Type -> str "type"
     | Retroknowledge.Int31Twice -> str "twice"
     | Retroknowledge.Int31TwicePlusOne -> str "twice plus one"
     | Retroknowledge.Int31Phi -> str "phi"
     | Retroknowledge.Int31PhiInv -> str "phi inv"
     | Retroknowledge.Int31Plus -> str "plus"
     | Retroknowledge.Int31Times -> str "times"
     | Retroknowledge.Int31Constructor -> assert false
     | Retroknowledge.Int31PlusC -> str "plusc"
     | Retroknowledge.Int31PlusCarryC -> str "pluscarryc"
     | Retroknowledge.Int31Minus -> str "minus"
     | Retroknowledge.Int31MinusC -> str "minusc"
     | Retroknowledge.Int31MinusCarryC -> str "minuscarryc"
     | Retroknowledge.Int31TimesC -> str "timesc"
     | Retroknowledge.Int31Div21 -> str "div21"
     | Retroknowledge.Int31Div -> str "div"
     | Retroknowledge.Int31Diveucl -> str "diveucl"
     | Retroknowledge.Int31AddMulDiv -> str "addmuldiv"
     | Retroknowledge.Int31Compare -> str "compare"
     | Retroknowledge.Int31Head0 -> str "head0"
     | Retroknowledge.Int31Tail0 -> str "tail0"
     | Retroknowledge.Int31Lor -> str "lor"
     | Retroknowledge.Int31Land -> str "land"
     | Retroknowledge.Int31Lxor -> str "lxor")

let pr_retroknowledge_field f =
  match f with
    Retroknowledge.KInt31 (group, i31f) ->
      (++) ((++) ((++) (pr_r_int31_field i31f) (spc ())) (str "in "))
        (qs group)

let (wit_retroknowledge_nat : ('a, unit, unit) Genarg.genarg_type) =
  Genarg.create_arg "retroknowledge_nat"
let retroknowledge_nat =
  let retroknowledge_nat =
    Pcoq.create_generic_entry Pcoq.utactic "retroknowledge_nat"
      (Genarg.rawwit wit_retroknowledge_nat)
  in
  let () =
    Pcoq.grammar_extend retroknowledge_nat None
      (None,
       [None, None,
        [Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "nat")),
               Extend.Atoken (CLexer.terminal "times")),
            (fun _ _ loc -> Retroknowledge.NatTimes));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "nat")),
               Extend.Atoken (CLexer.terminal "plus")),
            (fun _ _ loc -> Retroknowledge.NatPlus));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "nat")),
               Extend.Atoken (CLexer.terminal "type")),
            (fun _ _ loc -> Retroknowledge.NatType))]])
  in
  retroknowledge_nat
let _ =
  Pptactic.declare_extra_vernac_genarg_pprule wit_retroknowledge_nat
    (fun _ _ _ -> pr_r_nat_field)


let (wit_retroknowledge_binary_n : ('a, unit, unit) Genarg.genarg_type) =
  Genarg.create_arg "retroknowledge_binary_n"
let retroknowledge_binary_n =
  let retroknowledge_binary_n =
    Pcoq.create_generic_entry Pcoq.utactic "retroknowledge_binary_n"
      (Genarg.rawwit wit_retroknowledge_binary_n)
  in
  let () =
    Pcoq.grammar_extend retroknowledge_binary_n None
      (None,
       [None, None,
        [Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next
                    (Extend.Stop, Extend.Atoken (CLexer.terminal "binary")),
                  Extend.Atoken (CLexer.terminal "N")),
               Extend.Atoken (CLexer.terminal "times")),
            (fun _ _ _ loc -> Retroknowledge.NTimes));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next
                    (Extend.Stop, Extend.Atoken (CLexer.terminal "binary")),
                  Extend.Atoken (CLexer.terminal "N")),
               Extend.Atoken (CLexer.terminal "plus")),
            (fun _ _ _ loc -> Retroknowledge.NPlus));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next
                    (Extend.Next
                       (Extend.Stop,
                        Extend.Atoken (CLexer.terminal "binary")),
                     Extend.Atoken (CLexer.terminal "N")),
                  Extend.Atoken (CLexer.terminal "phi")),
               Extend.Atoken (CLexer.terminal "inv")),
            (fun _ _ _ _ loc -> Retroknowledge.NPhiInv));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next
                    (Extend.Stop, Extend.Atoken (CLexer.terminal "binary")),
                  Extend.Atoken (CLexer.terminal "N")),
               Extend.Atoken (CLexer.terminal "phi")),
            (fun _ _ _ loc -> Retroknowledge.NPhi));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next
                    (Extend.Next
                       (Extend.Next
                          (Extend.Stop,
                           Extend.Atoken (CLexer.terminal "binary")),
                        Extend.Atoken (CLexer.terminal "N")),
                     Extend.Atoken (CLexer.terminal "twice")),
                  Extend.Atoken (CLexer.terminal "plus")),
               Extend.Atoken (CLexer.terminal "one")),
            (fun _ _ _ _ _ loc -> Retroknowledge.NTwicePlusOne));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next
                    (Extend.Stop, Extend.Atoken (CLexer.terminal "binary")),
                  Extend.Atoken (CLexer.terminal "N")),
               Extend.Atoken (CLexer.terminal "twice")),
            (fun _ _ _ loc -> Retroknowledge.NTwice));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next
                    (Extend.Stop, Extend.Atoken (CLexer.terminal "binary")),
                  Extend.Atoken (CLexer.terminal "N")),
               Extend.Atoken (CLexer.terminal "type")),
            (fun _ _ _ loc -> Retroknowledge.NType));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next
                    (Extend.Stop, Extend.Atoken (CLexer.terminal "binary")),
                  Extend.Atoken (CLexer.terminal "N")),
               Extend.Atoken (CLexer.terminal "positive")),
            (fun _ _ _ loc -> Retroknowledge.NPositive))]])
  in
  retroknowledge_binary_n
let _ =
  Pptactic.declare_extra_vernac_genarg_pprule wit_retroknowledge_binary_n
    (fun _ _ _ -> pr_r_n_field)

let (wit_retroknowledge_int31 : ('a, unit, unit) Genarg.genarg_type) =
  Genarg.create_arg "retroknowledge_int31"
let retroknowledge_int31 =
  let retroknowledge_int31 =
    Pcoq.create_generic_entry Pcoq.utactic "retroknowledge_int31"
      (Genarg.rawwit wit_retroknowledge_int31)
  in
  let () =
    Pcoq.grammar_extend retroknowledge_int31 None
      (None,
       [None, None,
        [Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
               Extend.Atoken (CLexer.terminal "lxor")),
            (fun _ _ loc -> Retroknowledge.Int31Lxor));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
               Extend.Atoken (CLexer.terminal "land")),
            (fun _ _ loc -> Retroknowledge.Int31Land));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
               Extend.Atoken (CLexer.terminal "lor")),
            (fun _ _ loc -> Retroknowledge.Int31Lor));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
               Extend.Atoken (CLexer.terminal "tail0")),
            (fun _ _ loc -> Retroknowledge.Int31Tail0));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
               Extend.Atoken (CLexer.terminal "head0")),
            (fun _ _ loc -> Retroknowledge.Int31Head0));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
               Extend.Atoken (CLexer.terminal "compare")),
            (fun _ _ loc -> Retroknowledge.Int31Compare));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
               Extend.Atoken (CLexer.terminal "addmuldiv")),
            (fun _ _ loc -> Retroknowledge.Int31AddMulDiv));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
               Extend.Atoken (CLexer.terminal "diveucl")),
            (fun _ _ loc -> Retroknowledge.Int31Diveucl));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
               Extend.Atoken (CLexer.terminal "div")),
            (fun _ _ loc -> Retroknowledge.Int31Div));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
               Extend.Atoken (CLexer.terminal "div21")),
            (fun _ _ loc -> Retroknowledge.Int31Div21));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
               Extend.Atoken (CLexer.terminal "timesc")),
            (fun _ _ loc -> Retroknowledge.Int31TimesC));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
               Extend.Atoken (CLexer.terminal "times")),
            (fun _ _ loc -> Retroknowledge.Int31Times));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
               Extend.Atoken (CLexer.terminal "minuscarryc")),
            (fun _ _ loc -> Retroknowledge.Int31MinusCarryC));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
               Extend.Atoken (CLexer.terminal "minusc")),
            (fun _ _ loc -> Retroknowledge.Int31MinusC));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
               Extend.Atoken (CLexer.terminal "minus")),
            (fun _ _ loc -> Retroknowledge.Int31Minus));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
               Extend.Atoken (CLexer.terminal "pluscarryc")),
            (fun _ _ loc -> Retroknowledge.Int31PlusCarryC));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
               Extend.Atoken (CLexer.terminal "plusc")),
            (fun _ _ loc -> Retroknowledge.Int31PlusC));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
               Extend.Atoken (CLexer.terminal "plus")),
            (fun _ _ loc -> Retroknowledge.Int31Plus));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next
                    (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
                  Extend.Atoken (CLexer.terminal "phi")),
               Extend.Atoken (CLexer.terminal "inv")),
            (fun _ _ _ loc -> Retroknowledge.Int31PhiInv));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
               Extend.Atoken (CLexer.terminal "phi")),
            (fun _ _ loc -> Retroknowledge.Int31Phi));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next
                    (Extend.Next
                       (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
                     Extend.Atoken (CLexer.terminal "twice")),
                  Extend.Atoken (CLexer.terminal "plus")),
               Extend.Atoken (CLexer.terminal "one")),
            (fun _ _ _ _ loc -> Retroknowledge.Int31TwicePlusOne));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
               Extend.Atoken (CLexer.terminal "twice")),
            (fun _ _ loc -> Retroknowledge.Int31Twice));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
               Extend.Atoken (CLexer.terminal "type")),
            (fun _ _ loc -> Retroknowledge.Int31Type));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "int31")),
               Extend.Atoken (CLexer.terminal "bits")),
            (fun _ _ loc -> Retroknowledge.Int31Bits))]])
  in
  retroknowledge_int31
let _ =
  Pptactic.declare_extra_vernac_genarg_pprule wit_retroknowledge_int31
    (fun _ _ _ -> pr_r_int31_field)

let (wit_retroknowledge_field : ('a, unit, unit) Genarg.genarg_type) =
  Genarg.create_arg "retroknowledge_field"
let retroknowledge_field =
  let retroknowledge_field =
    Pcoq.create_generic_entry Pcoq.utactic "retroknowledge_field"
      (Genarg.rawwit wit_retroknowledge_field)
  in
  let () =
    Pcoq.grammar_extend retroknowledge_field None
      (None,
       [None, None,
        [Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next
                    (Extend.Stop, Extend.Aentry retroknowledge_int31),
                  Extend.Atoken (CLexer.terminal "in")),
               Extend.Aentry string),
            (fun g _ i loc -> Retroknowledge.KInt31 (g, i)))]])
  in
  retroknowledge_field
let _ =
  Pptactic.declare_extra_vernac_genarg_pprule wit_retroknowledge_field
    (fun _ _ _ -> pr_retroknowledge_field)
    *)
