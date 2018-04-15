(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constrexpr
open Vernacexpr
open Misctypes

open Pcoq
open Pcoq.Prim
open Pcoq.Constr
open Pcoq.Vernac_

let thm_token = G_vernac.thm_token

let hint = Gram.entry_create "hint"

let warn_deprecated_focus =
  CWarnings.create ~name:"deprecated-focus" ~category:"deprecated"
    (fun () ->
       Pp.strbrk
         "The Focus command is deprecated; use bullets or focusing brackets instead")

let warn_deprecated_focus_n n =
  CWarnings.create ~name:"deprecated-focus" ~category:"deprecated"
    (fun () ->
       Pp
       .((++)
         ((++)
            ((++) ((++) (str "The Focus command is deprecated;") (spc ()))
               (str "use '"))
            (int n))
         (str ": {' instead")))

let warn_deprecated_unfocus =
  CWarnings.create ~name:"deprecated-unfocus" ~category:"deprecated"
    (fun () -> Pp.strbrk "The Unfocus command is deprecated")

(* Proof commands *)
let _ =
  let _ = (hint : 'hint Gram.Entry.e)
  and _ = (command : 'command Gram.Entry.e) in
  let grammar_entry_create = Gram.Entry.create in
  let opt_hintbases : 'opt_hintbases Gram.Entry.e =
    grammar_entry_create "opt_hintbases"
  and reference_or_constr : 'reference_or_constr Gram.Entry.e =
    grammar_entry_create "reference_or_constr"
  and constr_body : 'constr_body Gram.Entry.e =
    grammar_entry_create "constr_body"
  and mode : 'mode Gram.Entry.e = grammar_entry_create "mode" in
  Gram.extend (opt_hintbases : 'opt_hintbases Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", ":");
       Gramext.Slist1
         (Gramext.srules
            [[Gramext.Stoken ("IDENT", "")],
             Gramext.action
               (fun (id : string) (loc : Ploc.t) -> (id : 'e__1))])],
      Gramext.action
        (fun (l : 'e__1 list) _ (loc : Ploc.t) -> (l : 'opt_hintbases));
      [], Gramext.action (fun (loc : Ploc.t) -> ([] : 'opt_hintbases))]];
  Gram.extend (command : 'command Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "Hint"); Gramext.Stoken ("IDENT", "Resolve");
       Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj
               (reference_or_constr : 'reference_or_constr Gram.Entry.e)));
       Gramext.Snterm (Gram.Entry.obj (hint_info : 'hint_info Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (opt_hintbases : 'opt_hintbases Gram.Entry.e))],
      Gramext.action
        (fun (dbnames : 'opt_hintbases) (info : 'hint_info)
             (lc : 'reference_or_constr list) _ _ (loc : Ploc.t) ->
           (VernacHints
              (dbnames, HintsResolve (List.map (fun x -> info, true, x) lc)) :
            'command));
      [Gramext.Stoken ("IDENT", "Hint");
       Gramext.Snterm (Gram.Entry.obj (hint : 'hint Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (opt_hintbases : 'opt_hintbases Gram.Entry.e))],
      Gramext.action
        (fun (dbnames : 'opt_hintbases) (h : 'hint) _ (loc : Ploc.t) ->
           (VernacHints (dbnames, h) : 'command));
      [Gramext.Stoken ("IDENT", "Remove"); Gramext.Stoken ("IDENT", "Hints");
       Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e)));
       Gramext.Snterm
         (Gram.Entry.obj (opt_hintbases : 'opt_hintbases Gram.Entry.e))],
      Gramext.action
        (fun (dbnames : 'opt_hintbases) (ids : 'global list) _ _
             (loc : Ploc.t) ->
           (VernacRemoveHints (dbnames, ids) : 'command));
      [Gramext.Stoken ("IDENT", "Create"); Gramext.Stoken ("IDENT", "HintDb");
       Gramext.Stoken ("IDENT", "");
       Gramext.srules
         [[], Gramext.action (fun (loc : Ploc.t) -> (false : 'e__2));
          [Gramext.Stoken ("", "discriminated")],
          Gramext.action (fun _ (loc : Ploc.t) -> (true : 'e__2))]],
      Gramext.action
        (fun (b : 'e__2) (id : string) _ _ (loc : Ploc.t) ->
           (VernacCreateHintDb (id, b) : 'command));
      [Gramext.Stoken ("IDENT", "Guarded")],
      Gramext.action (fun _ (loc : Ploc.t) -> (VernacCheckGuard : 'command));
      [Gramext.Stoken ("IDENT", "Show"); Gramext.Stoken ("IDENT", "Match");
       Gramext.Snterm (Gram.Entry.obj (reference : 'reference Gram.Entry.e))],
      Gramext.action
        (fun (id : 'reference) _ _ (loc : Ploc.t) ->
           (VernacShow (ShowMatch id) : 'command));
      [Gramext.Stoken ("IDENT", "Show"); Gramext.Stoken ("IDENT", "Intros")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) -> (VernacShow (ShowIntros true) : 'command));
      [Gramext.Stoken ("IDENT", "Show"); Gramext.Stoken ("IDENT", "Intro")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) ->
           (VernacShow (ShowIntros false) : 'command));
      [Gramext.Stoken ("IDENT", "Show"); Gramext.Stoken ("IDENT", "Proof")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) -> (VernacShow ShowProof : 'command));
      [Gramext.Stoken ("IDENT", "Show");
       Gramext.Stoken ("IDENT", "Conjectures")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) -> (VernacShow ShowProofNames : 'command));
      [Gramext.Stoken ("IDENT", "Show");
       Gramext.Stoken ("IDENT", "Universes")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) -> (VernacShow ShowUniverses : 'command));
      [Gramext.Stoken ("IDENT", "Show");
       Gramext.Stoken ("IDENT", "Existentials")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) -> (VernacShow ShowExistentials : 'command));
      [Gramext.Stoken ("IDENT", "Show"); Gramext.Stoken ("IDENT", "Script")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) -> (VernacShow ShowScript : 'command));
      [Gramext.Stoken ("IDENT", "Show");
       Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e))],
      Gramext.action
        (fun (id : 'ident) _ (loc : Ploc.t) ->
           (VernacShow (ShowGoal (GoalId id)) : 'command));
      [Gramext.Stoken ("IDENT", "Show");
       Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e))],
      Gramext.action
        (fun (n : 'natural) _ (loc : Ploc.t) ->
           (VernacShow (ShowGoal (NthGoal n)) : 'command));
      [Gramext.Stoken ("IDENT", "Show")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           (VernacShow (ShowGoal OpenSubgoals) : 'command));
      [Gramext.Stoken ("IDENT", "Unfocused")],
      Gramext.action (fun _ (loc : Ploc.t) -> (VernacUnfocused : 'command));
      [Gramext.Stoken ("IDENT", "Unfocus")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           (warn_deprecated_unfocus ~loc:((!@) loc) (); VernacUnfocus :
            'command));
      [Gramext.Stoken ("IDENT", "Focus");
       Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e))],
      Gramext.action
        (fun (n : 'natural) _ (loc : Ploc.t) ->
           (warn_deprecated_focus_n n ~loc:((!@) loc) ();
            VernacFocus (Some n) :
            'command));
      [Gramext.Stoken ("IDENT", "Focus")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           (warn_deprecated_focus ~loc:((!@) loc) (); VernacFocus None :
            'command));
      [Gramext.Stoken ("IDENT", "Undo"); Gramext.Stoken ("IDENT", "To");
       Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e))],
      Gramext.action
        (fun (n : 'natural) _ _ (loc : Ploc.t) ->
           (VernacUndoTo n : 'command));
      [Gramext.Stoken ("IDENT", "Undo");
       Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e))],
      Gramext.action
        (fun (n : 'natural) _ (loc : Ploc.t) -> (VernacUndo n : 'command));
      [Gramext.Stoken ("IDENT", "Undo")],
      Gramext.action (fun _ (loc : Ploc.t) -> (VernacUndo 1 : 'command));
      [Gramext.Stoken ("IDENT", "Restart")],
      Gramext.action (fun _ (loc : Ploc.t) -> (VernacRestart : 'command));
      [Gramext.Stoken ("IDENT", "Defined");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e))],
      Gramext.action
        (fun (id : 'identref) _ (loc : Ploc.t) ->
           (VernacEndProof (Proved (Transparent, Some id)) : 'command));
      [Gramext.Stoken ("IDENT", "Defined")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           (VernacEndProof (Proved (Transparent, None)) : 'command));
      [Gramext.Stoken ("IDENT", "Save");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e))],
      Gramext.action
        (fun (id : 'identref) _ (loc : Ploc.t) ->
           (VernacEndProof (Proved (Opaque, Some id)) : 'command));
      [Gramext.Stoken ("IDENT", "Qed")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           (VernacEndProof (Proved (Opaque, None)) : 'command));
      [Gramext.Stoken ("IDENT", "Admitted")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (VernacEndProof Admitted : 'command));
      [Gramext.Stoken ("IDENT", "Existential");
       Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (constr_body : 'constr_body Gram.Entry.e))],
      Gramext.action
        (fun (c : 'constr_body) (n : 'natural) _ (loc : Ploc.t) ->
           (VernacSolveExistential (n, c) : 'command));
      [Gramext.Stoken ("IDENT", "Abort");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e))],
      Gramext.action
        (fun (id : 'identref) _ (loc : Ploc.t) ->
           (VernacAbort (Some id) : 'command));
      [Gramext.Stoken ("IDENT", "Abort"); Gramext.Stoken ("IDENT", "All")],
      Gramext.action (fun _ _ (loc : Ploc.t) -> (VernacAbortAll : 'command));
      [Gramext.Stoken ("IDENT", "Abort")],
      Gramext.action (fun _ (loc : Ploc.t) -> (VernacAbort None : 'command));
      [Gramext.Stoken ("IDENT", "Proof");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'lconstr) _ (loc : Ploc.t) ->
           (VernacExactProof c : 'command));
      [Gramext.Stoken ("IDENT", "Proof"); Gramext.Stoken ("IDENT", "Mode");
       Gramext.Snterm (Gram.Entry.obj (string : 'string Gram.Entry.e))],
      Gramext.action
        (fun (mn : 'string) _ _ (loc : Ploc.t) ->
           (VernacProofMode mn : 'command));
      [Gramext.Stoken ("IDENT", "Proof")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (VernacProof (None, None) : 'command));
      [Gramext.Stoken ("IDENT", "Goal");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'lconstr) _ (loc : Ploc.t) ->
           (VernacDefinition
              (Decl_kinds.(NoDischarge, Definition),
               (CAst.make ~loc:((!@) loc) Names.Anonymous, None),
               ProveBody ([], c)) :
            'command))]];
  Gram.extend (reference_or_constr : 'reference_or_constr Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'constr) (loc : Ploc.t) ->
           (HintsConstr c : 'reference_or_constr));
      [Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e))],
      Gramext.action
        (fun (r : 'global) (loc : Ploc.t) ->
           (HintsReference r : 'reference_or_constr))]];
  Gram.extend (hint : 'hint Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "Constructors");
       Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e)))],
      Gramext.action
        (fun (lc : 'global list) _ (loc : Ploc.t) ->
           (HintsConstructors lc : 'hint));
      [Gramext.Stoken ("IDENT", "Unfold");
       Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e)))],
      Gramext.action
        (fun (lqid : 'global list) _ (loc : Ploc.t) ->
           (HintsUnfold lqid : 'hint));
      [Gramext.Stoken ("IDENT", "Mode");
       Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (mode : 'mode Gram.Entry.e))],
      Gramext.action
        (fun (m : 'mode) (l : 'global) _ (loc : Ploc.t) ->
           (HintsMode (l, m) : 'hint));
      [Gramext.Stoken ("IDENT", "Opaque");
       Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e)))],
      Gramext.action
        (fun (lc : 'global list) _ (loc : Ploc.t) ->
           (HintsTransparency (lc, false) : 'hint));
      [Gramext.Stoken ("IDENT", "Transparent");
       Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e)))],
      Gramext.action
        (fun (lc : 'global list) _ (loc : Ploc.t) ->
           (HintsTransparency (lc, true) : 'hint));
      [Gramext.Stoken ("IDENT", "Immediate");
       Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj
               (reference_or_constr : 'reference_or_constr Gram.Entry.e)))],
      Gramext.action
        (fun (lc : 'reference_or_constr list) _ (loc : Ploc.t) ->
           (HintsImmediate lc : 'hint));
      [Gramext.Stoken ("IDENT", "Resolve");
       Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj
               (reference_or_constr : 'reference_or_constr Gram.Entry.e)));
       Gramext.Snterm (Gram.Entry.obj (hint_info : 'hint_info Gram.Entry.e))],
      Gramext.action
        (fun (info : 'hint_info) (lc : 'reference_or_constr list) _
             (loc : Ploc.t) ->
           (HintsResolve (List.map (fun x -> info, true, x) lc) : 'hint))]];
  Gram.extend (constr_body : 'constr_body Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", ":");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'lconstr) _ (t : 'lconstr) _ (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CCast (c, CastConv t)) :
            'constr_body));
      [Gramext.Stoken ("", ":=");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'lconstr) _ (loc : Ploc.t) -> (c : 'constr_body))]];
  Gram.extend (mode : 'mode Gram.Entry.e) None
    [None, None,
     [[Gramext.Slist1
         (Gramext.srules
            [[Gramext.Stoken ("", "-")],
             Gramext.action (fun _ (loc : Ploc.t) -> (ModeOutput : 'e__3));
             [Gramext.Stoken ("", "!")],
             Gramext.action
               (fun _ (loc : Ploc.t) -> (ModeNoHeadEvar : 'e__3));
             [Gramext.Stoken ("", "+")],
             Gramext.action (fun _ (loc : Ploc.t) -> (ModeInput : 'e__3))])],
      Gramext.action (fun (l : 'e__3 list) (loc : Ploc.t) -> (l : 'mode))]]
