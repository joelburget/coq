(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let __coq_plugin_name =
  (************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

  "ltac_plugin"

open Util
open Pp
open Constrexpr
open Tacexpr
open Misctypes
open Genarg
open Genredexpr
open Tok (* necessary for camlp5 *)
open Names

open Pcoq
open Pcoq.Constr
open Pcoq.Vernac_
open Pcoq.Prim
open Pltac

let fail_default_value = ArgArg 0

let arg_of_expr =
  function
    TacArg (loc, a) -> a
  | e -> Tacexp (e : raw_tactic_expr)

let genarg_of_unit () = in_gen (rawwit Stdarg.wit_unit) ()
let genarg_of_int n = in_gen (rawwit Stdarg.wit_int) n
let genarg_of_ipattern pat = in_gen (rawwit Stdarg.wit_intro_pattern) pat
let genarg_of_uconstr c = in_gen (rawwit Stdarg.wit_uconstr) c
let in_tac tac = in_gen (rawwit Tacarg.wit_ltac) tac

let reference_to_id =
  CAst.map_with_loc
    (fun ?loc ->
       function
         Libnames.Ident id -> id
       | Libnames.Qualid _ ->
           CErrors.user_err ?loc
             (str "This expression should be a simple identifier."))

let tactic_mode = Gram.entry_create "vernac:tactic_command"

let new_entry name = let e = Gram.entry_create name in e

let toplevel_selector = new_entry "vernac:toplevel_selector"
let tacdef_body = new_entry "tactic:tacdef_body"

(* Registers the Classic Proof Mode (which uses [tactic_mode] as a parser for
    proof editing and changes nothing else). Then sets it as the default proof mode. *)
let _ =
  let mode =
    {Proof_global.name = "Classic";
     set = (fun () -> set_command_entry tactic_mode);
     reset = fun () -> set_command_entry Pcoq.Vernac_.noedit_mode}
  in
  Proof_global.register_proof_mode mode

(* Hack to parse "[ id" without dropping [ *)
let test_bracket_ident =
  Gram.Entry.of_parser "test_bracket_ident"
    (fun strm ->
       match stream_nth 0 strm with
         KEYWORD "[" ->
           begin match stream_nth 1 strm with
             IDENT _ -> ()
           | _ -> raise Stream.Failure
           end
       | _ -> raise Stream.Failure)

(* Tactics grammar rules *)

let hint = G_proofs.hint

let _ =
  let _ = (tactic : 'tactic Gram.Entry.e)
  and _ = (tacdef_body : 'tacdef_body Gram.Entry.e)
  and _ = (tactic_expr : 'tactic_expr Gram.Entry.e)
  and _ = (binder_tactic : 'binder_tactic Gram.Entry.e)
  and _ = (tactic_arg : 'tactic_arg Gram.Entry.e)
  and _ = (command : 'command Gram.Entry.e)
  and _ = (hint : 'hint Gram.Entry.e)
  and _ = (tactic_mode : 'tactic_mode Gram.Entry.e)
  and _ = (constr_may_eval : 'constr_may_eval Gram.Entry.e)
  and _ = (constr_eval : 'constr_eval Gram.Entry.e)
  and _ = (toplevel_selector : 'toplevel_selector Gram.Entry.e)
  and _ = (operconstr : 'operconstr Gram.Entry.e) in
  let grammar_entry_create = Gram.Entry.create in
  let tactic_then_last : 'tactic_then_last Gram.Entry.e =
    grammar_entry_create "tactic_then_last"
  and tactic_then_gen : 'tactic_then_gen Gram.Entry.e =
    grammar_entry_create "tactic_then_gen"
  and tactic_then_locality : 'tactic_then_locality Gram.Entry.e =
    grammar_entry_create "tactic_then_locality"
  and failkw : 'failkw Gram.Entry.e = grammar_entry_create "failkw"
  and tactic_arg_compat : 'tactic_arg_compat Gram.Entry.e =
    (* Tactic arguments to the right of an application *)
    grammar_entry_create "tactic_arg_compat"
  and fresh_id : 'fresh_id Gram.Entry.e =
    (* If a qualid is given, use its short name. TODO: have the shortest
       non ambiguous name where dots are replaced by "_"? Probably too
       verbose most of the time. *)
    grammar_entry_create "fresh_id"
  and tactic_atom : 'tactic_atom Gram.Entry.e =
    grammar_entry_create "tactic_atom"
  and match_key : 'match_key Gram.Entry.e = grammar_entry_create "match_key"
  and input_fun : 'input_fun Gram.Entry.e = grammar_entry_create "input_fun"
  and let_clause : 'let_clause Gram.Entry.e =
    grammar_entry_create "let_clause"
  and match_pattern : 'match_pattern Gram.Entry.e =
    grammar_entry_create "match_pattern"
  and match_hyps : 'match_hyps Gram.Entry.e =
    grammar_entry_create "match_hyps"
  and match_context_rule : 'match_context_rule Gram.Entry.e =
    grammar_entry_create "match_context_rule"
  and match_context_list : 'match_context_list Gram.Entry.e =
    grammar_entry_create "match_context_list"
  and match_rule : 'match_rule Gram.Entry.e =
    grammar_entry_create "match_rule"
  and match_list : 'match_list Gram.Entry.e =
    grammar_entry_create "match_list"
  and message_token : 'message_token Gram.Entry.e =
    grammar_entry_create "message_token"
  and ltac_def_kind : 'ltac_def_kind Gram.Entry.e =
    grammar_entry_create "ltac_def_kind"
  and range_selector : 'range_selector Gram.Entry.e =
    grammar_entry_create "range_selector"
  and range_selector_or_nth : 'range_selector_or_nth Gram.Entry.e =
    (* We unfold a range selectors list once so that we can make a special case
     * for a unique SelectNth selector. *)
    grammar_entry_create "range_selector_or_nth"
  and selector_body : 'selector_body Gram.Entry.e =
    grammar_entry_create "selector_body"
  and selector : 'selector Gram.Entry.e = grammar_entry_create "selector" in
  Gram.extend (tactic_then_last : 'tactic_then_last Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> ([| |] : 'tactic_then_last));
      [Gramext.Stoken ("", "|");
       Gramext.Slist0sep
         (Gramext.Sopt
            (Gramext.Snterm
               (Gram.Entry.obj (tactic_expr : 'tactic_expr Gram.Entry.e))),
          Gramext.Stoken ("", "|"), false)],
      Gramext.action
        (fun (lta : 'tactic_expr option list) _ (loc : Ploc.t) ->
           (Array.map
              (function
                 None -> TacId []
               | Some t -> t)
              (Array.of_list lta) :
            'tactic_then_last))]];
  Gram.extend (tactic_then_gen : 'tactic_then_gen Gram.Entry.e) None
    [None, None,
     [[],
      Gramext.action
        (fun (loc : Ploc.t) -> ([TacId []], None : 'tactic_then_gen));
      [Gramext.Stoken ("", "|"); Gramext.Sself],
      Gramext.action
        (fun (first, last : 'tactic_then_gen) _ (loc : Ploc.t) ->
           (TacId [] :: first, last : 'tactic_then_gen));
      [Gramext.Snterm
         (Gram.Entry.obj (tactic_expr : 'tactic_expr Gram.Entry.e))],
      Gramext.action
        (fun (ta : 'tactic_expr) (loc : Ploc.t) ->
           ([ta], None : 'tactic_then_gen));
      [Gramext.Stoken ("", "..");
       Gramext.Snterm
         (Gram.Entry.obj
            (tactic_then_last : 'tactic_then_last Gram.Entry.e))],
      Gramext.action
        (fun (l : 'tactic_then_last) _ (loc : Ploc.t) ->
           ([], Some (TacId [], l) : 'tactic_then_gen));
      [Gramext.Snterm
         (Gram.Entry.obj (tactic_expr : 'tactic_expr Gram.Entry.e));
       Gramext.Stoken ("", "..");
       Gramext.Snterm
         (Gram.Entry.obj
            (tactic_then_last : 'tactic_then_last Gram.Entry.e))],
      Gramext.action
        (fun (l : 'tactic_then_last) _ (ta : 'tactic_expr) (loc : Ploc.t) ->
           ([], Some (ta, l) : 'tactic_then_gen));
      [Gramext.Snterm
         (Gram.Entry.obj (tactic_expr : 'tactic_expr Gram.Entry.e));
       Gramext.Stoken ("", "|"); Gramext.Sself],
      Gramext.action
        (fun (first, last : 'tactic_then_gen) _ (ta : 'tactic_expr)
             (loc : Ploc.t) ->
           (ta :: first, last : 'tactic_then_gen))]];
  Gram.extend (tactic_then_locality : 'tactic_then_locality Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "["); Gramext.Sopt (Gramext.Stoken ("", ">"))],
      Gramext.action
        (fun (l : string option) _ (loc : Ploc.t) ->
           (if Option.is_empty l then true else false :
            'tactic_then_locality))]];
  Gram.extend (tactic_expr : 'tactic_expr Gram.Entry.e) None
    [Some "5", Some Gramext.RightA,
     [[Gramext.Snterm
         (Gram.Entry.obj (binder_tactic : 'binder_tactic Gram.Entry.e))],
      Gramext.action
        (fun (te : 'binder_tactic) (loc : Ploc.t) -> (te : 'tactic_expr))];
     Some "4", Some Gramext.LeftA,
     [[Gramext.Sself; Gramext.Stoken ("", ";");
       Gramext.Snterm
         (Gram.Entry.obj
            (tactic_then_locality : 'tactic_then_locality Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (tactic_then_gen : 'tactic_then_gen Gram.Entry.e));
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (first, tail : 'tactic_then_gen) (l : 'tactic_then_locality) _
             (ta0 : 'tactic_expr) (loc : Ploc.t) ->
           (match l, tail with
              false, Some (t, last) ->
                TacThen (ta0, TacExtendTac (Array.of_list first, t, last))
            | true, Some (t, last) ->
                TacThens3parts (ta0, Array.of_list first, t, last)
            | false, None -> TacThen (ta0, TacDispatch first)
            | true, None -> TacThens (ta0, first) :
            'tactic_expr));
      [Gramext.Sself; Gramext.Stoken ("", ";"); Gramext.Sself],
      Gramext.action
        (fun (ta1 : 'tactic_expr) _ (ta0 : 'tactic_expr) (loc : Ploc.t) ->
           (TacThen (ta0, ta1) : 'tactic_expr));
      [Gramext.Sself; Gramext.Stoken ("", ";");
       Gramext.Snterm
         (Gram.Entry.obj (binder_tactic : 'binder_tactic Gram.Entry.e))],
      Gramext.action
        (fun (ta1 : 'binder_tactic) _ (ta0 : 'tactic_expr) (loc : Ploc.t) ->
           (TacThen (ta0, ta1) : 'tactic_expr))];
     Some "3", Some Gramext.RightA,
     [[Gramext.Snterm (Gram.Entry.obj (selector : 'selector Gram.Entry.e));
       Gramext.Sself],
      Gramext.action
        (fun (ta : 'tactic_expr) (sel : 'selector) (loc : Ploc.t) ->
           (TacSelect (sel, ta) : 'tactic_expr));
      [Gramext.Stoken ("IDENT", "abstract"); Gramext.Snext;
       Gramext.Stoken ("", "using");
       Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e))],
      Gramext.action
        (fun (s : 'ident) _ (tc : 'tactic_expr) _ (loc : Ploc.t) ->
           (TacAbstract (tc, Some s) : 'tactic_expr));
      [Gramext.Stoken ("IDENT", "abstract"); Gramext.Snext],
      Gramext.action
        (fun (tc : 'tactic_expr) _ (loc : Ploc.t) ->
           (TacAbstract (tc, None) : 'tactic_expr));
      [Gramext.Stoken ("IDENT", "infoH"); Gramext.Sself],
      Gramext.action
        (fun (ta : 'tactic_expr) _ (loc : Ploc.t) ->
           (TacShowHyps ta : 'tactic_expr));
      [Gramext.Stoken ("IDENT", "exactly_once"); Gramext.Sself],
      Gramext.action
        (fun (ta : 'tactic_expr) _ (loc : Ploc.t) ->
           (TacExactlyOnce ta : 'tactic_expr));
      [Gramext.Stoken ("IDENT", "once"); Gramext.Sself],
      Gramext.action
        (fun (ta : 'tactic_expr) _ (loc : Ploc.t) ->
           (TacOnce ta : 'tactic_expr));
      [Gramext.Stoken ("IDENT", "progress"); Gramext.Sself],
      Gramext.action
        (fun (ta : 'tactic_expr) _ (loc : Ploc.t) ->
           (TacProgress ta : 'tactic_expr));
      [Gramext.Stoken ("IDENT", "repeat"); Gramext.Sself],
      Gramext.action
        (fun (ta : 'tactic_expr) _ (loc : Ploc.t) ->
           (TacRepeat ta : 'tactic_expr));
      [Gramext.Stoken ("IDENT", "time");
       Gramext.Sopt
         (Gramext.Snterm (Gram.Entry.obj (string : 'string Gram.Entry.e)));
       Gramext.Sself],
      Gramext.action
        (fun (ta : 'tactic_expr) (s : 'string option) _ (loc : Ploc.t) ->
           (TacTime (s, ta) : 'tactic_expr));
      [Gramext.Stoken ("IDENT", "timeout");
       Gramext.Snterm
         (Gram.Entry.obj (int_or_var : 'int_or_var Gram.Entry.e));
       Gramext.Sself],
      Gramext.action
        (fun (ta : 'tactic_expr) (n : 'int_or_var) _ (loc : Ploc.t) ->
           (TacTimeout (n, ta) : 'tactic_expr));
      [Gramext.Stoken ("IDENT", "do");
       Gramext.Snterm
         (Gram.Entry.obj (int_or_var : 'int_or_var Gram.Entry.e));
       Gramext.Sself],
      Gramext.action
        (fun (ta : 'tactic_expr) (n : 'int_or_var) _ (loc : Ploc.t) ->
           (TacDo (n, ta) : 'tactic_expr));
      [Gramext.Stoken ("IDENT", "try"); Gramext.Sself],
      Gramext.action
        (fun (ta : 'tactic_expr) _ (loc : Ploc.t) ->
           (TacTry ta : 'tactic_expr))];
     Some "2", Some Gramext.RightA,
     [[Gramext.Sself; Gramext.Stoken ("", "||"); Gramext.Sself],
      Gramext.action
        (fun (ta1 : 'tactic_expr) _ (ta0 : 'tactic_expr) (loc : Ploc.t) ->
           (TacOrelse (ta0, ta1) : 'tactic_expr));
      [Gramext.Sself; Gramext.Stoken ("", "||");
       Gramext.Snterm
         (Gram.Entry.obj (binder_tactic : 'binder_tactic Gram.Entry.e))],
      Gramext.action
        (fun (ta1 : 'binder_tactic) _ (ta0 : 'tactic_expr) (loc : Ploc.t) ->
           (TacOrelse (ta0, ta1) : 'tactic_expr));
      [Gramext.Stoken ("IDENT", "tryif"); Gramext.Sself;
       Gramext.Stoken ("", "then"); Gramext.Sself;
       Gramext.Stoken ("", "else"); Gramext.Sself],
      Gramext.action
        (fun (tae : 'tactic_expr) _ (tat : 'tactic_expr) _ (ta : 'tactic_expr)
             _ (loc : Ploc.t) ->
           (TacIfThenCatch (ta, tat, tae) : 'tactic_expr));
      [Gramext.Sself; Gramext.Stoken ("", "+"); Gramext.Sself],
      Gramext.action
        (fun (ta1 : 'tactic_expr) _ (ta0 : 'tactic_expr) (loc : Ploc.t) ->
           (TacOr (ta0, ta1) : 'tactic_expr));
      [Gramext.Sself; Gramext.Stoken ("", "+");
       Gramext.Snterm
         (Gram.Entry.obj (binder_tactic : 'binder_tactic Gram.Entry.e))],
      Gramext.action
        (fun (ta1 : 'binder_tactic) _ (ta0 : 'tactic_expr) (loc : Ploc.t) ->
           (TacOr (ta0, ta1) : 'tactic_expr))];
     Some "1", Some Gramext.RightA,
     [[Gramext.Snterm (Gram.Entry.obj (reference : 'reference Gram.Entry.e));
       Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj
               (tactic_arg_compat : 'tactic_arg_compat Gram.Entry.e)))],
      Gramext.action
        (fun (la : 'tactic_arg_compat list) (r : 'reference) (loc : Ploc.t) ->
           (TacArg
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacCall (Loc.tag ~loc:((!@) loc) (r, la)))) :
            'tactic_expr));
      [Gramext.Snterm
         (Gram.Entry.obj (tactic_arg : 'tactic_arg Gram.Entry.e))],
      Gramext.action
        (fun (a : 'tactic_arg) (loc : Ploc.t) ->
           (TacArg (Loc.tag ~loc:((!@) loc) a) : 'tactic_expr));
      [Gramext.Snterm
         (Gram.Entry.obj (simple_tactic : 'simple_tactic Gram.Entry.e))],
      Gramext.action
        (fun (st : 'simple_tactic) (loc : Ploc.t) -> (st : 'tactic_expr));
      [Gramext.Snterm (Gram.Entry.obj (failkw : 'failkw Gram.Entry.e));
       Gramext.srules
         [[],
          Gramext.action (fun (loc : Ploc.t) -> (fail_default_value : 'e__1));
          [Gramext.Snterm
             (Gram.Entry.obj (int_or_var : 'int_or_var Gram.Entry.e))],
          Gramext.action
            (fun (n : 'int_or_var) (loc : Ploc.t) -> (n : 'e__1))];
       Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj (message_token : 'message_token Gram.Entry.e)))],
      Gramext.action
        (fun (l : 'message_token list) (n : 'e__1) (g : 'failkw)
             (loc : Ploc.t) ->
           (TacFail (g, n, l) : 'tactic_expr));
      [Gramext.Stoken ("IDENT", "idtac");
       Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj (message_token : 'message_token Gram.Entry.e)))],
      Gramext.action
        (fun (l : 'message_token list) _ (loc : Ploc.t) ->
           (TacId l : 'tactic_expr));
      [Gramext.Stoken ("IDENT", "solve"); Gramext.Stoken ("", "[");
       Gramext.Slist0sep
         (Gramext.Snterm
            (Gram.Entry.obj (tactic_expr : 'tactic_expr Gram.Entry.e)),
          Gramext.Stoken ("", "|"), false);
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (l : 'tactic_expr list) _ _ (loc : Ploc.t) ->
           (TacSolve l : 'tactic_expr));
      [Gramext.Stoken ("IDENT", "first"); Gramext.Stoken ("", "[");
       Gramext.Slist0sep
         (Gramext.Snterm
            (Gram.Entry.obj (tactic_expr : 'tactic_expr Gram.Entry.e)),
          Gramext.Stoken ("", "|"), false);
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (l : 'tactic_expr list) _ _ (loc : Ploc.t) ->
           (TacFirst l : 'tactic_expr));
      [Gramext.Snterm (Gram.Entry.obj (match_key : 'match_key Gram.Entry.e));
       Gramext.Sself; Gramext.Stoken ("", "with");
       Gramext.Snterm
         (Gram.Entry.obj (match_list : 'match_list Gram.Entry.e));
       Gramext.Stoken ("", "end")],
      Gramext.action
        (fun _ (mrl : 'match_list) _ (c : 'tactic_expr) (b : 'match_key)
             (loc : Ploc.t) ->
           (TacMatch (b, c, mrl) : 'tactic_expr));
      [Gramext.Snterm (Gram.Entry.obj (match_key : 'match_key Gram.Entry.e));
       Gramext.Stoken ("IDENT", "reverse"); Gramext.Stoken ("IDENT", "goal");
       Gramext.Stoken ("", "with");
       Gramext.Snterm
         (Gram.Entry.obj
            (match_context_list : 'match_context_list Gram.Entry.e));
       Gramext.Stoken ("", "end")],
      Gramext.action
        (fun _ (mrl : 'match_context_list) _ _ _ (b : 'match_key)
             (loc : Ploc.t) ->
           (TacMatchGoal (b, true, mrl) : 'tactic_expr));
      [Gramext.Snterm (Gram.Entry.obj (match_key : 'match_key Gram.Entry.e));
       Gramext.Stoken ("IDENT", "goal"); Gramext.Stoken ("", "with");
       Gramext.Snterm
         (Gram.Entry.obj
            (match_context_list : 'match_context_list Gram.Entry.e));
       Gramext.Stoken ("", "end")],
      Gramext.action
        (fun _ (mrl : 'match_context_list) _ _ (b : 'match_key)
             (loc : Ploc.t) ->
           (TacMatchGoal (b, false, mrl) : 'tactic_expr))];
     Some "0", None,
     [[Gramext.Snterm
         (Gram.Entry.obj (tactic_atom : 'tactic_atom Gram.Entry.e))],
      Gramext.action
        (fun (a : 'tactic_atom) (loc : Ploc.t) ->
           (TacArg (Loc.tag ~loc:((!@) loc) a) : 'tactic_expr));
      [Gramext.Stoken ("", "["); Gramext.Stoken ("", ">");
       Gramext.Snterm
         (Gram.Entry.obj (tactic_then_gen : 'tactic_then_gen Gram.Entry.e));
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (tf, tail : 'tactic_then_gen) _ _ (loc : Ploc.t) ->
           (match tail with
              Some (t, tl) -> TacExtendTac (Array.of_list tf, t, tl)
            | None -> TacDispatch tf :
            'tactic_expr));
      [Gramext.Stoken ("", "("); Gramext.Sself; Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (a : 'tactic_expr) _ (loc : Ploc.t) -> (a : 'tactic_expr))]];
  Gram.extend (failkw : 'failkw Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "gfail")],
      Gramext.action (fun _ (loc : Ploc.t) -> (TacGlobal : 'failkw));
      [Gramext.Stoken ("IDENT", "fail")],
      Gramext.action (fun _ (loc : Ploc.t) -> (TacLocal : 'failkw))]];
  Gram.extend (binder_tactic : 'binder_tactic Gram.Entry.e) None
    [None, Some Gramext.RightA,
     [[Gramext.Stoken ("IDENT", "info");
       Gramext.Snterml
         (Gram.Entry.obj (tactic_expr : 'tactic_expr Gram.Entry.e), "5")],
      Gramext.action
        (fun (tc : 'tactic_expr) _ (loc : Ploc.t) ->
           (TacInfo tc : 'binder_tactic));
      [Gramext.Stoken ("", "let");
       Gramext.srules
         [[], Gramext.action (fun (loc : Ploc.t) -> (false : 'e__2));
          [Gramext.Stoken ("IDENT", "rec")],
          Gramext.action (fun _ (loc : Ploc.t) -> (true : 'e__2))];
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj (let_clause : 'let_clause Gram.Entry.e)),
          Gramext.Stoken ("", "with"), false);
       Gramext.Stoken ("", "in");
       Gramext.Snterml
         (Gram.Entry.obj (tactic_expr : 'tactic_expr Gram.Entry.e), "5")],
      Gramext.action
        (fun (body : 'tactic_expr) _ (llc : 'let_clause list) (isrec : 'e__2)
             _ (loc : Ploc.t) ->
           (TacLetIn (isrec, llc, body) : 'binder_tactic));
      [Gramext.Stoken ("", "fun");
       Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (input_fun : 'input_fun Gram.Entry.e)));
       Gramext.Stoken ("", "=>");
       Gramext.Snterml
         (Gram.Entry.obj (tactic_expr : 'tactic_expr Gram.Entry.e), "5")],
      Gramext.action
        (fun (body : 'tactic_expr) _ (it : 'input_fun list) _
             (loc : Ploc.t) ->
           (TacFun (it, body) : 'binder_tactic))]];
  Gram.extend (tactic_arg_compat : 'tactic_arg_compat Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "()")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           (TacGeneric (genarg_of_unit ()) : 'tactic_arg_compat));
      [Gramext.Snterm
         (Gram.Entry.obj (Constr.constr : 'Constr__constr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'Constr__constr) (loc : Ploc.t) ->
           (match c with
              {CAst.v = CRef (r, None)} -> Reference r
            | c -> ConstrMayEval (ConstrTerm c) :
            'tactic_arg_compat));
      [Gramext.Snterm
         (Gram.Entry.obj (tactic_arg : 'tactic_arg Gram.Entry.e))],
      Gramext.action
        (fun (a : 'tactic_arg) (loc : Ploc.t) -> (a : 'tactic_arg_compat))]];
  Gram.extend (tactic_arg : 'tactic_arg Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "numgoals")],
      Gramext.action (fun _ (loc : Ploc.t) -> (TacNumgoals : 'tactic_arg));
      [Gramext.Stoken ("IDENT", "type_term");
       Gramext.Snterm (Gram.Entry.obj (uconstr : 'uconstr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'uconstr) _ (loc : Ploc.t) -> (TacPretype c : 'tactic_arg));
      [Gramext.Stoken ("IDENT", "fresh");
       Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj (fresh_id : 'fresh_id Gram.Entry.e)))],
      Gramext.action
        (fun (l : 'fresh_id list) _ (loc : Ploc.t) ->
           (TacFreshId l : 'tactic_arg));
      [Gramext.Snterm
         (Gram.Entry.obj (constr_eval : 'constr_eval Gram.Entry.e))],
      Gramext.action
        (fun (c : 'constr_eval) (loc : Ploc.t) ->
           (ConstrMayEval c : 'tactic_arg))]];
  Gram.extend (fresh_id : 'fresh_id Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (qualid : 'qualid Gram.Entry.e))],
      Gramext.action
        (fun (qid : 'qualid) (loc : Ploc.t) ->
           (let (_pth, id) = Libnames.repr_qualid qid.CAst.v in
            ArgVar (CAst.make ~loc:((!@) loc) id) :
            'fresh_id));
      [Gramext.Stoken ("STRING", "")],
      Gramext.action
        (fun (s : string) (loc : Ploc.t) -> (ArgArg s : 'fresh_id))]];
  Gram.extend (constr_eval : 'constr_eval Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "type"); Gramext.Stoken ("IDENT", "of");
       Gramext.Snterm
         (Gram.Entry.obj (Constr.constr : 'Constr__constr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'Constr__constr) _ _ (loc : Ploc.t) ->
           (ConstrTypeOf c : 'constr_eval));
      [Gramext.Stoken ("IDENT", "context");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Stoken ("", "[");
       Gramext.Snterm
         (Gram.Entry.obj (Constr.lconstr : 'Constr__lconstr Gram.Entry.e));
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (c : 'Constr__lconstr) _ (id : 'identref) _ (loc : Ploc.t) ->
           (ConstrContext (id, c) : 'constr_eval));
      [Gramext.Stoken ("IDENT", "eval");
       Gramext.Snterm (Gram.Entry.obj (red_expr : 'red_expr Gram.Entry.e));
       Gramext.Stoken ("", "in");
       Gramext.Snterm
         (Gram.Entry.obj (Constr.constr : 'Constr__constr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'Constr__constr) _ (rtc : 'red_expr) _ (loc : Ploc.t) ->
           (ConstrEval (rtc, c) : 'constr_eval))]];
  Gram.extend (constr_may_eval : 'constr_may_eval Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (Constr.constr : 'Constr__constr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'Constr__constr) (loc : Ploc.t) ->
           (ConstrTerm c : 'constr_may_eval));
      [Gramext.Snterm
         (Gram.Entry.obj (constr_eval : 'constr_eval Gram.Entry.e))],
      Gramext.action
        (fun (c : 'constr_eval) (loc : Ploc.t) -> (c : 'constr_may_eval))]];
  Gram.extend (tactic_atom : 'tactic_atom Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "()")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           (TacGeneric (genarg_of_unit ()) : 'tactic_atom));
      [Gramext.Snterm (Gram.Entry.obj (reference : 'reference Gram.Entry.e))],
      Gramext.action
        (fun (r : 'reference) (loc : Ploc.t) ->
           (TacCall (Loc.tag ~loc:((!@) loc) (r, [])) : 'tactic_atom));
      [Gramext.Snterm (Gram.Entry.obj (integer : 'integer Gram.Entry.e))],
      Gramext.action
        (fun (n : 'integer) (loc : Ploc.t) ->
           (TacGeneric (genarg_of_int n) : 'tactic_atom))]];
  Gram.extend (match_key : 'match_key Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "multimatch")],
      Gramext.action (fun _ (loc : Ploc.t) -> (General : 'match_key));
      [Gramext.Stoken ("", "lazymatch")],
      Gramext.action (fun _ (loc : Ploc.t) -> (Select : 'match_key));
      [Gramext.Stoken ("", "match")],
      Gramext.action (fun _ (loc : Ploc.t) -> (Once : 'match_key))]];
  Gram.extend (input_fun : 'input_fun Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e))],
      Gramext.action
        (fun (l : 'ident) (loc : Ploc.t) -> (Name.Name l : 'input_fun));
      [Gramext.Stoken ("", "_")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (Name.Anonymous : 'input_fun))]];
  Gram.extend (let_clause : 'let_clause Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (input_fun : 'input_fun Gram.Entry.e)));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm
         (Gram.Entry.obj (tactic_expr : 'tactic_expr Gram.Entry.e))],
      Gramext.action
        (fun (te : 'tactic_expr) _ (args : 'input_fun list) (idr : 'identref)
             (loc : Ploc.t) ->
           (CAst.map (fun id -> Name id) idr,
            arg_of_expr (TacFun (args, te)) :
            'let_clause));
      [Gramext.srules
         [[Gramext.Stoken ("", "_")],
          Gramext.action
            (fun _ (loc : Ploc.t) ->
               (CAst.make ~loc:((!@) loc) Anonymous : 'e__3))];
       Gramext.Stoken ("", ":=");
       Gramext.Snterm
         (Gram.Entry.obj (tactic_expr : 'tactic_expr Gram.Entry.e))],
      Gramext.action
        (fun (te : 'tactic_expr) _ (na : 'e__3) (loc : Ploc.t) ->
           (na, arg_of_expr te : 'let_clause));
      [Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm
         (Gram.Entry.obj (tactic_expr : 'tactic_expr Gram.Entry.e))],
      Gramext.action
        (fun (te : 'tactic_expr) _ (idr : 'identref) (loc : Ploc.t) ->
           (CAst.map (fun id -> Name id) idr, arg_of_expr te :
            'let_clause))]];
  Gram.extend (match_pattern : 'match_pattern Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj
            (Constr.lconstr_pattern :
             'Constr__lconstr_pattern Gram.Entry.e))],
      Gramext.action
        (fun (pc : 'Constr__lconstr_pattern) (loc : Ploc.t) ->
           (Term pc : 'match_pattern));
      [Gramext.Stoken ("IDENT", "context");
       Gramext.Sopt
         (Gramext.Snterm
            (Gram.Entry.obj (Constr.ident : 'Constr__ident Gram.Entry.e)));
       Gramext.Stoken ("", "[");
       Gramext.Snterm
         (Gram.Entry.obj
            (Constr.lconstr_pattern : 'Constr__lconstr_pattern Gram.Entry.e));
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (pc : 'Constr__lconstr_pattern) _ (oid : 'Constr__ident option)
             _ (loc : Ploc.t) ->
           (Subterm (oid, pc) : 'match_pattern))]];
  Gram.extend (match_hyps : 'match_hyps Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm
         (Gram.Entry.obj (match_pattern : 'match_pattern Gram.Entry.e))],
      Gramext.action
        (fun (mpv : 'match_pattern) _ (na : 'name) (loc : Ploc.t) ->
           (let (t, ty) =
              match mpv with
                Term t ->
                  begin match t with
                    {CAst.v =
                       CCast
                         (t, (CastConv ty (* | CastVM ty | CastNative ty *)))} ->
                      Term t, Some (Term ty)
                  | _ -> mpv, None
                  end
              | _ -> mpv, None
            in
            Def
              (na, t,
               Option.default
                 (Term ((@@) CAst.make (CHole (None, IntroAnonymous, None))))
                 ty) :
            'match_hyps));
      [Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e));
       Gramext.Stoken ("", ":="); Gramext.Stoken ("", "[");
       Gramext.Snterm
         (Gram.Entry.obj (match_pattern : 'match_pattern Gram.Entry.e));
       Gramext.Stoken ("", "]"); Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Gram.Entry.obj (match_pattern : 'match_pattern Gram.Entry.e))],
      Gramext.action
        (fun (mpt : 'match_pattern) _ _ (mpv : 'match_pattern) _ _
             (na : 'name) (loc : Ploc.t) ->
           (Def (na, mpv, mpt) : 'match_hyps));
      [Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Gram.Entry.obj (match_pattern : 'match_pattern Gram.Entry.e))],
      Gramext.action
        (fun (mp : 'match_pattern) _ (na : 'name) (loc : Ploc.t) ->
           (Hyp (na, mp) : 'match_hyps))]];
  Gram.extend (match_context_rule : 'match_context_rule Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "_"); Gramext.Stoken ("", "=>");
       Gramext.Snterm
         (Gram.Entry.obj (tactic_expr : 'tactic_expr Gram.Entry.e))],
      Gramext.action
        (fun (te : 'tactic_expr) _ _ (loc : Ploc.t) ->
           (All te : 'match_context_rule));
      [Gramext.Stoken ("", "[");
       Gramext.Slist0sep
         (Gramext.Snterm
            (Gram.Entry.obj (match_hyps : 'match_hyps Gram.Entry.e)),
          Gramext.Stoken ("", ","), false);
       Gramext.Stoken ("", "|-");
       Gramext.Snterm
         (Gram.Entry.obj (match_pattern : 'match_pattern Gram.Entry.e));
       Gramext.Stoken ("", "]"); Gramext.Stoken ("", "=>");
       Gramext.Snterm
         (Gram.Entry.obj (tactic_expr : 'tactic_expr Gram.Entry.e))],
      Gramext.action
        (fun (te : 'tactic_expr) _ _ (mp : 'match_pattern) _
             (largs : 'match_hyps list) _ (loc : Ploc.t) ->
           (Pat (largs, mp, te) : 'match_context_rule));
      [Gramext.Slist0sep
         (Gramext.Snterm
            (Gram.Entry.obj (match_hyps : 'match_hyps Gram.Entry.e)),
          Gramext.Stoken ("", ","), false);
       Gramext.Stoken ("", "|-");
       Gramext.Snterm
         (Gram.Entry.obj (match_pattern : 'match_pattern Gram.Entry.e));
       Gramext.Stoken ("", "=>");
       Gramext.Snterm
         (Gram.Entry.obj (tactic_expr : 'tactic_expr Gram.Entry.e))],
      Gramext.action
        (fun (te : 'tactic_expr) _ (mp : 'match_pattern) _
             (largs : 'match_hyps list) (loc : Ploc.t) ->
           (Pat (largs, mp, te) : 'match_context_rule))]];
  Gram.extend (match_context_list : 'match_context_list Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "|");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj
               (match_context_rule : 'match_context_rule Gram.Entry.e)),
          Gramext.Stoken ("", "|"), false)],
      Gramext.action
        (fun (mrl : 'match_context_rule list) _ (loc : Ploc.t) ->
           (mrl : 'match_context_list));
      [Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj
               (match_context_rule : 'match_context_rule Gram.Entry.e)),
          Gramext.Stoken ("", "|"), false)],
      Gramext.action
        (fun (mrl : 'match_context_rule list) (loc : Ploc.t) ->
           (mrl : 'match_context_list))]];
  Gram.extend (match_rule : 'match_rule Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "_"); Gramext.Stoken ("", "=>");
       Gramext.Snterm
         (Gram.Entry.obj (tactic_expr : 'tactic_expr Gram.Entry.e))],
      Gramext.action
        (fun (te : 'tactic_expr) _ _ (loc : Ploc.t) ->
           (All te : 'match_rule));
      [Gramext.Snterm
         (Gram.Entry.obj (match_pattern : 'match_pattern Gram.Entry.e));
       Gramext.Stoken ("", "=>");
       Gramext.Snterm
         (Gram.Entry.obj (tactic_expr : 'tactic_expr Gram.Entry.e))],
      Gramext.action
        (fun (te : 'tactic_expr) _ (mp : 'match_pattern) (loc : Ploc.t) ->
           (Pat ([], mp, te) : 'match_rule))]];
  Gram.extend (match_list : 'match_list Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "|");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj (match_rule : 'match_rule Gram.Entry.e)),
          Gramext.Stoken ("", "|"), false)],
      Gramext.action
        (fun (mrl : 'match_rule list) _ (loc : Ploc.t) ->
           (mrl : 'match_list));
      [Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj (match_rule : 'match_rule Gram.Entry.e)),
          Gramext.Stoken ("", "|"), false)],
      Gramext.action
        (fun (mrl : 'match_rule list) (loc : Ploc.t) ->
           (mrl : 'match_list))]];
  Gram.extend (message_token : 'message_token Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (integer : 'integer Gram.Entry.e))],
      Gramext.action
        (fun (n : 'integer) (loc : Ploc.t) -> (MsgInt n : 'message_token));
      [Gramext.Stoken ("STRING", "")],
      Gramext.action
        (fun (s : string) (loc : Ploc.t) -> (MsgString s : 'message_token));
      [Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e))],
      Gramext.action
        (fun (id : 'identref) (loc : Ploc.t) ->
           (MsgIdent id : 'message_token))]];
  Gram.extend (ltac_def_kind : 'ltac_def_kind Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "::=")],
      Gramext.action (fun _ (loc : Ploc.t) -> (true : 'ltac_def_kind));
      [Gramext.Stoken ("", ":=")],
      Gramext.action (fun _ (loc : Ploc.t) -> (false : 'ltac_def_kind))]];
  Gram.extend (tacdef_body : 'tacdef_body Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (Constr.global : 'Constr__global Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (ltac_def_kind : 'ltac_def_kind Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (tactic_expr : 'tactic_expr Gram.Entry.e))],
      Gramext.action
        (fun (body : 'tactic_expr) (redef : 'ltac_def_kind)
             (name : 'Constr__global) (loc : Ploc.t) ->
           (if redef then Tacexpr.TacticRedefinition (name, body)
            else
              let id = reference_to_id name in
              Tacexpr.TacticDefinition (id, body) :
            'tacdef_body));
      [Gramext.Snterm
         (Gram.Entry.obj (Constr.global : 'Constr__global Gram.Entry.e));
       Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (input_fun : 'input_fun Gram.Entry.e)));
       Gramext.Snterm
         (Gram.Entry.obj (ltac_def_kind : 'ltac_def_kind Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (tactic_expr : 'tactic_expr Gram.Entry.e))],
      Gramext.action
        (fun (body : 'tactic_expr) (redef : 'ltac_def_kind)
             (it : 'input_fun list) (name : 'Constr__global) (loc : Ploc.t) ->
           (if redef then Tacexpr.TacticRedefinition (name, TacFun (it, body))
            else
              let id = reference_to_id name in
              Tacexpr.TacticDefinition (id, TacFun (it, body)) :
            'tacdef_body))]];
  Gram.extend (tactic : 'tactic Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (tactic_expr : 'tactic_expr Gram.Entry.e))],
      Gramext.action
        (fun (tac : 'tactic_expr) (loc : Ploc.t) -> (tac : 'tactic))]];
  Gram.extend (range_selector : 'range_selector Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e))],
      Gramext.action
        (fun (n : 'natural) (loc : Ploc.t) -> (n, n : 'range_selector));
      [Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e));
       Gramext.Stoken ("", "-");
       Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e))],
      Gramext.action
        (fun (m : 'natural) _ (n : 'natural) (loc : Ploc.t) ->
           (n, m : 'range_selector))]];
  Gram.extend (range_selector_or_nth : 'range_selector_or_nth Gram.Entry.e)
    None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e));
       Gramext.Sopt
         (Gramext.srules
            [[Gramext.Stoken ("", ",");
              Gramext.Slist1sep
                (Gramext.Snterm
                   (Gram.Entry.obj
                      (range_selector : 'range_selector Gram.Entry.e)),
                 Gramext.Stoken ("", ","), false)],
             Gramext.action
               (fun (l : 'range_selector list) _ (loc : Ploc.t) ->
                  (l : 'e__5))])],
      Gramext.action
        (fun (l : 'e__5 option) (n : 'natural) (loc : Ploc.t) ->
           (Option.cata (fun l -> SelectList ((n, n) :: l)) (SelectNth n) l :
            'range_selector_or_nth));
      [Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e));
       Gramext.Stoken ("", "-");
       Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e));
       Gramext.Sopt
         (Gramext.srules
            [[Gramext.Stoken ("", ",");
              Gramext.Slist1sep
                (Gramext.Snterm
                   (Gram.Entry.obj
                      (range_selector : 'range_selector Gram.Entry.e)),
                 Gramext.Stoken ("", ","), false)],
             Gramext.action
               (fun (l : 'range_selector list) _ (loc : Ploc.t) ->
                  (l : 'e__4))])],
      Gramext.action
        (fun (l : 'e__4 option) (m : 'natural) _ (n : 'natural)
             (loc : Ploc.t) ->
           (SelectList ((n, m) :: Option.default [] l) :
            'range_selector_or_nth))]];
  Gram.extend (selector_body : 'selector_body Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj
            (test_bracket_ident : 'test_bracket_ident Gram.Entry.e));
       Gramext.Stoken ("", "[");
       Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e));
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (id : 'ident) _ _ (loc : Ploc.t) ->
           (SelectId id : 'selector_body));
      [Gramext.Snterm
         (Gram.Entry.obj
            (range_selector_or_nth : 'range_selector_or_nth Gram.Entry.e))],
      Gramext.action
        (fun (l : 'range_selector_or_nth) (loc : Ploc.t) ->
           (l : 'selector_body))]];
  Gram.extend (selector : 'selector Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "only");
       Gramext.Snterm
         (Gram.Entry.obj (selector_body : 'selector_body Gram.Entry.e));
       Gramext.Stoken ("", ":")],
      Gramext.action
        (fun _ (sel : 'selector_body) _ (loc : Ploc.t) ->
           (sel : 'selector))]];
  Gram.extend (toplevel_selector : 'toplevel_selector Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "all"); Gramext.Stoken ("", ":")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) -> (SelectAll : 'toplevel_selector));
      [Gramext.Snterm
         (Gram.Entry.obj (selector_body : 'selector_body Gram.Entry.e));
       Gramext.Stoken ("", ":")],
      Gramext.action
        (fun _ (sel : 'selector_body) (loc : Ploc.t) ->
           (sel : 'toplevel_selector))]];
  Gram.extend (tactic_mode : 'tactic_mode Gram.Entry.e) None
    [None, None,
     [[Gramext.Sopt
         (Gramext.Snterm
            (Gram.Entry.obj
               (toplevel_selector : 'toplevel_selector Gram.Entry.e)));
       Gramext.Stoken ("", "{")],
      Gramext.action
        (fun _ (g : 'toplevel_selector option) (loc : Ploc.t) ->
           (Vernacexpr.VernacSubproof g : 'tactic_mode));
      [Gramext.Sopt
         (Gramext.Snterm
            (Gram.Entry.obj
               (toplevel_selector : 'toplevel_selector Gram.Entry.e)));
       Gramext.Snterm
         (Gram.Entry.obj
            (G_vernac.query_command :
             'G_vernac__query_command Gram.Entry.e))],
      Gramext.action
        (fun (tac : 'G_vernac__query_command) (g : 'toplevel_selector option)
             (loc : Ploc.t) ->
           (tac g : 'tactic_mode))]];
  Gram.extend (command : 'command Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "Proof"); Gramext.Stoken ("", "using");
       Gramext.Snterm
         (Gram.Entry.obj
            (G_vernac.section_subset_expr :
             'G_vernac__section_subset_expr Gram.Entry.e));
       Gramext.Sopt
         (Gramext.srules
            [[Gramext.Stoken ("", "with");
              Gramext.Snterm
                (Gram.Entry.obj
                   (Pltac.tactic : 'Pltac__tactic Gram.Entry.e))],
             Gramext.action
               (fun (ta : 'Pltac__tactic) _ (loc : Ploc.t) ->
                  (in_tac ta : 'e__7))])],
      Gramext.action
        (fun (ta : 'e__7 option) (l : 'G_vernac__section_subset_expr) _ _
             (loc : Ploc.t) ->
           (Vernacexpr.VernacProof (ta, Some l) : 'command));
      [Gramext.Stoken ("IDENT", "Proof"); Gramext.Stoken ("", "with");
       Gramext.Snterm
         (Gram.Entry.obj (Pltac.tactic : 'Pltac__tactic Gram.Entry.e));
       Gramext.Sopt
         (Gramext.srules
            [[Gramext.Stoken ("", "using");
              Gramext.Snterm
                (Gram.Entry.obj
                   (G_vernac.section_subset_expr :
                    'G_vernac__section_subset_expr Gram.Entry.e))],
             Gramext.action
               (fun (l : 'G_vernac__section_subset_expr) _ (loc : Ploc.t) ->
                  (l : 'e__6))])],
      Gramext.action
        (fun (l : 'e__6 option) (ta : 'Pltac__tactic) _ _ (loc : Ploc.t) ->
           (Vernacexpr.VernacProof (Some (in_tac ta), l) : 'command))]];
  Gram.extend (hint : 'hint Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "Extern");
       Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e));
       Gramext.Sopt
         (Gramext.Snterm
            (Gram.Entry.obj
               (Constr.constr_pattern :
                'Constr__constr_pattern Gram.Entry.e)));
       Gramext.Stoken ("", "=>");
       Gramext.Snterm
         (Gram.Entry.obj (Pltac.tactic : 'Pltac__tactic Gram.Entry.e))],
      Gramext.action
        (fun (tac : 'Pltac__tactic) _ (c : 'Constr__constr_pattern option)
             (n : 'natural) _ (loc : Ploc.t) ->
           (Vernacexpr.HintsExtern (n, c, in_tac tac) : 'hint))]];
  Gram.extend (operconstr : 'operconstr Gram.Entry.e)
    (Some (Gramext.Level "0"))
    [None, None,
     [[Gramext.Stoken ("IDENT", "ltac"); Gramext.Stoken ("", ":");
       Gramext.Stoken ("", "(");
       Gramext.Snterm
         (Gram.Entry.obj
            (Pltac.tactic_expr : 'Pltac__tactic_expr Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (tac : 'Pltac__tactic_expr) _ _ _ (loc : Ploc.t) ->
           (let arg = Genarg.in_gen (Genarg.rawwit Tacarg.wit_tactic) tac in
            (@@) (CAst.make ~loc:((!@) loc))
              (CHole (None, IntroAnonymous, Some arg)) :
            'operconstr))]]

open Stdarg
open Tacarg
open Vernacexpr
open Vernac_classifier
open Goptions
open Libnames

let print_info_trace = ref None

let _ =
  declare_int_option
    {optdepr = false; optname = "print info trace";
     optkey = ["Info"; "Level"]; optread = (fun () -> !print_info_trace);
     optwrite = fun n -> print_info_trace := n}

let vernac_solve n info tcom b =
  let status =
    Proof_global.with_current_proof
      (fun etac p ->
         let with_end_tac = if b then Some etac else None in
         let global =
           match n with
             SelectAll | SelectList _ -> true
           | _ -> false
         in
         let info = Option.append info !print_info_trace in
         let (p, status) =
           Pfedit.solve n info (Tacinterp.hide_interp global tcom None)
             ?with_end_tac p
         in
         (* in case a strict subtree was completed,
            go back to the top of the prooftree *)
         let p = Proof.maximal_unfocus Vernacentries.command_focus p in
         p, status)
  in
  if not status then Feedback.feedback Feedback.AddedAxiom

let pr_ltac_selector s = Pptactic.pr_goal_selector ~toplevel:true s

let (wit_ltac_selector : ('a, unit, unit) Genarg.genarg_type) =
  Genarg.create_arg "ltac_selector"
let ltac_selector =
  let () = Pcoq.register_grammar wit_ltac_selector toplevel_selector in
  toplevel_selector
let _ =
  Pptactic.declare_extra_vernac_genarg_pprule wit_ltac_selector
    (fun _ _ _ -> pr_ltac_selector)

let pr_ltac_info n = (++) ((++) (str "Info") (spc ())) (int n)

let (wit_ltac_info : ('a, unit, unit) Genarg.genarg_type) =
  Genarg.create_arg "ltac_info"
let ltac_info =
  let ltac_info =
    Pcoq.create_generic_entry Pcoq.utactic "ltac_info"
      (Genarg.rawwit wit_ltac_info)
  in
  let () =
    Pcoq.grammar_extend ltac_info None
      (None,
       [None, None,
        [Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Stop, Extend.Atoken (CLexer.terminal "Info")),
               Extend.Aentry natural),
            (fun n _ loc -> n))]])
  in
  ltac_info
let _ =
  Pptactic.declare_extra_vernac_genarg_pprule wit_ltac_info
    (fun _ _ _ -> pr_ltac_info)

let pr_ltac_use_default b = if b then str ".." else mt ()

let (wit_ltac_use_default : ('a, unit, unit) Genarg.genarg_type) =
  Genarg.create_arg "ltac_use_default"
let ltac_use_default =
  let ltac_use_default =
    Pcoq.create_generic_entry Pcoq.utactic "ltac_use_default"
      (Genarg.rawwit wit_ltac_use_default)
  in
  let () =
    Pcoq.grammar_extend ltac_use_default None
      (None,
       [None, None,
        [Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Atoken (CLexer.terminal "...")),
            (fun _ loc -> true));
         Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Atoken (CLexer.terminal ".")),
            (fun _ loc -> false))]])
  in
  ltac_use_default
let _ =
  Pptactic.declare_extra_vernac_genarg_pprule wit_ltac_use_default
    (fun _ _ _ -> pr_ltac_use_default)

let is_anonymous_abstract =
  function
    TacAbstract (_, None) -> true
  | TacSolve [TacAbstract (_, None)] -> true
  | _ -> false
let rm_abstract =
  function
    TacAbstract (t, _) -> t
  | TacSolve [TacAbstract (t, _)] -> TacSolve [t]
  | x -> x
let is_explicit_terminator =
  function
    TacSolve _ -> true
  | _ -> false

let _ =
  CList.iteri
    (fun i (depr, f) -> Vernacinterp.vinterp_add depr ("VernacSolve", i) f)
    [false,
     (function
        [g; n; t; def] ->
          let g =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_opt wit_ltac_selector))
              g
          in
          let n =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_opt wit_ltac_info)) n
          in
          let t = Genarg.out_gen (Genarg.rawwit wit_tactic) t in
          let def = Genarg.out_gen (Genarg.rawwit wit_ltac_use_default) def in
          (fun ~atts ~st ->
             let () =
               let g =
                 Option.default (Proof_bullet.get_default_goal_selector ()) g
               in
               vernac_solve g n t def
             in
             st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [n; t; def] ->
          let n =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_opt wit_ltac_info)) n
          in
          let t = Genarg.out_gen (Genarg.rawwit wit_tactic) t in
          let def = Genarg.out_gen (Genarg.rawwit wit_ltac_use_default) def in
          (fun ~atts ~st ->
             let () =
               let t = rm_abstract t in vernac_solve SelectAll n t def
             in
             st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("VernacSolve", i) f)
    [(function
        [g; n; t; def] ->
          let g =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_opt wit_ltac_selector))
              g
          in
          let n =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_opt wit_ltac_info)) n
          in
          let t = Genarg.out_gen (Genarg.rawwit wit_tactic) t in
          let def = Genarg.out_gen (Genarg.rawwit wit_ltac_use_default) def in
          let _ = let _ = g in let _ = n in let _ = t in let _ = def in () in
          (fun loc -> classify_as_proofstep)
      | _ -> failwith "Extension: cannot occur");
     (function
        [n; t; def] ->
          let n =
            Genarg.out_gen (Genarg.rawwit (Genarg.wit_opt wit_ltac_info)) n
          in
          let t = Genarg.out_gen (Genarg.rawwit wit_tactic) t in
          let def = Genarg.out_gen (Genarg.rawwit wit_ltac_use_default) def in
          let _ = let _ = n in let _ = t in let _ = def in () in
          (fun loc ->
             let anon_abstracting_tac = is_anonymous_abstract t in
             let solving_tac = is_explicit_terminator t in
             let parallel = `Yes (solving_tac, anon_abstracting_tac) in
             let pbr = if solving_tac then Some "par" else None in
             VtProofStep {parallel = parallel; proof_block_detection = pbr},
             VtLater)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("VernacSolve", i)
         (Some tactic_mode) r)
    [[Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_opt wit_ltac_selector)),
            Extend.Aopt
              (Extend.Aentry (Pcoq.genarg_grammar wit_ltac_selector))));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_opt wit_ltac_info)),
            Extend.Aopt (Extend.Aentry (Pcoq.genarg_grammar wit_ltac_info))));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_tactic),
            Extend.Aentry (Pcoq.genarg_grammar wit_tactic)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ltac_use_default),
            Extend.Aentry (Pcoq.genarg_grammar wit_ltac_use_default)))];
     [Egramml.GramTerminal "par"; Egramml.GramTerminal ":";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_opt wit_ltac_info)),
            Extend.Aopt (Extend.Aentry (Pcoq.genarg_grammar wit_ltac_info))));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_tactic),
            Extend.Aentry (Pcoq.genarg_grammar wit_tactic)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ltac_use_default),
            Extend.Aentry (Pcoq.genarg_grammar wit_ltac_use_default)))]]

let pr_ltac_tactic_level n = (++) ((++) (str "(at level ") (int n)) (str ")")

let (wit_ltac_tactic_level : ('a, unit, unit) Genarg.genarg_type) =
  Genarg.create_arg "ltac_tactic_level"
let ltac_tactic_level =
  let ltac_tactic_level =
    Pcoq.create_generic_entry Pcoq.utactic "ltac_tactic_level"
      (Genarg.rawwit wit_ltac_tactic_level)
  in
  let () =
    Pcoq.grammar_extend ltac_tactic_level None
      (None,
       [None, None,
        [Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next
                    (Extend.Next
                       (Extend.Next
                          (Extend.Stop, Extend.Atoken (CLexer.terminal "(")),
                        Extend.Atoken (CLexer.terminal "at")),
                     Extend.Atoken (CLexer.terminal "level")),
                  Extend.Aentry natural),
               Extend.Atoken (CLexer.terminal ")")),
            (fun _ n _ _ _ loc -> n))]])
  in
  ltac_tactic_level
let _ =
  Pptactic.declare_extra_vernac_genarg_pprule wit_ltac_tactic_level
    (fun _ _ _ -> pr_ltac_tactic_level)

let (wit_ltac_production_sep : ('a, unit, unit) Genarg.genarg_type) =
  Genarg.create_arg "ltac_production_sep"
let ltac_production_sep =
  let ltac_production_sep =
    Pcoq.create_generic_entry Pcoq.utactic "ltac_production_sep"
      (Genarg.rawwit wit_ltac_production_sep)
  in
  let () =
    Pcoq.grammar_extend ltac_production_sep None
      (None,
       [None, None,
        [Extend.Rule
           (Extend.Next
              (Extend.Next (Extend.Stop, Extend.Atoken (CLexer.terminal ",")),
               Extend.Aentry string),
            (fun sep _ loc -> sep))]])
  in
  ltac_production_sep
let _ =
  Pptactic.declare_extra_vernac_genarg_pprule wit_ltac_production_sep
    (fun _ _ _ _ -> Pp.str "[No printer for ltac_production_sep]")

let pr_ltac_production_item =
  function
    Tacentries.TacTerm s -> quote (str s)
  | Tacentries.TacNonTerm (_, ((arg, None), None)) -> str arg
  | Tacentries.TacNonTerm (_, ((arg, Some _), None)) -> assert false
  | Tacentries.TacNonTerm (_, ((arg, sep), Some id)) ->
      let sep =
        match sep with
          None -> mt ()
        | Some sep -> (++) ((++) (str ",") (spc ())) (quote (str sep))
      in
      (++) ((++) ((++) ((++) (str arg) (str "(")) (Id.print id)) sep)
        (str ")")

let (wit_ltac_production_item : ('a, unit, unit) Genarg.genarg_type) =
  Genarg.create_arg "ltac_production_item"
let ltac_production_item =
  let ltac_production_item =
    Pcoq.create_generic_entry Pcoq.utactic "ltac_production_item"
      (Genarg.rawwit wit_ltac_production_item)
  in
  let () =
    Pcoq.grammar_extend ltac_production_item None
      (None,
       [None, None,
        [Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Aentry ident),
            (fun nt loc ->
               Tacentries.TacNonTerm
                 (Loc.tag ~loc ((Id.to_string nt, None), None))));
         Extend.Rule
           (Extend.Next
              (Extend.Next
                 (Extend.Next
                    (Extend.Next
                       (Extend.Next (Extend.Stop, Extend.Aentry ident),
                        Extend.Atoken (CLexer.terminal "(")),
                     Extend.Aentry ident),
                  Extend.Aopt (Extend.Aentry ltac_production_sep)),
               Extend.Atoken (CLexer.terminal ")")),
            (fun _ sep p _ nt loc ->
               Tacentries.TacNonTerm
                 (Loc.tag ~loc ((Id.to_string nt, sep), Some p))));
         Extend.Rule
           (Extend.Next (Extend.Stop, Extend.Aentry string),
            (fun s loc -> Tacentries.TacTerm s))]])
  in
  ltac_production_item
let _ =
  Pptactic.declare_extra_vernac_genarg_pprule wit_ltac_production_item
    (fun _ _ _ -> pr_ltac_production_item)

let _ =
  CList.iteri
    (fun i (depr, f) ->
       Vernacinterp.vinterp_add depr ("VernacTacticNotation", i) f)
    [false,
     (function
        [n; r; e] ->
          let n =
            Genarg.out_gen
              (Genarg.rawwit (Genarg.wit_opt wit_ltac_tactic_level)) n
          in
          let r =
            Genarg.out_gen
              (Genarg.rawwit (Genarg.wit_list wit_ltac_production_item)) r
          in
          let e = Genarg.out_gen (Genarg.rawwit wit_tactic) e in
          (fun ~atts ~st ->
             let open Vernacinterp in
             let n = Option.default 0 n in
             Tacentries.add_tactic_notation
               (Locality.make_module_locality atts.locality) n r e;
             st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("VernacTacticNotation", i)
         f)
    [(function
        [n; r; e] ->
          let n =
            Genarg.out_gen
              (Genarg.rawwit (Genarg.wit_opt wit_ltac_tactic_level)) n
          in
          let r =
            Genarg.out_gen
              (Genarg.rawwit (Genarg.wit_list wit_ltac_production_item)) r
          in
          let e = Genarg.out_gen (Genarg.rawwit wit_tactic) e in
          let _ = let _ = n in let _ = r in let _ = e in () in
          (fun loc -> VtSideff [], VtNow)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("VernacTacticNotation", i) None
         r)
    [[Egramml.GramTerminal "Tactic"; Egramml.GramTerminal "Notation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_opt wit_ltac_tactic_level)),
            Extend.Aopt
              (Extend.Aentry (Pcoq.genarg_grammar wit_ltac_tactic_level))));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_list wit_ltac_production_item)),
            Extend.Alist1
              (Extend.Aentry
                 (Pcoq.genarg_grammar wit_ltac_production_item))));
      Egramml.GramTerminal ":=";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_tactic),
            Extend.Aentry (Pcoq.genarg_grammar wit_tactic)))]]

let _ =
  CList.iteri
    (fun i (depr, f) ->
       Vernacinterp.vinterp_add depr ("VernacPrintLtac", i) f)
    [false,
     (function
        [r] ->
          let r = Genarg.out_gen (Genarg.rawwit wit_reference) r in
          (fun ~atts ~st ->
             let () =
               Feedback.msg_notice
                 (Tacintern.print_ltac
                    (Libnames.qualid_of_reference r).CAst.v)
             in
             st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("VernacPrintLtac", i) f)
    [(function
        [r] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_query) "VernacPrintLtac")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("VernacPrintLtac", i) None r)
    [[Egramml.GramTerminal "Print"; Egramml.GramTerminal "Ltac";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_reference),
            Extend.Aentry (Pcoq.genarg_grammar wit_reference)))]]

let _ =
  CList.iteri
    (fun i (depr, f) ->
       Vernacinterp.vinterp_add depr ("VernacLocateLtac", i) f)
    [false,
     (function
        [r] ->
          let r = Genarg.out_gen (Genarg.rawwit wit_reference) r in
          (fun ~atts ~st -> let () = Tacentries.print_located_tactic r in st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("VernacLocateLtac", i) f)
    [(function
        [r] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_query)
               "VernacLocateLtac")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("VernacLocateLtac", i) None r)
    [[Egramml.GramTerminal "Locate"; Egramml.GramTerminal "Ltac";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_reference),
            Extend.Aentry (Pcoq.genarg_grammar wit_reference)))]]

let pr_ltac_ref = Libnames.pr_reference

let pr_tacdef_body tacdef_body =
  let (id, redef, body) =
    match tacdef_body with
      TacticDefinition ({CAst.v = id}, body) -> Id.print id, false, body
    | TacticRedefinition (id, body) -> pr_ltac_ref id, true, body
  in
  let (idl, body) =
    match body with
      Tacexpr.TacFun (idl, b) -> idl, b
    | _ -> [], body
  in
  (++)
    ((++)
       ((++)
          ((++) id
             (prlist
                (function
                   Name.Anonymous -> str " _"
                 | Name.Name id -> (++) (spc ()) (Id.print id))
                idl))
          (if redef then str " ::=" else str " :="))
       (brk (1, 1)))
    (Pptactic.pr_raw_tactic body)

let (wit_ltac_tacdef_body : ('a, unit, unit) Genarg.genarg_type) =
  Genarg.create_arg "ltac_tacdef_body"
let ltac_tacdef_body =
  let () = Pcoq.register_grammar wit_ltac_tacdef_body tacdef_body in
  tacdef_body
let _ =
  Pptactic.declare_extra_vernac_genarg_pprule wit_ltac_tacdef_body
    (fun _ _ _ -> pr_tacdef_body)

let _ =
  CList.iteri
    (fun i (depr, f) ->
       Vernacinterp.vinterp_add depr ("VernacDeclareTacticDefinition", i) f)
    [false,
     (function
        [l] ->
          let l =
            Genarg.out_gen
              (Genarg.rawwit (Genarg.wit_list wit_ltac_tacdef_body)) l
          in
          (fun ~atts ~st ->
             let open Vernacinterp in
             begin
               Tacentries.register_ltac
                 (Locality.make_module_locality atts.locality) l;
               st
             end)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier
         ("VernacDeclareTacticDefinition", i) f)
    [(function
        [l] ->
          let l =
            Genarg.out_gen
              (Genarg.rawwit (Genarg.wit_list wit_ltac_tacdef_body)) l
          in
          let _ = let _ = l in () in
          (fun loc ->
             VtSideff
               (List.map
                  (function
                     TacticDefinition ({CAst.v = r}, _) -> r
                   | TacticRedefinition ({CAst.v = Ident r}, _) -> r
                   | TacticRedefinition ({CAst.v = Qualid q}, _) ->
                       snd (repr_qualid q))
                  l),
             VtLater)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar
         ("VernacDeclareTacticDefinition", i) None r)
    [[Egramml.GramTerminal "Ltac";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit (Genarg.wit_list wit_ltac_tacdef_body)),
            Extend.Alist1sep
              (Extend.Aentry (Pcoq.genarg_grammar wit_ltac_tacdef_body),
               Extend.Atoken (CLexer.terminal "with"))))]]

let _ =
  CList.iteri
    (fun i (depr, f) ->
       Vernacinterp.vinterp_add depr ("VernacPrintLtacs", i) f)
    [false,
     (function
        [] -> (fun ~atts ~st -> let () = Tacentries.print_ltacs () in st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("VernacPrintLtacs", i) f)
    [(function
        [] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_query)
               "VernacPrintLtacs")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("VernacPrintLtacs", i) None r)
    [[Egramml.GramTerminal "Print"; Egramml.GramTerminal "Ltac";
      Egramml.GramTerminal "Signatures"]]
