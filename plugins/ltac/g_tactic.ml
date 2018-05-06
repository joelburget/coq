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
open CErrors
open Util
open Tacexpr
open Genredexpr
open Constrexpr
open Libnames
open Tok
open Misctypes
open Locus
open Decl_kinds

open Pcoq


let all_with delta =
  Redops.make_red_flag [FBeta; FMatch; FFix; FCofix; FZeta; delta]

let tactic_kw = ["->"; "<-"; "by"]
let _ = List.iter CLexer.add_keyword tactic_kw

let err () = raise Stream.Failure

(* Hack to parse "(x:=t)" as an explicit argument without conflicts with the *)
(* admissible notation "(x t)" *)
let test_lpar_id_coloneq =
  Gram.Entry.of_parser "lpar_id_coloneq"
    (fun strm ->
       match stream_nth 0 strm with
         KEYWORD "(" ->
           begin match stream_nth 1 strm with
             IDENT _ ->
               begin match stream_nth 2 strm with
                 KEYWORD ":=" -> ()
               | _ -> err ()
               end
           | _ -> err ()
           end
       | _ -> err ())

(* Hack to recognize "(x)" *)
let test_lpar_id_rpar =
  Gram.Entry.of_parser "lpar_id_coloneq"
    (fun strm ->
       match stream_nth 0 strm with
         KEYWORD "(" ->
           begin match stream_nth 1 strm with
             IDENT _ ->
               begin match stream_nth 2 strm with
                 KEYWORD ")" -> ()
               | _ -> err ()
               end
           | _ -> err ()
           end
       | _ -> err ())

(* idem for (x:=t) and (1:=t) *)
let test_lpar_idnum_coloneq =
  Gram.Entry.of_parser "test_lpar_idnum_coloneq"
    (fun strm ->
       match stream_nth 0 strm with
         KEYWORD "(" ->
           begin match stream_nth 1 strm with
             IDENT _ | INT _ ->
               begin match stream_nth 2 strm with
                 KEYWORD ":=" -> ()
               | _ -> err ()
               end
           | _ -> err ()
           end
       | _ -> err ())

(* idem for (x:t) *)
open Extraargs

(* idem for (x1..xn:t) [n^2 complexity but exceptional use] *)
let check_for_coloneq =
  Gram.Entry.of_parser "lpar_id_colon"
    (fun strm ->
       let rec skip_to_rpar p n =
         match List.last (Stream.npeek n strm) with
           KEYWORD "(" -> skip_to_rpar (p + 1) (n + 1)
         | KEYWORD ")" ->
             if Int.equal p 0 then n + 1 else skip_to_rpar (p - 1) (n + 1)
         | KEYWORD "." -> err ()
         | _ -> skip_to_rpar p (n + 1)
       in
       let rec skip_names n =
         match List.last (Stream.npeek n strm) with
           IDENT _ | KEYWORD "_" -> skip_names (n + 1)
         | KEYWORD ":" -> skip_to_rpar 0 (n + 1)
         | _ -> err ()
       in
       let rec skip_binders n =
         match List.last (Stream.npeek n strm) with
           KEYWORD "(" -> skip_binders (skip_names (n + 1))
         | IDENT _ | KEYWORD "_" -> skip_binders (n + 1)
         | KEYWORD ":=" -> ()
         | _ -> err ()
       in
       match stream_nth 0 strm with
         KEYWORD "(" -> skip_binders 2
       | _ -> err ())

let lookup_at_as_comma =
  Gram.Entry.of_parser "lookup_at_as_comma"
    (fun strm ->
       match stream_nth 0 strm with
         KEYWORD ("," | "at" | "as") -> ()
       | _ -> err ())

open Constr
open Prim
open Pltac

let mk_fix_tac (loc, id, bl, ann, ty) =
  let n =
    match bl, ann with
      [[_], _, _], None -> 1
    | _, Some x ->
        let ids =
          List.map (fun x -> x.CAst.v)
            (List.flatten (List.map (fun (nal, _, _) -> nal) bl))
        in
        begin try List.index Names.Name.equal x.CAst.v ids with
          Not_found -> user_err Pp.(str "No such fix variable.")
        end
    | _ -> user_err Pp.(str "Cannot guess decreasing argument of fix.")
  in
  let bl = List.map (fun (nal, bk, t) -> CLocalAssum (nal, bk, t)) bl in
  id, n, (@@) (CAst.make ~loc) (CProdN (bl, ty))

let mk_cofix_tac (loc, id, bl, ann, ty) =
  let _ =
    Option.map
      (fun {CAst.loc = aloc} ->
         user_err ?loc:aloc ~hdr:"Constr:mk_cofix_tac"
           (Pp.str "Annotation forbidden in cofix expression."))
      ann
  in
  let bl = List.map (fun (nal, bk, t) -> CLocalAssum (nal, bk, t)) bl in
  id, (@@) (CAst.make ~loc) (CProdN (bl, ty))

(* Functions overloaded by quotifier *)
let destruction_arg_of_constr (c, lbind as clbind) =
  match lbind with
    NoBindings ->
      begin try
        ElimOnIdent
          (CAst.make ?loc:(Constrexpr_ops.constr_loc c)
             (Constrexpr_ops.coerce_to_id c).CAst.v)
      with e when CErrors.noncritical e -> ElimOnConstr clbind
      end
  | _ -> ElimOnConstr clbind

let mkNumeral n = Numeral (string_of_int (abs n), 0 <= n)

let mkTacCase with_evar =
  function
    [(clear, ElimOnConstr cl), (None, None), None], None ->
      TacCase (with_evar, (clear, cl))
  | [(clear, ElimOnAnonHyp n), (None, None), None], None ->
      TacCase
        (with_evar,
         (clear, ((@@) CAst.make (CPrim (mkNumeral n)), NoBindings)))
  | [(clear, ElimOnIdent id), (None, None), None], None ->
      TacCase
        (with_evar,
         (clear,
          ((@@) CAst.make
             (CRef
                ((@@) (CAst.make ?loc:id.CAst.loc) (Ident id.CAst.v), None)),
           NoBindings)))
  | ic ->
      if List.exists
           (function
              (_, ElimOnAnonHyp _), _, _ -> true
            | _ -> false)
           (fst ic)
      then
        user_err
          Pp
          .(str
            "Use of numbers as direct arguments of 'case' is not supported.");
      TacInductionDestruct (false, with_evar, ic)

let rec mkCLambdaN_simple_loc ?loc bll c =
  match bll with
    (({CAst.loc = loc1} :: _ as idl), bk, t) :: bll ->
      (@@) (CAst.make ?loc)
        (CLambdaN
           ([CLocalAssum (idl, bk, t)],
            mkCLambdaN_simple_loc ?loc:(Loc.merge_opt loc1 loc) bll c))
  | ([], _, _) :: bll -> mkCLambdaN_simple_loc ?loc bll c
  | [] -> c

let mkCLambdaN_simple bl c =
  match bl with
    [] -> c
  | h :: _ ->
      let loc =
        Loc.merge_opt (List.hd (pi1 h)).CAst.loc (Constrexpr_ops.constr_loc c)
      in
      mkCLambdaN_simple_loc ?loc bl c

let loc_of_ne_list l =
  Loc.merge_opt (List.hd l).CAst.loc (List.last l).CAst.loc

let map_int_or_var f =
  function
    ArgArg x -> ArgArg (f x)
  | ArgVar _ as y -> y

let all_concl_occs_clause = {onhyps = Some []; concl_occs = AllOccurrences}

let merge_occurrences loc cl =
  function
    None ->
      if Locusops.clause_with_generic_occurrences cl then None, cl
      else
        user_err ~loc (str "Found an \"at\" clause without \"with\" clause.")
  | Some (occs, p) ->
      let ans =
        match occs with
          AllOccurrences -> cl
        | _ ->
            match cl with
              {onhyps = Some []; concl_occs = AllOccurrences} ->
                {onhyps = Some []; concl_occs = occs}
            | {onhyps = Some [(AllOccurrences, id), l];
               concl_occs = NoOccurrences} ->
                {cl with onhyps = Some [(occs, id), l]}
            | _ ->
                if Locusops.clause_with_generic_occurrences cl then
                  user_err ~loc
                    (str
                       "Unable to interpret the \"at\" clause; move it in the \"in\" clause.")
                else user_err ~loc (str "Cannot use clause \"at\" twice.")
      in
      Some p, ans

let warn_deprecated_eqn_syntax =
  CWarnings.create ~name:"deprecated-eqn-syntax" ~category:"deprecated"
    (fun arg ->
       strbrk
         (Printf.sprintf
            "Syntax \"_eqn:%s\" is deprecated. Please use \"eqn:%s\" instead."
            arg arg))

(* Auxiliary grammar rules *)

open Vernac_

let _ =
  let _ = (simple_tactic : 'simple_tactic Gram.Entry.e)
  and _ = (constr_with_bindings : 'constr_with_bindings Gram.Entry.e)
  and _ = (quantified_hypothesis : 'quantified_hypothesis Gram.Entry.e)
  and _ = (bindings : 'bindings Gram.Entry.e)
  and _ = (red_expr : 'red_expr Gram.Entry.e)
  and _ = (int_or_var : 'int_or_var Gram.Entry.e)
  and _ = (open_constr : 'open_constr Gram.Entry.e)
  and _ = (uconstr : 'uconstr Gram.Entry.e)
  and _ = (simple_intropattern : 'simple_intropattern Gram.Entry.e)
  and _ = (in_clause : 'in_clause Gram.Entry.e)
  and _ = (clause_dft_concl : 'clause_dft_concl Gram.Entry.e)
  and _ = (hypident : 'hypident Gram.Entry.e)
  and _ = (destruction_arg : 'destruction_arg Gram.Entry.e) in
  let grammar_entry_create = Gram.Entry.create in
  let nat_or_var : 'nat_or_var Gram.Entry.e =
    grammar_entry_create "nat_or_var"
  and id_or_meta : 'id_or_meta Gram.Entry.e =
    (* An identifier or a quotation meta-variable *)
    grammar_entry_create "id_or_meta"
  and constr_with_bindings_arg : 'constr_with_bindings_arg Gram.Entry.e =
    grammar_entry_create "constr_with_bindings_arg"
  and conversion : 'conversion Gram.Entry.e =
    grammar_entry_create "conversion"
  and occs_nums : 'occs_nums Gram.Entry.e = grammar_entry_create "occs_nums"
  and occs : 'occs Gram.Entry.e = grammar_entry_create "occs"
  and pattern_occ : 'pattern_occ Gram.Entry.e =
    grammar_entry_create "pattern_occ"
  and ref_or_pattern_occ : 'ref_or_pattern_occ Gram.Entry.e =
    grammar_entry_create "ref_or_pattern_occ"
  and unfold_occ : 'unfold_occ Gram.Entry.e =
    grammar_entry_create "unfold_occ"
  and intropatterns : 'intropatterns Gram.Entry.e =
    grammar_entry_create "intropatterns"
  and ne_intropatterns : 'ne_intropatterns Gram.Entry.e =
    grammar_entry_create "ne_intropatterns"
  and or_and_intropattern : 'or_and_intropattern Gram.Entry.e =
    grammar_entry_create "or_and_intropattern"
  and equality_intropattern : 'equality_intropattern Gram.Entry.e =
    grammar_entry_create "equality_intropattern"
  and naming_intropattern : 'naming_intropattern Gram.Entry.e =
    grammar_entry_create "naming_intropattern"
  and nonsimple_intropattern : 'nonsimple_intropattern Gram.Entry.e =
    grammar_entry_create "nonsimple_intropattern"
  and simple_intropattern_closed : 'simple_intropattern_closed Gram.Entry.e =
    grammar_entry_create "simple_intropattern_closed"
  and simple_binding : 'simple_binding Gram.Entry.e =
    grammar_entry_create "simple_binding"
  and with_bindings : 'with_bindings Gram.Entry.e =
    grammar_entry_create "with_bindings"
  and red_flags : 'red_flags Gram.Entry.e = grammar_entry_create "red_flags"
  and delta_flag : 'delta_flag Gram.Entry.e =
    grammar_entry_create "delta_flag"
  and strategy_flag : 'strategy_flag Gram.Entry.e =
    grammar_entry_create "strategy_flag"
  and hypident_occ : 'hypident_occ Gram.Entry.e =
    grammar_entry_create "hypident_occ"
  and clause_dft_all : 'clause_dft_all Gram.Entry.e =
    grammar_entry_create "clause_dft_all"
  and opt_clause : 'opt_clause Gram.Entry.e =
    grammar_entry_create "opt_clause"
  and concl_occ : 'concl_occ Gram.Entry.e = grammar_entry_create "concl_occ"
  and in_hyp_list : 'in_hyp_list Gram.Entry.e =
    grammar_entry_create "in_hyp_list"
  and in_hyp_as : 'in_hyp_as Gram.Entry.e = grammar_entry_create "in_hyp_as"
  and orient : 'orient Gram.Entry.e = grammar_entry_create "orient"
  and simple_binder : 'simple_binder Gram.Entry.e =
    grammar_entry_create "simple_binder"
  and fixdecl : 'fixdecl Gram.Entry.e = grammar_entry_create "fixdecl"
  and fixannot : 'fixannot Gram.Entry.e = grammar_entry_create "fixannot"
  and cofixdecl : 'cofixdecl Gram.Entry.e = grammar_entry_create "cofixdecl"
  and bindings_with_parameters : 'bindings_with_parameters Gram.Entry.e =
    grammar_entry_create "bindings_with_parameters"
  and eliminator : 'eliminator Gram.Entry.e =
    grammar_entry_create "eliminator"
  and as_ipat : 'as_ipat Gram.Entry.e = grammar_entry_create "as_ipat"
  and or_and_intropattern_loc : 'or_and_intropattern_loc Gram.Entry.e =
    grammar_entry_create "or_and_intropattern_loc"
  and as_or_and_ipat : 'as_or_and_ipat Gram.Entry.e =
    grammar_entry_create "as_or_and_ipat"
  and eqn_ipat : 'eqn_ipat Gram.Entry.e = grammar_entry_create "eqn_ipat"
  and as_name : 'as_name Gram.Entry.e = grammar_entry_create "as_name"
  and by_tactic : 'by_tactic Gram.Entry.e = grammar_entry_create "by_tactic"
  and rewriter : 'rewriter Gram.Entry.e = grammar_entry_create "rewriter"
  and oriented_rewriter : 'oriented_rewriter Gram.Entry.e =
    grammar_entry_create "oriented_rewriter"
  and induction_clause : 'induction_clause Gram.Entry.e =
    grammar_entry_create "induction_clause"
  and induction_clause_list : 'induction_clause_list Gram.Entry.e =
    grammar_entry_create "induction_clause_list"
  in
  Gram.extend (int_or_var : 'int_or_var Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e))],
      Gramext.action
        (fun (id : 'identref) (loc : Ploc.t) -> (ArgVar id : 'int_or_var));
      [Gramext.Snterm (Gram.Entry.obj (integer : 'integer Gram.Entry.e))],
      Gramext.action
        (fun (n : 'integer) (loc : Ploc.t) -> (ArgArg n : 'int_or_var))]];
  Gram.extend (nat_or_var : 'nat_or_var Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e))],
      Gramext.action
        (fun (id : 'identref) (loc : Ploc.t) -> (ArgVar id : 'nat_or_var));
      [Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e))],
      Gramext.action
        (fun (n : 'natural) (loc : Ploc.t) -> (ArgArg n : 'nat_or_var))]];
  Gram.extend (id_or_meta : 'id_or_meta Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e))],
      Gramext.action
        (fun (id : 'identref) (loc : Ploc.t) -> (id : 'id_or_meta))]];
  Gram.extend (open_constr : 'open_constr Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'constr) (loc : Ploc.t) -> (c : 'open_constr))]];
  Gram.extend (uconstr : 'uconstr Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e))],
      Gramext.action (fun (c : 'constr) (loc : Ploc.t) -> (c : 'uconstr))]];
  Gram.extend (destruction_arg : 'destruction_arg Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj
            (constr_with_bindings_arg :
             'constr_with_bindings_arg Gram.Entry.e))],
      Gramext.action
        (fun (c : 'constr_with_bindings_arg) (loc : Ploc.t) ->
           (on_snd destruction_arg_of_constr c : 'destruction_arg));
      [Gramext.Snterm
         (Gram.Entry.obj
            (test_lpar_id_rpar : 'test_lpar_id_rpar Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj
            (constr_with_bindings : 'constr_with_bindings Gram.Entry.e))],
      Gramext.action
        (fun (c : 'constr_with_bindings) _ (loc : Ploc.t) ->
           (Some false, destruction_arg_of_constr c : 'destruction_arg));
      [Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e))],
      Gramext.action
        (fun (n : 'natural) (loc : Ploc.t) ->
           (None, ElimOnAnonHyp n : 'destruction_arg))]];
  Gram.extend
    (constr_with_bindings_arg : 'constr_with_bindings_arg Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj
            (constr_with_bindings : 'constr_with_bindings Gram.Entry.e))],
      Gramext.action
        (fun (c : 'constr_with_bindings) (loc : Ploc.t) ->
           (None, c : 'constr_with_bindings_arg));
      [Gramext.Stoken ("", ">");
       Gramext.Snterm
         (Gram.Entry.obj
            (constr_with_bindings : 'constr_with_bindings Gram.Entry.e))],
      Gramext.action
        (fun (c : 'constr_with_bindings) _ (loc : Ploc.t) ->
           (Some true, c : 'constr_with_bindings_arg))]];
  Gram.extend (quantified_hypothesis : 'quantified_hypothesis Gram.Entry.e)
    None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e))],
      Gramext.action
        (fun (n : 'natural) (loc : Ploc.t) ->
           (AnonHyp n : 'quantified_hypothesis));
      [Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e))],
      Gramext.action
        (fun (id : 'ident) (loc : Ploc.t) ->
           (NamedHyp id : 'quantified_hypothesis))]];
  Gram.extend (conversion : 'conversion Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.Stoken ("", "at");
       Gramext.Snterm (Gram.Entry.obj (occs_nums : 'occs_nums Gram.Entry.e));
       Gramext.Stoken ("", "with");
       Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e))],
      Gramext.action
        (fun (c2 : 'constr) _ (occs : 'occs_nums) _ (c1 : 'constr)
             (loc : Ploc.t) ->
           (Some (occs, c1), c2 : 'conversion));
      [Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.Stoken ("", "with");
       Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e))],
      Gramext.action
        (fun (c2 : 'constr) _ (c1 : 'constr) (loc : Ploc.t) ->
           (Some (AllOccurrences, c1), c2 : 'conversion));
      [Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'constr) (loc : Ploc.t) -> (None, c : 'conversion))]];
  Gram.extend (occs_nums : 'occs_nums Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "-");
       Gramext.Snterm
         (Gram.Entry.obj (nat_or_var : 'nat_or_var Gram.Entry.e));
       Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj (int_or_var : 'int_or_var Gram.Entry.e)))],
      Gramext.action
        (fun (nl : 'int_or_var list) (n : 'nat_or_var) _ (loc : Ploc.t) ->
           (AllOccurrencesBut (List.map (map_int_or_var abs) (n :: nl)) :
            'occs_nums));
      [Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (nat_or_var : 'nat_or_var Gram.Entry.e)))],
      Gramext.action
        (fun (nl : 'nat_or_var list) (loc : Ploc.t) ->
           (OnlyOccurrences nl : 'occs_nums))]];
  Gram.extend (occs : 'occs Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> (AllOccurrences : 'occs));
      [Gramext.Stoken ("", "at");
       Gramext.Snterm (Gram.Entry.obj (occs_nums : 'occs_nums Gram.Entry.e))],
      Gramext.action
        (fun (occs : 'occs_nums) _ (loc : Ploc.t) -> (occs : 'occs))]];
  Gram.extend (pattern_occ : 'pattern_occ Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (occs : 'occs Gram.Entry.e))],
      Gramext.action
        (fun (nl : 'occs) (c : 'constr) (loc : Ploc.t) ->
           (nl, c : 'pattern_occ))]];
  Gram.extend (ref_or_pattern_occ : 'ref_or_pattern_occ Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (occs : 'occs Gram.Entry.e))],
      Gramext.action
        (fun (nl : 'occs) (c : 'constr) (loc : Ploc.t) ->
           (nl, Inr c : 'ref_or_pattern_occ));
      [Gramext.Snterm
         (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (occs : 'occs Gram.Entry.e))],
      Gramext.action
        (fun (nl : 'occs) (c : 'smart_global) (loc : Ploc.t) ->
           (nl, Inl c : 'ref_or_pattern_occ))]];
  Gram.extend (unfold_occ : 'unfold_occ Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (occs : 'occs Gram.Entry.e))],
      Gramext.action
        (fun (nl : 'occs) (c : 'smart_global) (loc : Ploc.t) ->
           (nl, c : 'unfold_occ))]];
  Gram.extend (intropatterns : 'intropatterns Gram.Entry.e) None
    [None, None,
     [[Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj
               (nonsimple_intropattern :
                'nonsimple_intropattern Gram.Entry.e)))],
      Gramext.action
        (fun (l : 'nonsimple_intropattern list) (loc : Ploc.t) ->
           (l : 'intropatterns))]];
  Gram.extend (ne_intropatterns : 'ne_intropatterns Gram.Entry.e) None
    [None, None,
     [[Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj
               (nonsimple_intropattern :
                'nonsimple_intropattern Gram.Entry.e)))],
      Gramext.action
        (fun (l : 'nonsimple_intropattern list) (loc : Ploc.t) ->
           (l : 'ne_intropatterns))]];
  Gram.extend (or_and_intropattern : 'or_and_intropattern Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "(");
       Gramext.Snterm
         (Gram.Entry.obj
            (simple_intropattern : 'simple_intropattern Gram.Entry.e));
       Gramext.Stoken ("", "&");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj
               (simple_intropattern : 'simple_intropattern Gram.Entry.e)),
          Gramext.Stoken ("", "&"), false);
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (tc : 'simple_intropattern list) _ (si : 'simple_intropattern)
             _ (loc : Ploc.t) ->
           (let rec pairify =
              function
                [] | [_] | [_; _] as l -> l
              | t :: q ->
                  [t;
                   CAst.make ?loc:(loc_of_ne_list q)
                     (IntroAction
                        (IntroOrAndPattern (IntroAndPattern (pairify q))))]
            in
            IntroAndPattern (pairify (si :: tc)) :
            'or_and_intropattern));
      [Gramext.Stoken ("", "(");
       Gramext.Snterm
         (Gram.Entry.obj
            (simple_intropattern : 'simple_intropattern Gram.Entry.e));
       Gramext.Stoken ("", ",");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj
               (simple_intropattern : 'simple_intropattern Gram.Entry.e)),
          Gramext.Stoken ("", ","), false);
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (tc : 'simple_intropattern list) _ (si : 'simple_intropattern)
             _ (loc : Ploc.t) ->
           (IntroAndPattern (si :: tc) : 'or_and_intropattern));
      [Gramext.Stoken ("", "(");
       Gramext.Snterm
         (Gram.Entry.obj
            (simple_intropattern : 'simple_intropattern Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (si : 'simple_intropattern) _ (loc : Ploc.t) ->
           (IntroAndPattern [si] : 'or_and_intropattern));
      [Gramext.Stoken ("", "()")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (IntroAndPattern [] : 'or_and_intropattern));
      [Gramext.Stoken ("", "[");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj (intropatterns : 'intropatterns Gram.Entry.e)),
          Gramext.Stoken ("", "|"), false);
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (tc : 'intropatterns list) _ (loc : Ploc.t) ->
           (IntroOrPattern tc : 'or_and_intropattern))]];
  Gram.extend (equality_intropattern : 'equality_intropattern Gram.Entry.e)
    None
    [None, None,
     [[Gramext.Stoken ("", "[=");
       Gramext.Snterm
         (Gram.Entry.obj (intropatterns : 'intropatterns Gram.Entry.e));
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (tc : 'intropatterns) _ (loc : Ploc.t) ->
           (IntroInjection tc : 'equality_intropattern));
      [Gramext.Stoken ("", "<-")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           (IntroRewrite false : 'equality_intropattern));
      [Gramext.Stoken ("", "->")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           (IntroRewrite true : 'equality_intropattern))]];
  Gram.extend (naming_intropattern : 'naming_intropattern Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e))],
      Gramext.action
        (fun (id : 'ident) (loc : Ploc.t) ->
           (IntroIdentifier id : 'naming_intropattern));
      [Gramext.Stoken ("", "?")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (IntroAnonymous : 'naming_intropattern));
      [Gramext.Snterm
         (Gram.Entry.obj (pattern_ident : 'pattern_ident Gram.Entry.e))],
      Gramext.action
        (fun (prefix : 'pattern_ident) (loc : Ploc.t) ->
           (IntroFresh prefix : 'naming_intropattern))]];
  Gram.extend (nonsimple_intropattern : 'nonsimple_intropattern Gram.Entry.e)
    None
    [None, None,
     [[Gramext.Stoken ("", "**")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (IntroForthcoming false) :
            'nonsimple_intropattern));
      [Gramext.Stoken ("", "*")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (IntroForthcoming true) :
            'nonsimple_intropattern));
      [Gramext.Snterm
         (Gram.Entry.obj
            (simple_intropattern : 'simple_intropattern Gram.Entry.e))],
      Gramext.action
        (fun (l : 'simple_intropattern) (loc : Ploc.t) ->
           (l : 'nonsimple_intropattern))]];
  Gram.extend (simple_intropattern : 'simple_intropattern Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj
            (simple_intropattern_closed :
             'simple_intropattern_closed Gram.Entry.e));
       Gramext.Slist0
         (Gramext.srules
            [[Gramext.Stoken ("", "%");
              Gramext.Snterml
                (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e),
                 "0")],
             Gramext.action
               (fun (c : 'operconstr) _ (loc : Ploc.t) -> (c : 'e__1))])],
      Gramext.action
        (fun (l : 'e__1 list) (pat : 'simple_intropattern_closed)
             (loc : Ploc.t) ->
           (let {CAst.loc = loc0; v = pat} = pat in
            let f c pat =
              let loc1 = Constrexpr_ops.constr_loc c in
              let loc = Loc.merge_opt loc0 loc1 in
              IntroAction
                (IntroApplyOn (CAst.(make ?loc:loc1 c), CAst.(make ?loc pat)))
            in
            (@@) (CAst.make ~loc:((!@) loc)) (List.fold_right f l pat) :
            'simple_intropattern))]];
  Gram.extend
    (simple_intropattern_closed : 'simple_intropattern_closed Gram.Entry.e)
    None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj
            (naming_intropattern : 'naming_intropattern Gram.Entry.e))],
      Gramext.action
        (fun (pat : 'naming_intropattern) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (IntroNaming pat) :
            'simple_intropattern_closed));
      [Gramext.Stoken ("", "_")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (IntroAction IntroWildcard) :
            'simple_intropattern_closed));
      [Gramext.Snterm
         (Gram.Entry.obj
            (equality_intropattern : 'equality_intropattern Gram.Entry.e))],
      Gramext.action
        (fun (pat : 'equality_intropattern) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (IntroAction pat) :
            'simple_intropattern_closed));
      [Gramext.Snterm
         (Gram.Entry.obj
            (or_and_intropattern : 'or_and_intropattern Gram.Entry.e))],
      Gramext.action
        (fun (pat : 'or_and_intropattern) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc))
              (IntroAction (IntroOrAndPattern pat)) :
            'simple_intropattern_closed))]];
  Gram.extend (simple_binding : 'simple_binding Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "(");
       Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (c : 'lconstr) _ (n : 'natural) _ (loc : Ploc.t) ->
           (CAst.make ~loc:((!@) loc) (AnonHyp n, c) : 'simple_binding));
      [Gramext.Stoken ("", "(");
       Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (c : 'lconstr) _ (id : 'ident) _ (loc : Ploc.t) ->
           (CAst.make ~loc:((!@) loc) (NamedHyp id, c) : 'simple_binding))]];
  Gram.extend (bindings : 'bindings Gram.Entry.e) None
    [None, None,
     [[Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e)))],
      Gramext.action
        (fun (bl : 'constr list) (loc : Ploc.t) ->
           (ImplicitBindings bl : 'bindings));
      [Gramext.Snterm
         (Gram.Entry.obj
            (test_lpar_idnum_coloneq :
             'test_lpar_idnum_coloneq Gram.Entry.e));
       Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj
               (simple_binding : 'simple_binding Gram.Entry.e)))],
      Gramext.action
        (fun (bl : 'simple_binding list) _ (loc : Ploc.t) ->
           (ExplicitBindings bl : 'bindings))]];
  Gram.extend (constr_with_bindings : 'constr_with_bindings Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (with_bindings : 'with_bindings Gram.Entry.e))],
      Gramext.action
        (fun (l : 'with_bindings) (c : 'constr) (loc : Ploc.t) ->
           (c, l : 'constr_with_bindings))]];
  Gram.extend (with_bindings : 'with_bindings Gram.Entry.e) None
    [None, None,
     [[],
      Gramext.action (fun (loc : Ploc.t) -> (NoBindings : 'with_bindings));
      [Gramext.Stoken ("", "with");
       Gramext.Snterm (Gram.Entry.obj (bindings : 'bindings Gram.Entry.e))],
      Gramext.action
        (fun (bl : 'bindings) _ (loc : Ploc.t) -> (bl : 'with_bindings))]];
  Gram.extend (red_flags : 'red_flags Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "delta");
       Gramext.Snterm
         (Gram.Entry.obj (delta_flag : 'delta_flag Gram.Entry.e))],
      Gramext.action
        (fun (d : 'delta_flag) _ (loc : Ploc.t) -> ([d] : 'red_flags));
      [Gramext.Stoken ("IDENT", "zeta")],
      Gramext.action (fun _ (loc : Ploc.t) -> ([FZeta] : 'red_flags));
      [Gramext.Stoken ("IDENT", "cofix")],
      Gramext.action (fun _ (loc : Ploc.t) -> ([FCofix] : 'red_flags));
      [Gramext.Stoken ("IDENT", "fix")],
      Gramext.action (fun _ (loc : Ploc.t) -> ([FFix] : 'red_flags));
      [Gramext.Stoken ("IDENT", "match")],
      Gramext.action (fun _ (loc : Ploc.t) -> ([FMatch] : 'red_flags));
      [Gramext.Stoken ("IDENT", "iota")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> ([FMatch; FFix; FCofix] : 'red_flags));
      [Gramext.Stoken ("IDENT", "beta")],
      Gramext.action (fun _ (loc : Ploc.t) -> ([FBeta] : 'red_flags))]];
  Gram.extend (delta_flag : 'delta_flag Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> (FDeltaBut [] : 'delta_flag));
      [Gramext.Stoken ("", "[");
       Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e)));
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (idl : 'smart_global list) _ (loc : Ploc.t) ->
           (FConst idl : 'delta_flag));
      [Gramext.Stoken ("", "-"); Gramext.Stoken ("", "[");
       Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e)));
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (idl : 'smart_global list) _ _ (loc : Ploc.t) ->
           (FDeltaBut idl : 'delta_flag))]];
  Gram.extend (strategy_flag : 'strategy_flag Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (delta_flag : 'delta_flag Gram.Entry.e))],
      Gramext.action
        (fun (d : 'delta_flag) (loc : Ploc.t) ->
           (all_with d : 'strategy_flag));
      [Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (red_flags : 'red_flags Gram.Entry.e)))],
      Gramext.action
        (fun (s : 'red_flags list) (loc : Ploc.t) ->
           (Redops.make_red_flag (List.flatten s) : 'strategy_flag))]];
  Gram.extend (red_expr : 'red_expr Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "")],
      Gramext.action
        (fun (s : string) (loc : Ploc.t) -> (ExtraRedExpr s : 'red_expr));
      [Gramext.Stoken ("IDENT", "pattern");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj (pattern_occ : 'pattern_occ Gram.Entry.e)),
          Gramext.Stoken ("", ","), false)],
      Gramext.action
        (fun (pl : 'pattern_occ list) _ (loc : Ploc.t) ->
           (Pattern pl : 'red_expr));
      [Gramext.Stoken ("IDENT", "fold");
       Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e)))],
      Gramext.action
        (fun (cl : 'constr list) _ (loc : Ploc.t) -> (Fold cl : 'red_expr));
      [Gramext.Stoken ("IDENT", "unfold");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj (unfold_occ : 'unfold_occ Gram.Entry.e)),
          Gramext.Stoken ("", ","), false)],
      Gramext.action
        (fun (ul : 'unfold_occ list) _ (loc : Ploc.t) ->
           (Unfold ul : 'red_expr));
      (*[Gramext.Stoken ("IDENT", "native_compute");
       Gramext.Sopt
         (Gramext.Snterm
            (Gram.Entry.obj
               (ref_or_pattern_occ : 'ref_or_pattern_occ Gram.Entry.e)))],
      Gramext.action
        (fun (po : 'ref_or_pattern_occ option) _ (loc : Ploc.t) ->
           (CbvNative po : 'red_expr));
      [Gramext.Stoken ("IDENT", "vm_compute");
       Gramext.Sopt
         (Gramext.Snterm
            (Gram.Entry.obj
               (ref_or_pattern_occ : 'ref_or_pattern_occ Gram.Entry.e)))],
      Gramext.action
        (fun (po : 'ref_or_pattern_occ option) _ (loc : Ploc.t) ->
           (CbvVm po : 'red_expr)); *)
      [Gramext.Stoken ("IDENT", "compute");
       Gramext.Snterm
         (Gram.Entry.obj (delta_flag : 'delta_flag Gram.Entry.e))],
      Gramext.action
        (fun (delta : 'delta_flag) _ (loc : Ploc.t) ->
           (Cbv (all_with delta) : 'red_expr));
      [Gramext.Stoken ("IDENT", "lazy");
       Gramext.Snterm
         (Gram.Entry.obj (strategy_flag : 'strategy_flag Gram.Entry.e))],
      Gramext.action
        (fun (s : 'strategy_flag) _ (loc : Ploc.t) -> (Lazy s : 'red_expr));
      [Gramext.Stoken ("IDENT", "cbn");
       Gramext.Snterm
         (Gram.Entry.obj (strategy_flag : 'strategy_flag Gram.Entry.e))],
      Gramext.action
        (fun (s : 'strategy_flag) _ (loc : Ploc.t) -> (Cbn s : 'red_expr));
      [Gramext.Stoken ("IDENT", "cbv");
       Gramext.Snterm
         (Gram.Entry.obj (strategy_flag : 'strategy_flag Gram.Entry.e))],
      Gramext.action
        (fun (s : 'strategy_flag) _ (loc : Ploc.t) -> (Cbv s : 'red_expr));
      [Gramext.Stoken ("IDENT", "simpl");
       Gramext.Snterm
         (Gram.Entry.obj (delta_flag : 'delta_flag Gram.Entry.e));
       Gramext.Sopt
         (Gramext.Snterm
            (Gram.Entry.obj
               (ref_or_pattern_occ : 'ref_or_pattern_occ Gram.Entry.e)))],
      Gramext.action
        (fun (po : 'ref_or_pattern_occ option) (d : 'delta_flag) _
             (loc : Ploc.t) ->
           (Simpl (all_with d, po) : 'red_expr));
      [Gramext.Stoken ("IDENT", "hnf")],
      Gramext.action (fun _ (loc : Ploc.t) -> (Hnf : 'red_expr));
      [Gramext.Stoken ("IDENT", "red")],
      Gramext.action (fun _ (loc : Ploc.t) -> (Red false : 'red_expr))]];
  Gram.extend (hypident : 'hypident Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "("); Gramext.Stoken ("IDENT", "value");
       Gramext.Stoken ("IDENT", "of");
       Gramext.Snterm
         (Gram.Entry.obj (id_or_meta : 'id_or_meta Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (id : 'id_or_meta) _ _ _ (loc : Ploc.t) ->
           (let id : Misctypes.lident = id in id, InHypValueOnly :
            'hypident));
      [Gramext.Stoken ("", "("); Gramext.Stoken ("IDENT", "type");
       Gramext.Stoken ("IDENT", "of");
       Gramext.Snterm
         (Gram.Entry.obj (id_or_meta : 'id_or_meta Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (id : 'id_or_meta) _ _ _ (loc : Ploc.t) ->
           (let id : Misctypes.lident = id in id, InHypTypeOnly : 'hypident));
      [Gramext.Snterm
         (Gram.Entry.obj (id_or_meta : 'id_or_meta Gram.Entry.e))],
      Gramext.action
        (fun (id : 'id_or_meta) (loc : Ploc.t) ->
           (let id : Misctypes.lident = id in id, InHyp : 'hypident))]];
  Gram.extend (hypident_occ : 'hypident_occ Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (hypident : 'hypident Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (occs : 'occs Gram.Entry.e))],
      Gramext.action
        (fun (occs : 'occs) (id, l : 'hypident) (loc : Ploc.t) ->
           (let id : Misctypes.lident = id in (occs, id), l :
            'hypident_occ))]];
  Gram.extend (in_clause : 'in_clause Gram.Entry.e) None
    [None, None,
     [[Gramext.Slist0sep
         (Gramext.Snterm
            (Gram.Entry.obj (hypident_occ : 'hypident_occ Gram.Entry.e)),
          Gramext.Stoken ("", ","), false)],
      Gramext.action
        (fun (hl : 'hypident_occ list) (loc : Ploc.t) ->
           ({onhyps = Some hl; concl_occs = NoOccurrences} : 'in_clause));
      [Gramext.Slist0sep
         (Gramext.Snterm
            (Gram.Entry.obj (hypident_occ : 'hypident_occ Gram.Entry.e)),
          Gramext.Stoken ("", ","), false);
       Gramext.Stoken ("", "|-");
       Gramext.Snterm (Gram.Entry.obj (concl_occ : 'concl_occ Gram.Entry.e))],
      Gramext.action
        (fun (occs : 'concl_occ) _ (hl : 'hypident_occ list) (loc : Ploc.t) ->
           ({onhyps = Some hl; concl_occs = occs} : 'in_clause));
      [Gramext.Stoken ("", "*"); Gramext.Stoken ("", "|-");
       Gramext.Snterm (Gram.Entry.obj (concl_occ : 'concl_occ Gram.Entry.e))],
      Gramext.action
        (fun (occs : 'concl_occ) _ _ (loc : Ploc.t) ->
           ({onhyps = None; concl_occs = occs} : 'in_clause));
      [Gramext.Stoken ("", "*");
       Gramext.Snterm (Gram.Entry.obj (occs : 'occs Gram.Entry.e))],
      Gramext.action
        (fun (occs : 'occs) _ (loc : Ploc.t) ->
           ({onhyps = None; concl_occs = occs} : 'in_clause))]];
  Gram.extend (clause_dft_concl : 'clause_dft_concl Gram.Entry.e) None
    [None, None,
     [[],
      Gramext.action
        (fun (loc : Ploc.t) -> (all_concl_occs_clause : 'clause_dft_concl));
      [Gramext.Snterm (Gram.Entry.obj (occs : 'occs Gram.Entry.e))],
      Gramext.action
        (fun (occs : 'occs) (loc : Ploc.t) ->
           ({onhyps = Some []; concl_occs = occs} : 'clause_dft_concl));
      [Gramext.Stoken ("", "in");
       Gramext.Snterm (Gram.Entry.obj (in_clause : 'in_clause Gram.Entry.e))],
      Gramext.action
        (fun (cl : 'in_clause) _ (loc : Ploc.t) ->
           (cl : 'clause_dft_concl))]];
  Gram.extend (clause_dft_all : 'clause_dft_all Gram.Entry.e) None
    [None, None,
     [[],
      Gramext.action
        (fun (loc : Ploc.t) ->
           ({onhyps = None; concl_occs = AllOccurrences} : 'clause_dft_all));
      [Gramext.Stoken ("", "in");
       Gramext.Snterm (Gram.Entry.obj (in_clause : 'in_clause Gram.Entry.e))],
      Gramext.action
        (fun (cl : 'in_clause) _ (loc : Ploc.t) -> (cl : 'clause_dft_all))]];
  Gram.extend (opt_clause : 'opt_clause Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> (None : 'opt_clause));
      [Gramext.Stoken ("", "at");
       Gramext.Snterm (Gram.Entry.obj (occs_nums : 'occs_nums Gram.Entry.e))],
      Gramext.action
        (fun (occs : 'occs_nums) _ (loc : Ploc.t) ->
           (Some {onhyps = Some []; concl_occs = occs} : 'opt_clause));
      [Gramext.Stoken ("", "in");
       Gramext.Snterm (Gram.Entry.obj (in_clause : 'in_clause Gram.Entry.e))],
      Gramext.action
        (fun (cl : 'in_clause) _ (loc : Ploc.t) -> (Some cl : 'opt_clause))]];
  Gram.extend (concl_occ : 'concl_occ Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> (NoOccurrences : 'concl_occ));
      [Gramext.Stoken ("", "*");
       Gramext.Snterm (Gram.Entry.obj (occs : 'occs Gram.Entry.e))],
      Gramext.action
        (fun (occs : 'occs) _ (loc : Ploc.t) -> (occs : 'concl_occ))]];
  Gram.extend (in_hyp_list : 'in_hyp_list Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> ([] : 'in_hyp_list));
      [Gramext.Stoken ("", "in");
       Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (id_or_meta : 'id_or_meta Gram.Entry.e)))],
      Gramext.action
        (fun (idl : 'id_or_meta list) _ (loc : Ploc.t) ->
           (idl : 'in_hyp_list))]];
  Gram.extend (in_hyp_as : 'in_hyp_as Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> (None : 'in_hyp_as));
      [Gramext.Stoken ("", "in");
       Gramext.Snterm
         (Gram.Entry.obj (id_or_meta : 'id_or_meta Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (as_ipat : 'as_ipat Gram.Entry.e))],
      Gramext.action
        (fun (ipat : 'as_ipat) (id : 'id_or_meta) _ (loc : Ploc.t) ->
           (Some (id, ipat) : 'in_hyp_as))]];
  Gram.extend (orient : 'orient Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> (true : 'orient));
      [Gramext.Stoken ("", "<-")],
      Gramext.action (fun _ (loc : Ploc.t) -> (false : 'orient));
      [Gramext.Stoken ("", "->")],
      Gramext.action (fun _ (loc : Ploc.t) -> (true : 'orient))]];
  Gram.extend (simple_binder : 'simple_binder Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "(");
       Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e)));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (c : 'lconstr) _ (nal : 'name list) _ (loc : Ploc.t) ->
           (nal, Default Explicit, c : 'simple_binder));
      [Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e))],
      Gramext.action
        (fun (na : 'name) (loc : Ploc.t) ->
           ([na], Default Explicit,
            (@@) (CAst.make ~loc:((!@) loc))
              (CHole
                 (Some (Evar_kinds.BinderType na.CAst.v), IntroAnonymous,
                  None)) :
            'simple_binder))]];
  Gram.extend (fixdecl : 'fixdecl Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "(");
       Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e));
       Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj (simple_binder : 'simple_binder Gram.Entry.e)));
       Gramext.Snterm (Gram.Entry.obj (fixannot : 'fixannot Gram.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (ty : 'lconstr) _ (ann : 'fixannot) (bl : 'simple_binder list)
             (id : 'ident) _ (loc : Ploc.t) ->
           ((!@) loc, id, bl, ann, ty : 'fixdecl))]];
  Gram.extend (fixannot : 'fixannot Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> (None : 'fixannot));
      [Gramext.Stoken ("", "{"); Gramext.Stoken ("IDENT", "struct");
       Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e));
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (id : 'name) _ _ (loc : Ploc.t) -> (Some id : 'fixannot))]];
  Gram.extend (cofixdecl : 'cofixdecl Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "(");
       Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e));
       Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj (simple_binder : 'simple_binder Gram.Entry.e)));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (ty : 'lconstr) _ (bl : 'simple_binder list) (id : 'ident) _
             (loc : Ploc.t) ->
           ((!@) loc, id, bl, None, ty : 'cofixdecl))]];
  Gram.extend
    (bindings_with_parameters : 'bindings_with_parameters Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj
            (check_for_coloneq : 'check_for_coloneq Gram.Entry.e));
       Gramext.Stoken ("", "(");
       Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e));
       Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj (simple_binder : 'simple_binder Gram.Entry.e)));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (c : 'lconstr) _ (bl : 'simple_binder list) (id : 'ident) _ _
             (loc : Ploc.t) ->
           (id, mkCLambdaN_simple bl c : 'bindings_with_parameters))]];
  Gram.extend (eliminator : 'eliminator Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "using");
       Gramext.Snterm
         (Gram.Entry.obj
            (constr_with_bindings : 'constr_with_bindings Gram.Entry.e))],
      Gramext.action
        (fun (el : 'constr_with_bindings) _ (loc : Ploc.t) ->
           (el : 'eliminator))]];
  Gram.extend (as_ipat : 'as_ipat Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> (None : 'as_ipat));
      [Gramext.Stoken ("", "as");
       Gramext.Snterm
         (Gram.Entry.obj
            (simple_intropattern : 'simple_intropattern Gram.Entry.e))],
      Gramext.action
        (fun (ipat : 'simple_intropattern) _ (loc : Ploc.t) ->
           (Some ipat : 'as_ipat))]];
  Gram.extend
    (or_and_intropattern_loc : 'or_and_intropattern_loc Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e))],
      Gramext.action
        (fun (locid : 'identref) (loc : Ploc.t) ->
           (ArgVar locid : 'or_and_intropattern_loc));
      [Gramext.Snterm
         (Gram.Entry.obj
            (or_and_intropattern : 'or_and_intropattern Gram.Entry.e))],
      Gramext.action
        (fun (ipat : 'or_and_intropattern) (loc : Ploc.t) ->
           (ArgArg (CAst.make ~loc:((!@) loc) ipat) :
            'or_and_intropattern_loc))]];
  Gram.extend (as_or_and_ipat : 'as_or_and_ipat Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> (None : 'as_or_and_ipat));
      [Gramext.Stoken ("", "as");
       Gramext.Snterm
         (Gram.Entry.obj
            (or_and_intropattern_loc :
             'or_and_intropattern_loc Gram.Entry.e))],
      Gramext.action
        (fun (ipat : 'or_and_intropattern_loc) _ (loc : Ploc.t) ->
           (Some ipat : 'as_or_and_ipat))]];
  Gram.extend (eqn_ipat : 'eqn_ipat Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> (None : 'eqn_ipat));
      [Gramext.Stoken ("IDENT", "_eqn")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           (let loc = (!@) loc in
            warn_deprecated_eqn_syntax ~loc "?";
            Some (CAst.make ~loc IntroAnonymous) :
            'eqn_ipat));
      [Gramext.Stoken ("IDENT", "_eqn"); Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Gram.Entry.obj
            (naming_intropattern : 'naming_intropattern Gram.Entry.e))],
      Gramext.action
        (fun (pat : 'naming_intropattern) _ _ (loc : Ploc.t) ->
           (let loc = (!@) loc in
            warn_deprecated_eqn_syntax ~loc "H"; Some (CAst.make ~loc pat) :
            'eqn_ipat));
      [Gramext.Stoken ("IDENT", "eqn"); Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Gram.Entry.obj
            (naming_intropattern : 'naming_intropattern Gram.Entry.e))],
      Gramext.action
        (fun (pat : 'naming_intropattern) _ _ (loc : Ploc.t) ->
           (Some (CAst.make ~loc:((!@) loc) pat) : 'eqn_ipat))]];
  Gram.extend (as_name : 'as_name Gram.Entry.e) None
    [None, None,
     [[],
      Gramext.action
        (fun (loc : Ploc.t) -> (Names.Name.Anonymous : 'as_name));
      [Gramext.Stoken ("", "as");
       Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e))],
      Gramext.action
        (fun (id : 'ident) _ (loc : Ploc.t) ->
           (Names.Name.Name id : 'as_name))]];
  Gram.extend (by_tactic : 'by_tactic Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> (None : 'by_tactic));
      [Gramext.Stoken ("", "by");
       Gramext.Snterml
         (Gram.Entry.obj (tactic_expr : 'tactic_expr Gram.Entry.e), "3")],
      Gramext.action
        (fun (tac : 'tactic_expr) _ (loc : Ploc.t) ->
           (Some tac : 'by_tactic))]];
  Gram.extend (rewriter : 'rewriter Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj
            (constr_with_bindings_arg :
             'constr_with_bindings_arg Gram.Entry.e))],
      Gramext.action
        (fun (c : 'constr_with_bindings_arg) (loc : Ploc.t) ->
           (Precisely 1, c : 'rewriter));
      [Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj
            (constr_with_bindings_arg :
             'constr_with_bindings_arg Gram.Entry.e))],
      Gramext.action
        (fun (c : 'constr_with_bindings_arg) (n : 'natural) (loc : Ploc.t) ->
           (Precisely n, c : 'rewriter));
      [Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e));
       Gramext.srules
         [[Gramext.Stoken ("LEFTQMARK", "")],
          Gramext.action (fun (x : string) (loc : Ploc.t) -> (x : 'e__3));
          [Gramext.Stoken ("", "?")],
          Gramext.action (fun (x : string) (loc : Ploc.t) -> (x : 'e__3))];
       Gramext.Snterm
         (Gram.Entry.obj
            (constr_with_bindings_arg :
             'constr_with_bindings_arg Gram.Entry.e))],
      Gramext.action
        (fun (c : 'constr_with_bindings_arg) _ (n : 'natural)
             (loc : Ploc.t) ->
           (UpTo n, c : 'rewriter));
      [Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e));
       Gramext.Stoken ("", "!");
       Gramext.Snterm
         (Gram.Entry.obj
            (constr_with_bindings_arg :
             'constr_with_bindings_arg Gram.Entry.e))],
      Gramext.action
        (fun (c : 'constr_with_bindings_arg) _ (n : 'natural)
             (loc : Ploc.t) ->
           (Precisely n, c : 'rewriter));
      [Gramext.srules
         [[Gramext.Stoken ("LEFTQMARK", "")],
          Gramext.action (fun (x : string) (loc : Ploc.t) -> (x : 'e__2));
          [Gramext.Stoken ("", "?")],
          Gramext.action (fun (x : string) (loc : Ploc.t) -> (x : 'e__2))];
       Gramext.Snterm
         (Gram.Entry.obj
            (constr_with_bindings_arg :
             'constr_with_bindings_arg Gram.Entry.e))],
      Gramext.action
        (fun (c : 'constr_with_bindings_arg) _ (loc : Ploc.t) ->
           (RepeatStar, c : 'rewriter));
      [Gramext.Stoken ("", "!");
       Gramext.Snterm
         (Gram.Entry.obj
            (constr_with_bindings_arg :
             'constr_with_bindings_arg Gram.Entry.e))],
      Gramext.action
        (fun (c : 'constr_with_bindings_arg) _ (loc : Ploc.t) ->
           (RepeatPlus, c : 'rewriter))]];
  Gram.extend (oriented_rewriter : 'oriented_rewriter Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (orient : 'orient Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (rewriter : 'rewriter Gram.Entry.e))],
      Gramext.action
        (fun (p : 'rewriter) (b : 'orient) (loc : Ploc.t) ->
           (let (m, c) = p in b, m, c : 'oriented_rewriter))]];
  Gram.extend (induction_clause : 'induction_clause Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (destruction_arg : 'destruction_arg Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (as_or_and_ipat : 'as_or_and_ipat Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (eqn_ipat : 'eqn_ipat Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (opt_clause : 'opt_clause Gram.Entry.e))],
      Gramext.action
        (fun (cl : 'opt_clause) (eq : 'eqn_ipat) (pat : 'as_or_and_ipat)
             (c : 'destruction_arg) (loc : Ploc.t) ->
           (c, (eq, pat), cl : 'induction_clause))]];
  Gram.extend (induction_clause_list : 'induction_clause_list Gram.Entry.e)
    None
    [None, None,
     [[Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj
               (induction_clause : 'induction_clause Gram.Entry.e)),
          Gramext.Stoken ("", ","), false);
       Gramext.Sopt
         (Gramext.Snterm
            (Gram.Entry.obj (eliminator : 'eliminator Gram.Entry.e)));
       Gramext.Snterm
         (Gram.Entry.obj (opt_clause : 'opt_clause Gram.Entry.e))],
      Gramext.action
        (fun (cl_tolerance : 'opt_clause) (el : 'eliminator option)
             (ic : 'induction_clause list) (loc : Ploc.t) ->
           (match ic, el, cl_tolerance with
              [c, pat, None], Some _, Some _ -> [c, pat, cl_tolerance], el
            | _, _, Some _ -> err ()
            | _, _, None -> ic, el :
            'induction_clause_list))]];
  Gram.extend (simple_tactic : 'simple_tactic Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "change");
       Gramext.Snterm
         (Gram.Entry.obj (conversion : 'conversion Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj
            (clause_dft_concl : 'clause_dft_concl Gram.Entry.e))],
      Gramext.action
        (fun (cl : 'clause_dft_concl) (oc, c : 'conversion) _
             (loc : Ploc.t) ->
           (let (p, cl) = merge_occurrences ((!@) loc) cl oc in
            TacAtom ((@@) (Loc.tag ~loc:((!@) loc)) (TacChange (p, c, cl))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "pattern");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj (pattern_occ : 'pattern_occ Gram.Entry.e)),
          Gramext.Stoken ("", ","), false);
       Gramext.Snterm
         (Gram.Entry.obj
            (clause_dft_concl : 'clause_dft_concl Gram.Entry.e))],
      Gramext.action
        (fun (cl : 'clause_dft_concl) (pl : 'pattern_occ list) _
             (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc)) (TacReduce (Pattern pl, cl))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "fold");
       Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e)));
       Gramext.Snterm
         (Gram.Entry.obj
            (clause_dft_concl : 'clause_dft_concl Gram.Entry.e))],
      Gramext.action
        (fun (cl : 'clause_dft_concl) (l : 'constr list) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc)) (TacReduce (Fold l, cl))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "unfold");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj (unfold_occ : 'unfold_occ Gram.Entry.e)),
          Gramext.Stoken ("", ","), false);
       Gramext.Snterm
         (Gram.Entry.obj
            (clause_dft_concl : 'clause_dft_concl Gram.Entry.e))],
      Gramext.action
        (fun (cl : 'clause_dft_concl) (ul : 'unfold_occ list) _
             (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc)) (TacReduce (Unfold ul, cl))) :
            'simple_tactic));
      (* [Gramext.Stoken ("IDENT", "native_compute");
       Gramext.Sopt
         (Gramext.Snterm
            (Gram.Entry.obj
               (ref_or_pattern_occ : 'ref_or_pattern_occ Gram.Entry.e)));
       Gramext.Snterm
         (Gram.Entry.obj
            (clause_dft_concl : 'clause_dft_concl Gram.Entry.e))],
      Gramext.action
        (fun (cl : 'clause_dft_concl) (po : 'ref_or_pattern_occ option) _
             (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacReduce (CbvNative po, cl))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "vm_compute");
       Gramext.Sopt
         (Gramext.Snterm
            (Gram.Entry.obj
               (ref_or_pattern_occ : 'ref_or_pattern_occ Gram.Entry.e)));
       Gramext.Snterm
         (Gram.Entry.obj
            (clause_dft_concl : 'clause_dft_concl Gram.Entry.e))],
      Gramext.action
        (fun (cl : 'clause_dft_concl) (po : 'ref_or_pattern_occ option) _
             (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc)) (TacReduce (CbvVm po, cl))) :
            'simple_tactic)); *)
      [Gramext.Stoken ("IDENT", "compute");
       Gramext.Snterm
         (Gram.Entry.obj (delta_flag : 'delta_flag Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj
            (clause_dft_concl : 'clause_dft_concl Gram.Entry.e))],
      Gramext.action
        (fun (cl : 'clause_dft_concl) (delta : 'delta_flag) _
             (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacReduce (Cbv (all_with delta), cl))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "lazy");
       Gramext.Snterm
         (Gram.Entry.obj (strategy_flag : 'strategy_flag Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj
            (clause_dft_concl : 'clause_dft_concl Gram.Entry.e))],
      Gramext.action
        (fun (cl : 'clause_dft_concl) (s : 'strategy_flag) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc)) (TacReduce (Lazy s, cl))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "cbn");
       Gramext.Snterm
         (Gram.Entry.obj (strategy_flag : 'strategy_flag Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj
            (clause_dft_concl : 'clause_dft_concl Gram.Entry.e))],
      Gramext.action
        (fun (cl : 'clause_dft_concl) (s : 'strategy_flag) _ (loc : Ploc.t) ->
           (TacAtom ((@@) (Loc.tag ~loc:((!@) loc)) (TacReduce (Cbn s, cl))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "cbv");
       Gramext.Snterm
         (Gram.Entry.obj (strategy_flag : 'strategy_flag Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj
            (clause_dft_concl : 'clause_dft_concl Gram.Entry.e))],
      Gramext.action
        (fun (cl : 'clause_dft_concl) (s : 'strategy_flag) _ (loc : Ploc.t) ->
           (TacAtom ((@@) (Loc.tag ~loc:((!@) loc)) (TacReduce (Cbv s, cl))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "simpl");
       Gramext.Snterm
         (Gram.Entry.obj (delta_flag : 'delta_flag Gram.Entry.e));
       Gramext.Sopt
         (Gramext.Snterm
            (Gram.Entry.obj
               (ref_or_pattern_occ : 'ref_or_pattern_occ Gram.Entry.e)));
       Gramext.Snterm
         (Gram.Entry.obj
            (clause_dft_concl : 'clause_dft_concl Gram.Entry.e))],
      Gramext.action
        (fun (cl : 'clause_dft_concl) (po : 'ref_or_pattern_occ option)
             (d : 'delta_flag) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacReduce (Simpl (all_with d, po), cl))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "hnf");
       Gramext.Snterm
         (Gram.Entry.obj
            (clause_dft_concl : 'clause_dft_concl Gram.Entry.e))],
      Gramext.action
        (fun (cl : 'clause_dft_concl) _ (loc : Ploc.t) ->
           (TacAtom ((@@) (Loc.tag ~loc:((!@) loc)) (TacReduce (Hnf, cl))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "red");
       Gramext.Snterm
         (Gram.Entry.obj
            (clause_dft_concl : 'clause_dft_concl Gram.Entry.e))],
      Gramext.action
        (fun (cl : 'clause_dft_concl) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc)) (TacReduce (Red false, cl))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "inversion");
       Gramext.Snterm
         (Gram.Entry.obj
            (quantified_hypothesis : 'quantified_hypothesis Gram.Entry.e));
       Gramext.Stoken ("", "using");
       Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (in_hyp_list : 'in_hyp_list Gram.Entry.e))],
      Gramext.action
        (fun (cl : 'in_hyp_list) (c : 'constr) _
             (hyp : 'quantified_hypothesis) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacInversion (InversionUsing (c, cl), hyp))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "inversion_clear");
       Gramext.Snterm
         (Gram.Entry.obj
            (quantified_hypothesis : 'quantified_hypothesis Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (as_or_and_ipat : 'as_or_and_ipat Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (in_hyp_list : 'in_hyp_list Gram.Entry.e))],
      Gramext.action
        (fun (cl : 'in_hyp_list) (ids : 'as_or_and_ipat)
             (hyp : 'quantified_hypothesis) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacInversion
                    (NonDepInversion (FullInversionClear, cl, ids), hyp))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "inversion");
       Gramext.Snterm
         (Gram.Entry.obj
            (quantified_hypothesis : 'quantified_hypothesis Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (as_or_and_ipat : 'as_or_and_ipat Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (in_hyp_list : 'in_hyp_list Gram.Entry.e))],
      Gramext.action
        (fun (cl : 'in_hyp_list) (ids : 'as_or_and_ipat)
             (hyp : 'quantified_hypothesis) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacInversion
                    (NonDepInversion (FullInversion, cl, ids), hyp))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "simple");
       Gramext.Stoken ("IDENT", "inversion");
       Gramext.Snterm
         (Gram.Entry.obj
            (quantified_hypothesis : 'quantified_hypothesis Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (as_or_and_ipat : 'as_or_and_ipat Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (in_hyp_list : 'in_hyp_list Gram.Entry.e))],
      Gramext.action
        (fun (cl : 'in_hyp_list) (ids : 'as_or_and_ipat)
             (hyp : 'quantified_hypothesis) _ _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacInversion
                    (NonDepInversion (SimpleInversion, cl, ids), hyp))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "dependent");
       Gramext.srules
         [[Gramext.Stoken ("IDENT", "inversion_clear")],
          Gramext.action
            (fun _ (loc : Ploc.t) -> (FullInversionClear : 'e__5));
          [Gramext.Stoken ("IDENT", "inversion")],
          Gramext.action (fun _ (loc : Ploc.t) -> (FullInversion : 'e__5));
          [Gramext.Stoken ("IDENT", "simple");
           Gramext.Stoken ("IDENT", "inversion")],
          Gramext.action
            (fun _ _ (loc : Ploc.t) -> (SimpleInversion : 'e__5))];
       Gramext.Snterm
         (Gram.Entry.obj
            (quantified_hypothesis : 'quantified_hypothesis Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (as_or_and_ipat : 'as_or_and_ipat Gram.Entry.e));
       Gramext.Sopt
         (Gramext.srules
            [[Gramext.Stoken ("", "with");
              Gramext.Snterm
                (Gram.Entry.obj (constr : 'constr Gram.Entry.e))],
             Gramext.action
               (fun (c : 'constr) _ (loc : Ploc.t) -> (c : 'e__6))])],
      Gramext.action
        (fun (co : 'e__6 option) (ids : 'as_or_and_ipat)
             (hyp : 'quantified_hypothesis) (k : 'e__5) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacInversion (DepInversion (k, co, ids), hyp))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "erewrite");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj
               (oriented_rewriter : 'oriented_rewriter Gram.Entry.e)),
          Gramext.Stoken ("", ","), false);
       Gramext.Snterm
         (Gram.Entry.obj (clause_dft_concl : 'clause_dft_concl Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (by_tactic : 'by_tactic Gram.Entry.e))],
      Gramext.action
        (fun (t : 'by_tactic) (cl : 'clause_dft_concl)
             (l : 'oriented_rewriter list) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc)) (TacRewrite (true, l, cl, t))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "rewrite");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj
               (oriented_rewriter : 'oriented_rewriter Gram.Entry.e)),
          Gramext.Stoken ("", ","), false);
       Gramext.Snterm
         (Gram.Entry.obj (clause_dft_concl : 'clause_dft_concl Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (by_tactic : 'by_tactic Gram.Entry.e))],
      Gramext.action
        (fun (t : 'by_tactic) (cl : 'clause_dft_concl)
             (l : 'oriented_rewriter list) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacRewrite (false, l, cl, t))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "edestruct");
       Gramext.Snterm
         (Gram.Entry.obj
            (induction_clause_list : 'induction_clause_list Gram.Entry.e))],
      Gramext.action
        (fun (icl : 'induction_clause_list) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacInductionDestruct (false, true, icl))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "destruct");
       Gramext.Snterm
         (Gram.Entry.obj
            (induction_clause_list : 'induction_clause_list Gram.Entry.e))],
      Gramext.action
        (fun (icl : 'induction_clause_list) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacInductionDestruct (false, false, icl))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "einduction");
       Gramext.Snterm
         (Gram.Entry.obj
            (induction_clause_list : 'induction_clause_list Gram.Entry.e))],
      Gramext.action
        (fun (ic : 'induction_clause_list) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacInductionDestruct (true, true, ic))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "induction");
       Gramext.Snterm
         (Gram.Entry.obj
            (induction_clause_list : 'induction_clause_list Gram.Entry.e))],
      Gramext.action
        (fun (ic : 'induction_clause_list) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacInductionDestruct (true, false, ic))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "generalize");
       Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj
            (lookup_at_as_comma : 'lookup_at_as_comma Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (occs : 'occs Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (as_name : 'as_name Gram.Entry.e));
       Gramext.Slist0
         (Gramext.srules
            [[Gramext.Stoken ("", ",");
              Gramext.Snterm
                (Gram.Entry.obj (pattern_occ : 'pattern_occ Gram.Entry.e));
              Gramext.Snterm
                (Gram.Entry.obj (as_name : 'as_name Gram.Entry.e))],
             Gramext.action
               (fun (na : 'as_name) (c : 'pattern_occ) _ (loc : Ploc.t) ->
                  (c, na : 'e__4))])],
      Gramext.action
        (fun (l : 'e__4 list) (na : 'as_name) (nl : 'occs) _ (c : 'constr) _
             (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacGeneralize (((nl, c), na) :: l))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "generalize");
       Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e)))],
      Gramext.action
        (fun (l : 'constr list) (c : 'constr) _ (loc : Ploc.t) ->
           (let gen_everywhere c =
              (AllOccurrences, c), Names.Name.Anonymous
            in
            TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacGeneralize (List.map gen_everywhere (c :: l)))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "generalize");
       Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'constr) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacGeneralize
                    [(AllOccurrences, c), Names.Name.Anonymous])) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "eenough");
       Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (as_ipat : 'as_ipat Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (by_tactic : 'by_tactic Gram.Entry.e))],
      Gramext.action
        (fun (tac : 'by_tactic) (ipat : 'as_ipat) (c : 'constr) _
             (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacAssert (true, false, Some tac, ipat, c))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "enough");
       Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (as_ipat : 'as_ipat Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (by_tactic : 'by_tactic Gram.Entry.e))],
      Gramext.action
        (fun (tac : 'by_tactic) (ipat : 'as_ipat) (c : 'constr) _
             (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacAssert (false, false, Some tac, ipat, c))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "epose"); Gramext.Stoken ("IDENT", "proof");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (as_ipat : 'as_ipat Gram.Entry.e))],
      Gramext.action
        (fun (ipat : 'as_ipat) (c : 'lconstr) _ _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacAssert (true, true, None, ipat, c))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "pose"); Gramext.Stoken ("IDENT", "proof");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (as_ipat : 'as_ipat Gram.Entry.e))],
      Gramext.action
        (fun (ipat : 'as_ipat) (c : 'lconstr) _ _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacAssert (false, true, None, ipat, c))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "eassert");
       Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (as_ipat : 'as_ipat Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (by_tactic : 'by_tactic Gram.Entry.e))],
      Gramext.action
        (fun (tac : 'by_tactic) (ipat : 'as_ipat) (c : 'constr) _
             (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacAssert (true, true, Some tac, ipat, c))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "assert");
       Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (as_ipat : 'as_ipat Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (by_tactic : 'by_tactic Gram.Entry.e))],
      Gramext.action
        (fun (tac : 'by_tactic) (ipat : 'as_ipat) (c : 'constr) _
             (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacAssert (false, true, Some tac, ipat, c))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "eenough");
       Gramext.Snterm
         (Gram.Entry.obj
            (test_lpar_id_colon : 'test_lpar_id_colon Gram.Entry.e));
       Gramext.Stoken ("", "(");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", ")");
       Gramext.Snterm (Gram.Entry.obj (by_tactic : 'by_tactic Gram.Entry.e))],
      Gramext.action
        (fun (tac : 'by_tactic) _ (c : 'lconstr) _ (lid : 'identref) _ _ _
             (loc : Ploc.t) ->
           (let {CAst.loc = loc; v = id} = lid in
            TacAtom
              ((@@) (Loc.tag ?loc)
                 (TacAssert
                    (true, false, Some tac,
                     Some
                       ((@@) (CAst.make ?loc)
                          (IntroNaming (IntroIdentifier id))),
                     c))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "enough");
       Gramext.Snterm
         (Gram.Entry.obj
            (test_lpar_id_colon : 'test_lpar_id_colon Gram.Entry.e));
       Gramext.Stoken ("", "(");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", ")");
       Gramext.Snterm (Gram.Entry.obj (by_tactic : 'by_tactic Gram.Entry.e))],
      Gramext.action
        (fun (tac : 'by_tactic) _ (c : 'lconstr) _ (lid : 'identref) _ _ _
             (loc : Ploc.t) ->
           (let {CAst.loc = loc; v = id} = lid in
            TacAtom
              ((@@) (Loc.tag ?loc)
                 (TacAssert
                    (false, false, Some tac,
                     Some
                       ((@@) (CAst.make ?loc)
                          (IntroNaming (IntroIdentifier id))),
                     c))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "eassert");
       Gramext.Snterm
         (Gram.Entry.obj
            (test_lpar_id_colon : 'test_lpar_id_colon Gram.Entry.e));
       Gramext.Stoken ("", "(");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", ")");
       Gramext.Snterm (Gram.Entry.obj (by_tactic : 'by_tactic Gram.Entry.e))],
      Gramext.action
        (fun (tac : 'by_tactic) _ (c : 'lconstr) _ (lid : 'identref) _ _ _
             (loc : Ploc.t) ->
           (let {CAst.loc = loc; v = id} = lid in
            TacAtom
              ((@@) (Loc.tag ?loc)
                 (TacAssert
                    (true, true, Some tac,
                     Some
                       ((@@) (CAst.make ?loc)
                          (IntroNaming (IntroIdentifier id))),
                     c))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "assert");
       Gramext.Snterm
         (Gram.Entry.obj
            (test_lpar_id_colon : 'test_lpar_id_colon Gram.Entry.e));
       Gramext.Stoken ("", "(");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", ")");
       Gramext.Snterm (Gram.Entry.obj (by_tactic : 'by_tactic Gram.Entry.e))],
      Gramext.action
        (fun (tac : 'by_tactic) _ (c : 'lconstr) _ (lid : 'identref) _ _ _
             (loc : Ploc.t) ->
           (let {CAst.loc = loc; v = id} = lid in
            TacAtom
              ((@@) (Loc.tag ?loc)
                 (TacAssert
                    (false, true, Some tac,
                     Some
                       ((@@) (CAst.make ?loc)
                          (IntroNaming (IntroIdentifier id))),
                     c))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "eassert");
       Gramext.Snterm
         (Gram.Entry.obj
            (test_lpar_id_coloneq : 'test_lpar_id_coloneq Gram.Entry.e));
       Gramext.Stoken ("", "(");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (c : 'lconstr) _ (lid : 'identref) _ _ _ (loc : Ploc.t) ->
           (let {CAst.loc = loc; v = id} = lid in
            TacAtom
              ((@@) (Loc.tag ?loc)
                 (TacAssert
                    (true, true, None,
                     Some
                       ((@@) (CAst.make ?loc)
                          (IntroNaming (IntroIdentifier id))),
                     c))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "assert");
       Gramext.Snterm
         (Gram.Entry.obj
            (test_lpar_id_coloneq : 'test_lpar_id_coloneq Gram.Entry.e));
       Gramext.Stoken ("", "(");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (c : 'lconstr) _ (lid : 'identref) _ _ _ (loc : Ploc.t) ->
           (let {CAst.loc = loc; v = id} = lid in
            TacAtom
              ((@@) (Loc.tag ?loc)
                 (TacAssert
                    (false, true, None,
                     Some
                       ((@@) (CAst.make ?loc)
                          (IntroNaming (IntroIdentifier id))),
                     c))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "eremember");
       Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (as_name : 'as_name Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (eqn_ipat : 'eqn_ipat Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (clause_dft_all : 'clause_dft_all Gram.Entry.e))],
      Gramext.action
        (fun (p : 'clause_dft_all) (e : 'eqn_ipat) (na : 'as_name)
             (c : 'constr) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacLetTac (true, na, c, p, false, e))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "remember");
       Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (as_name : 'as_name Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (eqn_ipat : 'eqn_ipat Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (clause_dft_all : 'clause_dft_all Gram.Entry.e))],
      Gramext.action
        (fun (p : 'clause_dft_all) (e : 'eqn_ipat) (na : 'as_name)
             (c : 'constr) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacLetTac (false, na, c, p, false, e))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "eset");
       Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (as_name : 'as_name Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj
            (clause_dft_concl : 'clause_dft_concl Gram.Entry.e))],
      Gramext.action
        (fun (p : 'clause_dft_concl) (na : 'as_name) (c : 'constr) _
             (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacLetTac (true, na, c, p, true, None))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "eset");
       Gramext.Snterm
         (Gram.Entry.obj
            (bindings_with_parameters :
             'bindings_with_parameters Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj
            (clause_dft_concl : 'clause_dft_concl Gram.Entry.e))],
      Gramext.action
        (fun (p : 'clause_dft_concl) (id, c : 'bindings_with_parameters) _
             (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacLetTac (true, Names.Name id, c, p, true, None))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "set");
       Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (as_name : 'as_name Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj
            (clause_dft_concl : 'clause_dft_concl Gram.Entry.e))],
      Gramext.action
        (fun (p : 'clause_dft_concl) (na : 'as_name) (c : 'constr) _
             (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacLetTac (false, na, c, p, true, None))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "set");
       Gramext.Snterm
         (Gram.Entry.obj
            (bindings_with_parameters :
             'bindings_with_parameters Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj
            (clause_dft_concl : 'clause_dft_concl Gram.Entry.e))],
      Gramext.action
        (fun (p : 'clause_dft_concl) (id, c : 'bindings_with_parameters) _
             (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacLetTac (false, Names.Name.Name id, c, p, true, None))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "epose");
       Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (as_name : 'as_name Gram.Entry.e))],
      Gramext.action
        (fun (na : 'as_name) (b : 'constr) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacLetTac (true, na, b, Locusops.nowhere, true, None))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "epose");
       Gramext.Snterm
         (Gram.Entry.obj
            (bindings_with_parameters :
             'bindings_with_parameters Gram.Entry.e))],
      Gramext.action
        (fun (id, b : 'bindings_with_parameters) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacLetTac
                    (true, Names.Name id, b, Locusops.nowhere, true, None))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "pose");
       Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (as_name : 'as_name Gram.Entry.e))],
      Gramext.action
        (fun (na : 'as_name) (b : 'constr) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacLetTac (false, na, b, Locusops.nowhere, true, None))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "pose");
       Gramext.Snterm
         (Gram.Entry.obj
            (bindings_with_parameters :
             'bindings_with_parameters Gram.Entry.e))],
      Gramext.action
        (fun (id, b : 'bindings_with_parameters) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacLetTac
                    (false, Names.Name.Name id, b, Locusops.nowhere, true,
                     None))) :
            'simple_tactic));
      [Gramext.Stoken ("", "cofix");
       Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e));
       Gramext.Stoken ("", "with");
       Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (cofixdecl : 'cofixdecl Gram.Entry.e)))],
      Gramext.action
        (fun (fd : 'cofixdecl list) _ (id : 'ident) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacMutualCofix (id, List.map mk_cofix_tac fd))) :
            'simple_tactic));
      [Gramext.Stoken ("", "fix");
       Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e));
       Gramext.Stoken ("", "with");
       Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (fixdecl : 'fixdecl Gram.Entry.e)))],
      Gramext.action
        (fun (fd : 'fixdecl list) _ (n : 'natural) (id : 'ident) _
             (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacMutualFix (id, n, List.map mk_fix_tac fd))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "ecase");
       Gramext.Snterm
         (Gram.Entry.obj
            (induction_clause_list : 'induction_clause_list Gram.Entry.e))],
      Gramext.action
        (fun (icl : 'induction_clause_list) _ (loc : Ploc.t) ->
           (TacAtom ((@@) (Loc.tag ~loc:((!@) loc)) (mkTacCase true icl)) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "case");
       Gramext.Snterm
         (Gram.Entry.obj
            (induction_clause_list : 'induction_clause_list Gram.Entry.e))],
      Gramext.action
        (fun (icl : 'induction_clause_list) _ (loc : Ploc.t) ->
           (TacAtom ((@@) (Loc.tag ~loc:((!@) loc)) (mkTacCase false icl)) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "eelim");
       Gramext.Snterm
         (Gram.Entry.obj
            (constr_with_bindings_arg :
             'constr_with_bindings_arg Gram.Entry.e));
       Gramext.Sopt
         (Gramext.Snterm
            (Gram.Entry.obj (eliminator : 'eliminator Gram.Entry.e)))],
      Gramext.action
        (fun (el : 'eliminator option) (cl : 'constr_with_bindings_arg) _
             (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc)) (TacElim (true, cl, el))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "elim");
       Gramext.Snterm
         (Gram.Entry.obj
            (constr_with_bindings_arg :
             'constr_with_bindings_arg Gram.Entry.e));
       Gramext.Sopt
         (Gramext.Snterm
            (Gram.Entry.obj (eliminator : 'eliminator Gram.Entry.e)))],
      Gramext.action
        (fun (el : 'eliminator option) (cl : 'constr_with_bindings_arg) _
             (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc)) (TacElim (false, cl, el))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "simple"); Gramext.Stoken ("IDENT", "eapply");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj
               (constr_with_bindings_arg :
                'constr_with_bindings_arg Gram.Entry.e)),
          Gramext.Stoken ("", ","), false);
       Gramext.Snterm (Gram.Entry.obj (in_hyp_as : 'in_hyp_as Gram.Entry.e))],
      Gramext.action
        (fun (inhyp : 'in_hyp_as) (cl : 'constr_with_bindings_arg list) _ _
             (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacApply (false, true, cl, inhyp))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "simple"); Gramext.Stoken ("IDENT", "apply");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj
               (constr_with_bindings_arg :
                'constr_with_bindings_arg Gram.Entry.e)),
          Gramext.Stoken ("", ","), false);
       Gramext.Snterm (Gram.Entry.obj (in_hyp_as : 'in_hyp_as Gram.Entry.e))],
      Gramext.action
        (fun (inhyp : 'in_hyp_as) (cl : 'constr_with_bindings_arg list) _ _
             (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacApply (false, false, cl, inhyp))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "eapply");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj
               (constr_with_bindings_arg :
                'constr_with_bindings_arg Gram.Entry.e)),
          Gramext.Stoken ("", ","), false);
       Gramext.Snterm (Gram.Entry.obj (in_hyp_as : 'in_hyp_as Gram.Entry.e))],
      Gramext.action
        (fun (inhyp : 'in_hyp_as) (cl : 'constr_with_bindings_arg list) _
             (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacApply (true, true, cl, inhyp))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "apply");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj
               (constr_with_bindings_arg :
                'constr_with_bindings_arg Gram.Entry.e)),
          Gramext.Stoken ("", ","), false);
       Gramext.Snterm (Gram.Entry.obj (in_hyp_as : 'in_hyp_as Gram.Entry.e))],
      Gramext.action
        (fun (inhyp : 'in_hyp_as) (cl : 'constr_with_bindings_arg list) _
             (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacApply (true, false, cl, inhyp))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "eintros");
       Gramext.Snterm
         (Gram.Entry.obj
            (ne_intropatterns : 'ne_intropatterns Gram.Entry.e))],
      Gramext.action
        (fun (pl : 'ne_intropatterns) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc)) (TacIntroPattern (true, pl))) :
            'simple_tactic));
      [Gramext.Stoken ("IDENT", "intros")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc))
                 (TacIntroPattern
                    (false,
                     [(@@) (CAst.make ~loc:((!@) loc))
                        (IntroForthcoming false)]))) :
            'simple_tactic));
      [(* Basic tactics *)
       Gramext.
       Stoken
         ("IDENT", "intros");
       Gramext.Snterm
         (Gram.Entry.obj
            (ne_intropatterns : 'ne_intropatterns Gram.Entry.e))],
      Gramext.action
        (fun (pl : 'ne_intropatterns) _ (loc : Ploc.t) ->
           (TacAtom
              ((@@) (Loc.tag ~loc:((!@) loc)) (TacIntroPattern (false, pl))) :
            'simple_tactic))]]
