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
open Libnames
open Constrexpr
open Constrexpr_ops
open Util
open Tok
open Misctypes
open Decl_kinds

open Pcoq
open Pcoq.Prim
open Pcoq.Constr

(* TODO: avoid this redefinition without an extra dep to Notation_ops *)
let ldots_var = Id.of_string ".."

let constr_kw =
  ["forall"; "fun"; "match"; "fix"; "cofix"; "with"; "in"; "for"; "end"; "as";
   "let"; "if"; "then"; "else"; "return"; "Prop"; "Set"; "Type"; ".("; "_";
   ".."; "`{"; "`("; "{|"; "|}"]

let _ = List.iter CLexer.add_keyword constr_kw

let mk_cast =
  function
    c, (_, None) -> c
  | c, (_, Some ty) ->
      let loc = Loc.merge_opt (constr_loc c) (constr_loc ty) in
      (@@) (CAst.make ?loc) (CCast (c, CastConv ty))

let binder_of_name expl {CAst.loc = loc; v = na} =
  CLocalAssum
    ([CAst.make ?loc na], Default expl,
     (@@) (CAst.make ?loc)
       (CHole (Some (Evar_kinds.BinderType na), IntroAnonymous, None)))

let binders_of_names l = List.map (binder_of_name Explicit) l

let mk_fixb (id, bl, ann, body, (loc, tyc)) : fix_expr =
  let ty =
    match tyc with
      Some ty -> ty
    | None -> (@@) CAst.make (CHole (None, IntroAnonymous, None))
  in
  id, ann, bl, ty, body

let mk_cofixb (id, bl, ann, body, (loc, tyc)) : cofix_expr =
  let _ =
    Option.map
      (fun {CAst.loc = aloc} ->
         CErrors.user_err ?loc:aloc ~hdr:"Constr:mk_cofixb"
           (Pp.str "Annotation forbidden in cofix expression."))
      (fst ann)
  in
  let ty =
    match tyc with
      Some ty -> ty
    | None -> (@@) CAst.make (CHole (None, IntroAnonymous, None))
  in
  id, bl, ty, body

let mk_fix (loc, kw, id, dcls) =
  if kw then
    let fb : fix_expr list = List.map mk_fixb dcls in
    (@@) (CAst.make ~loc) (CFix (id, fb))
  else
    let fb : cofix_expr list = List.map mk_cofixb dcls in
    (@@) (CAst.make ~loc) (CCoFix (id, fb))

let mk_single_fix (loc, kw, dcl) =
  let (id, _, _, _, _) = dcl in mk_fix (loc, kw, id, [dcl])

let err () = raise Stream.Failure

(* Hack to parse "(x:=t)" as an explicit argument without conflicts with the *)
(* admissible notation "(x t)" *)
let lpar_id_coloneq =
  Gram.Entry.of_parser "test_lpar_id_coloneq"
    (fun strm ->
       match stream_nth 0 strm with
         KEYWORD "(" ->
           begin match stream_nth 1 strm with
             IDENT s ->
               begin match stream_nth 2 strm with
                 KEYWORD ":=" -> stream_njunk 3 strm; Names.Id.of_string s
               | _ -> err ()
               end
           | _ -> err ()
           end
       | _ -> err ())

let impl_ident_head =
  Gram.Entry.of_parser "impl_ident_head"
    (fun strm ->
       match stream_nth 0 strm with
         KEYWORD "{" ->
           begin match stream_nth 1 strm with
             IDENT ("wf" | "struct" | "measure") -> err ()
           | IDENT s -> stream_njunk 2 strm; Names.Id.of_string s
           | _ -> err ()
           end
       | _ -> err ())

let name_colon =
  Gram.Entry.of_parser "name_colon"
    (fun strm ->
       match stream_nth 0 strm with
         IDENT s ->
           begin match stream_nth 1 strm with
             KEYWORD ":" -> stream_njunk 2 strm; Name (Names.Id.of_string s)
           | _ -> err ()
           end
       | KEYWORD "_" ->
           begin match stream_nth 1 strm with
             KEYWORD ":" -> stream_njunk 2 strm; Anonymous
           | _ -> err ()
           end
       | _ -> err ())

let aliasvar =
  function
    {CAst.v = CPatAlias (_, na)} -> Some na
  | _ -> None

let _ =
  let _ = (binder_constr : 'binder_constr Gram.Entry.e)
  and _ = (lconstr : 'lconstr Gram.Entry.e)
  and _ = (constr : 'constr Gram.Entry.e)
  and _ = (operconstr : 'operconstr Gram.Entry.e)
  and _ = (universe_level : 'universe_level Gram.Entry.e)
  and _ = (sort : 'sort Gram.Entry.e)
  and _ = (sort_family : 'sort_family Gram.Entry.e)
  and _ = (global : 'global Gram.Entry.e)
  and _ = (constr_pattern : 'constr_pattern Gram.Entry.e)
  and _ = (lconstr_pattern : 'lconstr_pattern Gram.Entry.e)
  and _ = (Constr.ident : 'Constr__ident Gram.Entry.e)
  and _ = (closed_binder : 'closed_binder Gram.Entry.e)
  and _ = (open_binders : 'open_binders Gram.Entry.e)
  and _ = (binder : 'binder Gram.Entry.e)
  and _ = (binders : 'binders Gram.Entry.e)
  and _ = (binders_fixannot : 'binders_fixannot Gram.Entry.e)
  and _ = (record_declaration : 'record_declaration Gram.Entry.e)
  and _ = (typeclass_constraint : 'typeclass_constraint Gram.Entry.e)
  and _ = (pattern : 'pattern Gram.Entry.e)
  and _ = (appl_arg : 'appl_arg Gram.Entry.e) in
  let grammar_entry_create = Gram.Entry.create in
  let universe_expr : 'universe_expr Gram.Entry.e =
    grammar_entry_create "universe_expr"
  and universe : 'universe Gram.Entry.e = grammar_entry_create "universe"
  and record_fields : 'record_fields Gram.Entry.e =
    grammar_entry_create "record_fields"
  and record_field_declaration : 'record_field_declaration Gram.Entry.e =
    grammar_entry_create "record_field_declaration"
  and atomic_constr : 'atomic_constr Gram.Entry.e =
    grammar_entry_create "atomic_constr"
  and inst : 'inst Gram.Entry.e = grammar_entry_create "inst"
  and evar_instance : 'evar_instance Gram.Entry.e =
    grammar_entry_create "evar_instance"
  and instance : 'instance Gram.Entry.e = grammar_entry_create "instance"
  and fix_constr : 'fix_constr Gram.Entry.e =
    grammar_entry_create "fix_constr"
  and single_fix : 'single_fix Gram.Entry.e =
    grammar_entry_create "single_fix"
  and fix_kw : 'fix_kw Gram.Entry.e = grammar_entry_create "fix_kw"
  and fix_decl : 'fix_decl Gram.Entry.e = grammar_entry_create "fix_decl"
  and match_constr : 'match_constr Gram.Entry.e =
    grammar_entry_create "match_constr"
  and case_item : 'case_item Gram.Entry.e = grammar_entry_create "case_item"
  and case_type : 'case_type Gram.Entry.e = grammar_entry_create "case_type"
  and return_type : 'return_type Gram.Entry.e =
    grammar_entry_create "return_type"
  and branches : 'branches Gram.Entry.e = grammar_entry_create "branches"
  and mult_pattern : 'mult_pattern Gram.Entry.e =
    grammar_entry_create "mult_pattern"
  and eqn : 'eqn Gram.Entry.e = grammar_entry_create "eqn"
  and record_pattern : 'record_pattern Gram.Entry.e =
    grammar_entry_create "record_pattern"
  and record_patterns : 'record_patterns Gram.Entry.e =
    grammar_entry_create "record_patterns"
  and impl_ident_tail : 'impl_ident_tail Gram.Entry.e =
    grammar_entry_create "impl_ident_tail"
  and fixannot : 'fixannot Gram.Entry.e = grammar_entry_create "fixannot"
  and impl_name_head : 'impl_name_head Gram.Entry.e =
    grammar_entry_create "impl_name_head"
  and type_cstr : 'type_cstr Gram.Entry.e =
    grammar_entry_create "type_cstr"
  in
  Gram.extend (Constr.ident : 'Constr__ident Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (Prim.ident : 'Prim__ident Gram.Entry.e))],
      Gramext.action
        (fun (id : 'Prim__ident) (loc : Ploc.t) -> (id : 'Constr__ident))]];
  Gram.extend (Prim.name : 'Prim__name Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "_")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           (CAst.make ~loc:((!@) loc) Anonymous : 'Prim__name))]];
  Gram.extend (global : 'global Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (Prim.reference : 'Prim__reference Gram.Entry.e))],
      Gramext.action
        (fun (r : 'Prim__reference) (loc : Ploc.t) -> (r : 'global))]];
  Gram.extend (constr_pattern : 'constr_pattern Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'constr) (loc : Ploc.t) -> (c : 'constr_pattern))]];
  Gram.extend (lconstr_pattern : 'lconstr_pattern Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'lconstr) (loc : Ploc.t) -> (c : 'lconstr_pattern))]];
  Gram.extend (sort : 'sort Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "Type"); Gramext.Stoken ("", "@{");
       Gramext.Snterm (Gram.Entry.obj (universe : 'universe Gram.Entry.e));
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (u : 'universe) _ _ (loc : Ploc.t) -> (GType u : 'sort));
      [Gramext.Stoken ("", "Type")],
      Gramext.action (fun _ (loc : Ploc.t) -> (GType [] : 'sort));
      [Gramext.Stoken ("", "Prop")],
      Gramext.action (fun _ (loc : Ploc.t) -> (GProp : 'sort));
      [Gramext.Stoken ("", "Set")],
      Gramext.action (fun _ (loc : Ploc.t) -> (GSet : 'sort))]];
  Gram.extend (sort_family : 'sort_family Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "Type")],
      Gramext.action (fun _ (loc : Ploc.t) -> (Sorts.InType : 'sort_family));
      [Gramext.Stoken ("", "Prop")],
      Gramext.action (fun _ (loc : Ploc.t) -> (Sorts.InProp : 'sort_family));
      [Gramext.Stoken ("", "Set")],
      Gramext.action (fun _ (loc : Ploc.t) -> (Sorts.InSet : 'sort_family))]];
  Gram.extend (universe_expr : 'universe_expr Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "_")],
      Gramext.action (fun _ (loc : Ploc.t) -> (None : 'universe_expr));
      [Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e))],
      Gramext.action
        (fun (id : 'global) (loc : Ploc.t) ->
           (Some (id, 0) : 'universe_expr));
      [Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e));
       Gramext.Stoken ("", "+");
       Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e))],
      Gramext.action
        (fun (n : 'natural) _ (id : 'global) (loc : Ploc.t) ->
           (Some (id, n) : 'universe_expr))]];
  Gram.extend (universe : 'universe Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (universe_expr : 'universe_expr Gram.Entry.e))],
      Gramext.action
        (fun (u : 'universe_expr) (loc : Ploc.t) -> ([u] : 'universe));
      [Gramext.Stoken ("IDENT", "max"); Gramext.Stoken ("", "(");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj (universe_expr : 'universe_expr Gram.Entry.e)),
          Gramext.Stoken ("", ","), false);
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (ids : 'universe_expr list) _ _ (loc : Ploc.t) ->
           (ids : 'universe))]];
  Gram.extend (lconstr : 'lconstr Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200")],
      Gramext.action
        (fun (c : 'operconstr) (loc : Ploc.t) -> (c : 'lconstr))]];
  Gram.extend (constr : 'constr Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "@");
       Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (instance : 'instance Gram.Entry.e))],
      Gramext.action
        (fun (i : 'instance) (f : 'global) _ (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CAppExpl ((None, f, i), [])) :
            'constr));
      [Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "8")],
      Gramext.action
        (fun (c : 'operconstr) (loc : Ploc.t) -> (c : 'constr))]];
  Gram.extend (operconstr : 'operconstr Gram.Entry.e) None
    [Some "200", Some Gramext.RightA,
     [[Gramext.Snterm
         (Gram.Entry.obj (binder_constr : 'binder_constr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'binder_constr) (loc : Ploc.t) -> (c : 'operconstr))];
     Some "100", Some Gramext.RightA,
     [[Gramext.Sself; Gramext.Stoken ("", ":>")],
      Gramext.action
        (fun _ (c1 : 'operconstr) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CCast (c1, CastCoerce)) :
            'operconstr));
      [Gramext.Sself; Gramext.Stoken ("", ":"); Gramext.Sself],
      Gramext.action
        (fun (c2 : 'operconstr) _ (c1 : 'operconstr) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CCast (c1, CastConv c2)) :
            'operconstr));
      [Gramext.Sself; Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Gram.Entry.obj (binder_constr : 'binder_constr Gram.Entry.e))],
      Gramext.action
        (fun (c2 : 'binder_constr) _ (c1 : 'operconstr) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CCast (c1, CastConv c2)) :
            'operconstr));
      (*
      [Gramext.Sself; Gramext.Stoken ("", "<<:"); Gramext.Sself],
      Gramext.action
        (fun (c2 : 'operconstr) _ (c1 : 'operconstr) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CCast (c1, CastNative c2)) :
            'operconstr));
      [Gramext.Sself; Gramext.Stoken ("", "<<:");
       Gramext.Snterm
         (Gram.Entry.obj (binder_constr : 'binder_constr Gram.Entry.e))],
      Gramext.action
        (fun (c2 : 'binder_constr) _ (c1 : 'operconstr) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CCast (c1, CastNative c2)) :
            'operconstr));
      [Gramext.Sself; Gramext.Stoken ("", "<:"); Gramext.Sself],
      Gramext.action
        (fun (c2 : 'operconstr) _ (c1 : 'operconstr) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CCast (c1, CastVM c2)) :
            'operconstr));
      [Gramext.Sself; Gramext.Stoken ("", "<:");
       Gramext.Snterm
         (Gram.Entry.obj (binder_constr : 'binder_constr Gram.Entry.e))],
      Gramext.action
        (fun (c2 : 'binder_constr) _ (c1 : 'operconstr) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CCast (c1, CastVM c2)) :
            'operconstr)) *)];
     Some "99", Some Gramext.RightA, []; Some "90", Some Gramext.RightA, [];
     Some "10", Some Gramext.LeftA,
     [[Gramext.Stoken ("", "@");
       Gramext.Snterm
         (Gram.Entry.obj (pattern_identref : 'pattern_identref Gram.Entry.e));
       Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (identref : 'identref Gram.Entry.e)))],
      Gramext.action
        (fun (args : 'identref list) (lid : 'pattern_identref) _
             (loc : Ploc.t) ->
           (let {CAst.loc = locid; v = id} = lid in
            let args =
              List.map
                (fun x ->
                   (@@) CAst.make
                     (CRef
                        ((@@) (CAst.make ?loc:x.CAst.loc) (Ident x.CAst.v),
                         None)),
                   None)
                args
            in
            (@@) (CAst.make ~loc:((!@) loc))
              (CApp
                 ((None, (@@) (CAst.make ?loc:locid) (CPatVar id)), args)) :
            'operconstr));
      [Gramext.Stoken ("", "@");
       Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (instance : 'instance Gram.Entry.e));
       Gramext.Slist0 Gramext.Snext],
      Gramext.action
        (fun (args : 'operconstr list) (i : 'instance) (f : 'global) _
             (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CAppExpl ((None, f, i), args)) :
            'operconstr));
      [Gramext.Sself;
       Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (appl_arg : 'appl_arg Gram.Entry.e)))],
      Gramext.action
        (fun (args : 'appl_arg list) (f : 'operconstr) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CApp ((None, f), args)) :
            'operconstr))];
     Some "9", None,
     [[Gramext.Stoken ("", "..");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "0");
       Gramext.Stoken ("", "..")],
      Gramext.action
        (fun _ (c : 'operconstr) _ (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc))
              (CAppExpl
                 ((None, (@@) (CAst.make ~loc:((!@) loc)) (Ident ldots_var),
                   None),
                  [c])) :
            'operconstr))];
     Some "8", None, [];
     Some "1", Some Gramext.LeftA,
     [[Gramext.Sself; Gramext.Stoken ("", "%"); Gramext.Stoken ("IDENT", "")],
      Gramext.action
        (fun (key : string) _ (c : 'operconstr) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CDelimiters (key, c)) :
            'operconstr));
      [Gramext.Sself; Gramext.Stoken ("", ".("); Gramext.Stoken ("", "@");
       Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e));
       Gramext.Slist0
         (Gramext.Snterml
            (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "9"));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (args : 'operconstr list) (f : 'global) _ _ (c : 'operconstr)
             (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc))
              (CAppExpl
                 ((Some (List.length args + 1), f, None), args @ [c])) :
            'operconstr));
      [Gramext.Sself; Gramext.Stoken ("", ".(");
       Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e));
       Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj (appl_arg : 'appl_arg Gram.Entry.e)));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (args : 'appl_arg list) (f : 'global) _ (c : 'operconstr)
             (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc))
              (CApp
                 ((Some (List.length args + 1),
                   (@@) CAst.make (CRef (f, None))),
                  args @ [c, None])) :
            'operconstr))];
     Some "0", None,
     [[Gramext.Stoken ("", "`(");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200");
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (c : 'operconstr) _ (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc))
              (CGeneralization (Explicit, None, c)) :
            'operconstr));
      [Gramext.Stoken ("", "`{");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200");
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (c : 'operconstr) _ (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc))
              (CGeneralization (Implicit, None, c)) :
            'operconstr));
      [Gramext.Stoken ("", "{");
       Gramext.Snterm
         (Gram.Entry.obj (binder_constr : 'binder_constr Gram.Entry.e));
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (c : 'binder_constr) _ (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc))
              (CNotation ("{ _ }", ([c], [], [], []))) :
            'operconstr));
      [Gramext.Stoken ("", "{|");
       Gramext.Snterm
         (Gram.Entry.obj
            (record_declaration : 'record_declaration Gram.Entry.e));
       Gramext.Stoken ("", "|}")],
      Gramext.action
        (fun _ (c : 'record_declaration) _ (loc : Ploc.t) ->
           (c : 'operconstr));
      [Gramext.Stoken ("", "(");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200");
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (c : 'operconstr) _ (loc : Ploc.t) ->
           (match c.CAst.v with
              CPrim (Numeral (n, true)) ->
                (@@) (CAst.make ~loc:((!@) loc))
                  (CNotation ("( _ )", ([c], [], [], [])))
            | _ -> c :
            'operconstr));
      [Gramext.Snterm
         (Gram.Entry.obj (match_constr : 'match_constr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'match_constr) (loc : Ploc.t) -> (c : 'operconstr));
      [Gramext.Snterm
         (Gram.Entry.obj (atomic_constr : 'atomic_constr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'atomic_constr) (loc : Ploc.t) -> (c : 'operconstr))]];
  Gram.extend (record_declaration : 'record_declaration Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (record_fields : 'record_fields Gram.Entry.e))],
      Gramext.action
        (fun (fs : 'record_fields) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CRecord fs) :
            'record_declaration))]];
  Gram.extend (record_fields : 'record_fields Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> ([] : 'record_fields));
      [Gramext.Snterm
         (Gram.Entry.obj
            (record_field_declaration :
             'record_field_declaration Gram.Entry.e))],
      Gramext.action
        (fun (f : 'record_field_declaration) (loc : Ploc.t) ->
           ([f] : 'record_fields));
      [Gramext.Snterm
         (Gram.Entry.obj
            (record_field_declaration :
             'record_field_declaration Gram.Entry.e));
       Gramext.Stoken ("", ";"); Gramext.Sself],
      Gramext.action
        (fun (fs : 'record_fields) _ (f : 'record_field_declaration)
             (loc : Ploc.t) ->
           (f :: fs : 'record_fields))]];
  Gram.extend
    (record_field_declaration : 'record_field_declaration Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (binders : 'binders Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'lconstr) _ (bl : 'binders) (id : 'global) (loc : Ploc.t) ->
           (id, mkCLambdaN ~loc:((!@) loc) bl c :
            'record_field_declaration))]];
  Gram.extend (binder_constr : 'binder_constr Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (fix_constr : 'fix_constr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'fix_constr) (loc : Ploc.t) -> (c : 'binder_constr));
      [Gramext.Stoken ("", "if");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200");
       Gramext.Snterm
         (Gram.Entry.obj (return_type : 'return_type Gram.Entry.e));
       Gramext.Stoken ("", "then");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200");
       Gramext.Stoken ("", "else");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200")],
      Gramext.action
        (fun (b2 : 'operconstr) _ (b1 : 'operconstr) _ (po : 'return_type)
             (c : 'operconstr) _ (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CIf (c, po, b1, b2)) :
            'binder_constr));
      [Gramext.Stoken ("", "let"); Gramext.Stoken ("", "'");
       Gramext.Snterm (Gram.Entry.obj (pattern : 'pattern Gram.Entry.e));
       Gramext.Stoken ("", "in");
       Gramext.Snterml
         (Gram.Entry.obj (pattern : 'pattern Gram.Entry.e), "200");
       Gramext.Stoken ("", ":=");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200");
       Gramext.Snterm (Gram.Entry.obj (case_type : 'case_type Gram.Entry.e));
       Gramext.Stoken ("", "in");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200")],
      Gramext.action
        (fun (c2 : 'operconstr) _ (rt : 'case_type) (c1 : 'operconstr) _
             (t : 'pattern) _ (p : 'pattern) _ _ (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc))
              (CCases
                 (LetPatternStyle, Some rt, [c1, aliasvar p, Some t],
                  [CAst.make ~loc:((!@) loc) ([[p]], c2)])) :
            'binder_constr));
      [Gramext.Stoken ("", "let"); Gramext.Stoken ("", "'");
       Gramext.Snterm (Gram.Entry.obj (pattern : 'pattern Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200");
       Gramext.Snterm (Gram.Entry.obj (case_type : 'case_type Gram.Entry.e));
       Gramext.Stoken ("", "in");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200")],
      Gramext.action
        (fun (c2 : 'operconstr) _ (rt : 'case_type) (c1 : 'operconstr) _
             (p : 'pattern) _ _ (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc))
              (CCases
                 (LetPatternStyle, Some rt, [c1, aliasvar p, None],
                  [CAst.make ~loc:((!@) loc) ([[p]], c2)])) :
            'binder_constr));
      [Gramext.Stoken ("", "let"); Gramext.Stoken ("", "'");
       Gramext.Snterm (Gram.Entry.obj (pattern : 'pattern Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200");
       Gramext.Stoken ("", "in");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200")],
      Gramext.action
        (fun (c2 : 'operconstr) _ (c1 : 'operconstr) _ (p : 'pattern) _ _
             (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc))
              (CCases
                 (LetPatternStyle, None, [c1, None, None],
                  [CAst.make ~loc:((!@) loc) ([[p]], c2)])) :
            'binder_constr));
      [Gramext.Stoken ("", "let");
       Gramext.srules
         [[Gramext.Stoken ("", "()")],
          Gramext.action (fun _ (loc : Ploc.t) -> ([] : 'e__1));
          [Gramext.Stoken ("", "(");
           Gramext.Slist0sep
             (Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e)),
              Gramext.Stoken ("", ","), false);
           Gramext.Stoken ("", ")")],
          Gramext.action
            (fun _ (l : 'name list) _ (loc : Ploc.t) -> (l : 'e__1))];
       Gramext.Snterm
         (Gram.Entry.obj (return_type : 'return_type Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200");
       Gramext.Stoken ("", "in");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200")],
      Gramext.action
        (fun (c2 : 'operconstr) _ (c1 : 'operconstr) _ (po : 'return_type)
             (lb : 'e__1) _ (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CLetTuple (lb, po, c1, c2)) :
            'binder_constr));
      [Gramext.Stoken ("", "let");
       Gramext.Snterm
         (Gram.Entry.obj (single_fix : 'single_fix Gram.Entry.e));
       Gramext.Stoken ("", "in");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200")],
      Gramext.action
        (fun (c : 'operconstr) _ (fx : 'single_fix) _ (loc : Ploc.t) ->
           (let fixp = mk_single_fix fx in
            let {CAst.loc = li; v = id} =
              match fixp.CAst.v with
                CFix (id, _) -> id
              | CCoFix (id, _) -> id
              | _ -> assert false
            in
            (@@) (CAst.make ~loc:((!@) loc))
              (CLetIn ((@@) (CAst.make ?loc:li) (Name id), fixp, None, c)) :
            'binder_constr));
      [Gramext.Stoken ("", "let");
       Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (binders : 'binders Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (type_cstr : 'type_cstr Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200");
       Gramext.Stoken ("", "in");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200")],
      Gramext.action
        (fun (c2 : 'operconstr) _ (c1 : 'operconstr) _ (ty : 'type_cstr)
             (bl : 'binders) (id : 'name) _ (loc : Ploc.t) ->
           (let (ty, c1) =
              match ty, c1 with
                (_, None), {CAst.v = CCast (c, CastConv t)} ->
                  (@@) (Loc.tag ?loc:(constr_loc t)) (Some t), c
              | _, _ -> ty, c1
            in
            (@@) (CAst.make ~loc:((!@) loc))
              (CLetIn
                 (id, mkCLambdaN ?loc:(constr_loc c1) bl c1,
                  Option.map (mkCProdN ?loc:(fst ty) bl) (snd ty), c2)) :
            'binder_constr));
      [Gramext.Stoken ("", "fun");
       Gramext.Snterm
         (Gram.Entry.obj (open_binders : 'open_binders Gram.Entry.e));
       Gramext.Stoken ("", "=>");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200")],
      Gramext.action
        (fun (c : 'operconstr) _ (bl : 'open_binders) _ (loc : Ploc.t) ->
           (mkCLambdaN ~loc:((!@) loc) bl c : 'binder_constr));
      [Gramext.Stoken ("", "forall");
       Gramext.Snterm
         (Gram.Entry.obj (open_binders : 'open_binders Gram.Entry.e));
       Gramext.Stoken ("", ",");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200")],
      Gramext.action
        (fun (c : 'operconstr) _ (bl : 'open_binders) _ (loc : Ploc.t) ->
           (mkCProdN ~loc:((!@) loc) bl c : 'binder_constr))]];
  Gram.extend (appl_arg : 'appl_arg Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "9")],
      Gramext.action
        (fun (c : 'operconstr) (loc : Ploc.t) -> (c, None : 'appl_arg));
      [Gramext.Snterm
         (Gram.Entry.obj (lpar_id_coloneq : 'lpar_id_coloneq Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (c : 'lconstr) (id : 'lpar_id_coloneq) (loc : Ploc.t) ->
           (c, Some ((@@) (CAst.make ~loc:((!@) loc)) (ExplByName id)) :
            'appl_arg))]];
  Gram.extend (atomic_constr : 'atomic_constr Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (pattern_ident : 'pattern_ident Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (evar_instance : 'evar_instance Gram.Entry.e))],
      Gramext.action
        (fun (inst : 'evar_instance) (id : 'pattern_ident) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CEvar (id, inst)) :
            'atomic_constr));
      [Gramext.Stoken ("", "?"); Gramext.Stoken ("", "[");
       Gramext.Snterm
         (Gram.Entry.obj (pattern_ident : 'pattern_ident Gram.Entry.e));
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (id : 'pattern_ident) _ _ (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc))
              (CHole (None, IntroFresh id, None)) :
            'atomic_constr));
      [Gramext.Stoken ("", "?"); Gramext.Stoken ("", "[");
       Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e));
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (id : 'ident) _ _ (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc))
              (CHole (None, IntroIdentifier id, None)) :
            'atomic_constr));
      [Gramext.Stoken ("", "_")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc))
              (CHole (None, IntroAnonymous, None)) :
            'atomic_constr));
      [Gramext.Snterm (Gram.Entry.obj (string : 'string Gram.Entry.e))],
      Gramext.action
        (fun (s : 'string) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CPrim (String s)) :
            'atomic_constr));
      [Gramext.Stoken ("INT", "")],
      Gramext.action
        (fun (n : string) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CPrim (Numeral (n, true))) :
            'atomic_constr));
      [Gramext.Snterm (Gram.Entry.obj (sort : 'sort Gram.Entry.e))],
      Gramext.action
        (fun (s : 'sort) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CSort s) : 'atomic_constr));
      [Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (instance : 'instance Gram.Entry.e))],
      Gramext.action
        (fun (i : 'instance) (g : 'global) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CRef (g, i)) :
            'atomic_constr))]];
  Gram.extend (inst : 'inst Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'lconstr) _ (id : 'ident) (loc : Ploc.t) ->
           (id, c : 'inst))]];
  Gram.extend (evar_instance : 'evar_instance Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> ([] : 'evar_instance));
      [Gramext.Stoken ("", "@{");
       Gramext.Slist1sep
         (Gramext.Snterm (Gram.Entry.obj (inst : 'inst Gram.Entry.e)),
          Gramext.Stoken ("", ";"), false);
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (l : 'inst list) _ (loc : Ploc.t) -> (l : 'evar_instance))]];
  Gram.extend (instance : 'instance Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> (None : 'instance));
      [Gramext.Stoken ("", "@{");
       Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj (universe_level : 'universe_level Gram.Entry.e)));
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (l : 'universe_level list) _ (loc : Ploc.t) ->
           (Some l : 'instance))]];
  Gram.extend (universe_level : 'universe_level Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e))],
      Gramext.action
        (fun (id : 'global) (loc : Ploc.t) ->
           (GType (UNamed id) : 'universe_level));
      [Gramext.Stoken ("", "_")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (GType UAnonymous : 'universe_level));
      [Gramext.Stoken ("", "Type")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (GType UUnknown : 'universe_level));
      [Gramext.Stoken ("", "Prop")],
      Gramext.action (fun _ (loc : Ploc.t) -> (GProp : 'universe_level));
      [Gramext.Stoken ("", "Set")],
      Gramext.action (fun _ (loc : Ploc.t) -> (GSet : 'universe_level))]];
  Gram.extend (fix_constr : 'fix_constr Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (single_fix : 'single_fix Gram.Entry.e));
       Gramext.Stoken ("", "with");
       Gramext.Slist1sep
         (Gramext.Snterm (Gram.Entry.obj (fix_decl : 'fix_decl Gram.Entry.e)),
          Gramext.Stoken ("", "with"), false);
       Gramext.Stoken ("", "for");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e))],
      Gramext.action
        (fun (id : 'identref) _ (dcls : 'fix_decl list) _
             (_, kw, dcl1 : 'single_fix) (loc : Ploc.t) ->
           (mk_fix ((!@) loc, kw, id, dcl1 :: dcls) : 'fix_constr));
      [Gramext.Snterm
         (Gram.Entry.obj (single_fix : 'single_fix Gram.Entry.e))],
      Gramext.action
        (fun (fx1 : 'single_fix) (loc : Ploc.t) ->
           (mk_single_fix fx1 : 'fix_constr))]];
  Gram.extend (single_fix : 'single_fix Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (fix_kw : 'fix_kw Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (fix_decl : 'fix_decl Gram.Entry.e))],
      Gramext.action
        (fun (dcl : 'fix_decl) (kw : 'fix_kw) (loc : Ploc.t) ->
           ((!@) loc, kw, dcl : 'single_fix))]];
  Gram.extend (fix_kw : 'fix_kw Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "cofix")],
      Gramext.action (fun _ (loc : Ploc.t) -> (false : 'fix_kw));
      [Gramext.Stoken ("", "fix")],
      Gramext.action (fun _ (loc : Ploc.t) -> (true : 'fix_kw))]];
  Gram.extend (fix_decl : 'fix_decl Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (binders_fixannot : 'binders_fixannot Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (type_cstr : 'type_cstr Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200")],
      Gramext.action
        (fun (c : 'operconstr) _ (ty : 'type_cstr) (bl : 'binders_fixannot)
             (id : 'identref) (loc : Ploc.t) ->
           (id, fst bl, snd bl, c, ty : 'fix_decl))]];
  Gram.extend (match_constr : 'match_constr Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "match");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj (case_item : 'case_item Gram.Entry.e)),
          Gramext.Stoken ("", ","), false);
       Gramext.Sopt
         (Gramext.Snterm
            (Gram.Entry.obj (case_type : 'case_type Gram.Entry.e)));
       Gramext.Stoken ("", "with");
       Gramext.Snterm (Gram.Entry.obj (branches : 'branches Gram.Entry.e));
       Gramext.Stoken ("", "end")],
      Gramext.action
        (fun _ (br : 'branches) _ (ty : 'case_type option)
             (ci : 'case_item list) _ (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc))
              (CCases (RegularStyle, ty, ci, br)) :
            'match_constr))]];
  Gram.extend (case_item : 'case_item Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "100");
       Gramext.Sopt
         (Gramext.srules
            [[Gramext.Stoken ("", "as");
              Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e))],
             Gramext.action
               (fun (id : 'name) _ (loc : Ploc.t) -> (id : 'e__2))]);
       Gramext.Sopt
         (Gramext.srules
            [[Gramext.Stoken ("", "in");
              Gramext.Snterm
                (Gram.Entry.obj (pattern : 'pattern Gram.Entry.e))],
             Gramext.action
               (fun (t : 'pattern) _ (loc : Ploc.t) -> (t : 'e__3))])],
      Gramext.action
        (fun (ty : 'e__3 option) (ona : 'e__2 option) (c : 'operconstr)
             (loc : Ploc.t) ->
           (c, ona, ty : 'case_item))]];
  Gram.extend (case_type : 'case_type Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "return");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "100")],
      Gramext.action
        (fun (ty : 'operconstr) _ (loc : Ploc.t) -> (ty : 'case_type))]];
  Gram.extend (return_type : 'return_type Gram.Entry.e) None
    [None, None,
     [[Gramext.Sopt
         (Gramext.srules
            [[Gramext.Sopt
                (Gramext.srules
                   [[Gramext.Stoken ("", "as");
                     Gramext.Snterm
                       (Gram.Entry.obj (name : 'name Gram.Entry.e))],
                    Gramext.action
                      (fun (na : 'name) _ (loc : Ploc.t) -> (na : 'e__4))]);
              Gramext.Snterm
                (Gram.Entry.obj (case_type : 'case_type Gram.Entry.e))],
             Gramext.action
               (fun (ty : 'case_type) (na : 'e__4 option) (loc : Ploc.t) ->
                  (na, ty : 'e__5))])],
      Gramext.action
        (fun (a : 'e__5 option) (loc : Ploc.t) ->
           (match a with
              None -> None, None
            | Some (na, t) -> na, Some t :
            'return_type))]];
  Gram.extend (branches : 'branches Gram.Entry.e) None
    [None, None,
     [[Gramext.Sopt (Gramext.Stoken ("", "|"));
       Gramext.Slist0sep
         (Gramext.Snterm (Gram.Entry.obj (eqn : 'eqn Gram.Entry.e)),
          Gramext.Stoken ("", "|"), false)],
      Gramext.action
        (fun (br : 'eqn list) _ (loc : Ploc.t) -> (br : 'branches))]];
  Gram.extend (mult_pattern : 'mult_pattern Gram.Entry.e) None
    [None, None,
     [[Gramext.Slist1sep
         (Gramext.Snterml
            (Gram.Entry.obj (pattern : 'pattern Gram.Entry.e), "99"),
          Gramext.Stoken ("", ","), false)],
      Gramext.action
        (fun (pl : 'pattern list) (loc : Ploc.t) -> (pl : 'mult_pattern))]];
  Gram.extend (eqn : 'eqn Gram.Entry.e) None
    [None, None,
     [[Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj (mult_pattern : 'mult_pattern Gram.Entry.e)),
          Gramext.Stoken ("", "|"), false);
       Gramext.Stoken ("", "=>");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
      Gramext.action
        (fun (rhs : 'lconstr) _ (pll : 'mult_pattern list) (loc : Ploc.t) ->
           (CAst.make ~loc:((!@) loc) (pll, rhs) : 'eqn))]];
  Gram.extend (record_pattern : 'record_pattern Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm (Gram.Entry.obj (pattern : 'pattern Gram.Entry.e))],
      Gramext.action
        (fun (pat : 'pattern) _ (id : 'global) (loc : Ploc.t) ->
           (id, pat : 'record_pattern))]];
  Gram.extend (record_patterns : 'record_patterns Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> ([] : 'record_patterns));
      [Gramext.Snterm
         (Gram.Entry.obj (record_pattern : 'record_pattern Gram.Entry.e))],
      Gramext.action
        (fun (p : 'record_pattern) (loc : Ploc.t) ->
           ([p] : 'record_patterns));
      [Gramext.Snterm
         (Gram.Entry.obj (record_pattern : 'record_pattern Gram.Entry.e));
       Gramext.Stoken ("", ";")],
      Gramext.action
        (fun _ (p : 'record_pattern) (loc : Ploc.t) ->
           ([p] : 'record_patterns));
      [Gramext.Snterm
         (Gram.Entry.obj (record_pattern : 'record_pattern Gram.Entry.e));
       Gramext.Stoken ("", ";"); Gramext.Sself],
      Gramext.action
        (fun (ps : 'record_patterns) _ (p : 'record_pattern) (loc : Ploc.t) ->
           (p :: ps : 'record_patterns))]];
  Gram.extend (pattern : 'pattern Gram.Entry.e) None
    [Some "200", Some Gramext.RightA, [];
     Some "100", Some Gramext.RightA,
     [[Gramext.Sself; Gramext.Stoken ("", "|");
       Gramext.Slist1sep
         (Gramext.Snterm (Gram.Entry.obj (pattern : 'pattern Gram.Entry.e)),
          Gramext.Stoken ("", "|"), false)],
      Gramext.action
        (fun (pl : 'pattern list) _ (p : 'pattern) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CPatOr (p :: pl)) : 'pattern))];
     Some "99", Some Gramext.RightA, []; Some "90", Some Gramext.RightA, [];
     Some "10", Some Gramext.LeftA,
     [[Gramext.Stoken ("", "@");
       Gramext.Snterm
         (Gram.Entry.obj (Prim.reference : 'Prim__reference Gram.Entry.e));
       Gramext.Slist0 Gramext.Snext],
      Gramext.action
        (fun (lp : 'pattern list) (r : 'Prim__reference) _ (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CPatCstr (r, Some lp, [])) :
            'pattern));
      [Gramext.Sself; Gramext.Slist1 Gramext.Snext],
      Gramext.action
        (fun (lp : 'pattern list) (p : 'pattern) (loc : Ploc.t) ->
           (mkAppPattern ~loc:((!@) loc) p lp : 'pattern));
      [Gramext.Sself; Gramext.Stoken ("", "as");
       Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e))],
      Gramext.action
        (fun (na : 'name) _ (p : 'pattern) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CPatAlias (p, na)) :
            'pattern))];
     Some "1", Some Gramext.LeftA,
     [[Gramext.Sself; Gramext.Stoken ("", "%"); Gramext.Stoken ("IDENT", "")],
      Gramext.action
        (fun (key : string) _ (c : 'pattern) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CPatDelimiters (key, c)) :
            'pattern))];
     Some "0", None,
     [[Gramext.Snterm (Gram.Entry.obj (string : 'string Gram.Entry.e))],
      Gramext.action
        (fun (s : 'string) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CPatPrim (String s)) :
            'pattern));
      [Gramext.Stoken ("INT", "")],
      Gramext.action
        (fun (n : string) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CPatPrim (Numeral (n, true))) :
            'pattern));
      [Gramext.Stoken ("", "(");
       Gramext.Snterml
         (Gram.Entry.obj (pattern : 'pattern Gram.Entry.e), "200");
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (ty : 'lconstr) _ (p : 'pattern) _ (loc : Ploc.t) ->
           (let p =
              match p with
                {CAst.v = CPatPrim (Numeral (n, true))} ->
                  (@@) (CAst.make ~loc:((!@) loc))
                    (CPatNotation ("( _ )", ([p], []), []))
              | _ -> p
            in
            (@@) (CAst.make ~loc:((!@) loc)) (CPatCast (p, ty)) :
            'pattern));
      [Gramext.Stoken ("", "(");
       Gramext.Snterml
         (Gram.Entry.obj (pattern : 'pattern Gram.Entry.e), "200");
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (p : 'pattern) _ (loc : Ploc.t) ->
           (match p.CAst.v with
              CPatPrim (Numeral (n, true)) ->
                (@@) (CAst.make ~loc:((!@) loc))
                  (CPatNotation ("( _ )", ([p], []), []))
            | _ -> p :
            'pattern));
      [Gramext.Stoken ("", "_")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CPatAtom None) : 'pattern));
      [Gramext.Stoken ("", "{|");
       Gramext.Snterm
         (Gram.Entry.obj (record_patterns : 'record_patterns Gram.Entry.e));
       Gramext.Stoken ("", "|}")],
      Gramext.action
        (fun _ (pat : 'record_patterns) _ (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CPatRecord pat) : 'pattern));
      [Gramext.Snterm
         (Gram.Entry.obj (Prim.reference : 'Prim__reference Gram.Entry.e))],
      Gramext.action
        (fun (r : 'Prim__reference) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CPatAtom (Some r)) :
            'pattern))]];
  Gram.extend (impl_ident_tail : 'impl_ident_tail Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", ":");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (c : 'lconstr) _ (loc : Ploc.t) ->
           (fun na -> CLocalAssum ([na], Default Implicit, c) :
            'impl_ident_tail));
      [Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e)));
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (nal : 'name list) (loc : Ploc.t) ->
           (fun na ->
              CLocalAssum
                (na :: nal, Default Implicit,
                 (@@)
                   (CAst.make
                      ?loc:(Loc.merge_opt na.CAst.loc (Some ((!@) loc))))
                   (CHole
                      (Some (Evar_kinds.BinderType na.CAst.v), IntroAnonymous,
                       None))) :
            'impl_ident_tail));
      [Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e)));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (c : 'lconstr) _ (nal : 'name list) (loc : Ploc.t) ->
           (fun na -> CLocalAssum (na :: nal, Default Implicit, c) :
            'impl_ident_tail));
      [Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           (binder_of_name Implicit : 'impl_ident_tail))]];
  Gram.extend (fixannot : 'fixannot Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "{"); Gramext.Stoken ("IDENT", "measure");
       Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.Sopt
         (Gramext.Snterm
            (Gram.Entry.obj (identref : 'identref Gram.Entry.e)));
       Gramext.Sopt
         (Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e)));
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (rel : 'constr option) (id : 'identref option) (m : 'constr) _
             _ (loc : Ploc.t) ->
           (id, CMeasureRec (m, rel) : 'fixannot));
      [Gramext.Stoken ("", "{"); Gramext.Stoken ("IDENT", "wf");
       Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.Sopt
         (Gramext.Snterm
            (Gram.Entry.obj (identref : 'identref Gram.Entry.e)));
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (id : 'identref option) (rel : 'constr) _ _ (loc : Ploc.t) ->
           (id, CWfRec rel : 'fixannot));
      [Gramext.Stoken ("", "{"); Gramext.Stoken ("IDENT", "struct");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (id : 'identref) _ _ (loc : Ploc.t) ->
           (Some id, CStructRec : 'fixannot))]];
  Gram.extend (impl_name_head : 'impl_name_head Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (impl_ident_head : 'impl_ident_head Gram.Entry.e))],
      Gramext.action
        (fun (id : 'impl_ident_head) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (Name id) : 'impl_name_head))]];
  Gram.extend (binders_fixannot : 'binders_fixannot Gram.Entry.e) None
    [None, None,
     [[],
      Gramext.action
        (fun (loc : Ploc.t) -> ([], (None, CStructRec) : 'binders_fixannot));
      [Gramext.Snterm (Gram.Entry.obj (binder : 'binder Gram.Entry.e));
       Gramext.Sself],
      Gramext.action
        (fun (bl : 'binders_fixannot) (b : 'binder) (loc : Ploc.t) ->
           (b @ fst bl, snd bl : 'binders_fixannot));
      [Gramext.Snterm (Gram.Entry.obj (fixannot : 'fixannot Gram.Entry.e))],
      Gramext.action
        (fun (f : 'fixannot) (loc : Ploc.t) -> ([], f : 'binders_fixannot));
      [Gramext.Snterm
         (Gram.Entry.obj (impl_name_head : 'impl_name_head Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (impl_ident_tail : 'impl_ident_tail Gram.Entry.e));
       Gramext.Sself],
      Gramext.action
        (fun (bl : 'binders_fixannot) (assum : 'impl_ident_tail)
             (na : 'impl_name_head) (loc : Ploc.t) ->
           (assum na :: fst bl, snd bl : 'binders_fixannot))]];
  Gram.extend (open_binders : 'open_binders Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (closed_binder : 'closed_binder Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (binders : 'binders Gram.Entry.e))],
      Gramext.action
        (fun (bl' : 'binders) (bl : 'closed_binder) (loc : Ploc.t) ->
           (bl @ bl' : 'open_binders));
      [Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e));
       Gramext.Stoken ("", "..");
       Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e))],
      Gramext.action
        (fun (id2 : 'name) _ (id1 : 'name) (loc : Ploc.t) ->
           ([CLocalAssum
               ([id1; CAst.make ~loc:((!@) loc) (Name ldots_var); id2],
                Default Explicit,
                (@@) (CAst.make ~loc:((!@) loc))
                  (CHole (None, IntroAnonymous, None)))] :
            'open_binders));
      [Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e));
       Gramext.Slist0
         (Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e)));
       Gramext.Snterm (Gram.Entry.obj (binders : 'binders Gram.Entry.e))],
      Gramext.action
        (fun (bl : 'binders) (idl : 'name list) (id : 'name) (loc : Ploc.t) ->
           (binders_of_names (id :: idl) @ bl : 'open_binders));
      [Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e));
       Gramext.Slist0
         (Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e)));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'lconstr) _ (idl : 'name list) (id : 'name)
             (loc : Ploc.t) ->
           ([CLocalAssum (id :: idl, Default Explicit, c)] :
            'open_binders))]];
  Gram.extend (binders : 'binders Gram.Entry.e) None
    [None, None,
     [[Gramext.Slist0
         (Gramext.Snterm (Gram.Entry.obj (binder : 'binder Gram.Entry.e)))],
      Gramext.action
        (fun (l : 'binder list) (loc : Ploc.t) ->
           (List.flatten l : 'binders))]];
  Gram.extend (binder : 'binder Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (closed_binder : 'closed_binder Gram.Entry.e))],
      Gramext.action
        (fun (bl : 'closed_binder) (loc : Ploc.t) -> (bl : 'binder));
      [Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e))],
      Gramext.action
        (fun (id : 'name) (loc : Ploc.t) ->
           ([CLocalAssum
               ([id], Default Explicit,
                (@@) (CAst.make ~loc:((!@) loc))
                  (CHole (None, IntroAnonymous, None)))] :
            'binder))]];
  Gram.extend (closed_binder : 'closed_binder Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "'");
       Gramext.Snterml
         (Gram.Entry.obj (pattern : 'pattern Gram.Entry.e), "0")],
      Gramext.action
        (fun (p : 'pattern) _ (loc : Ploc.t) ->
           (let (p, ty) =
              match p.CAst.v with
                CPatCast (p, ty) -> p, Some ty
              | _ -> p, None
            in
            [CLocalPattern (CAst.make ~loc:((!@) loc) (p, ty))] :
            'closed_binder));
      [Gramext.Stoken ("", "`{");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj
               (typeclass_constraint : 'typeclass_constraint Gram.Entry.e)),
          Gramext.Stoken ("", ","), false);
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (tc : 'typeclass_constraint list) _ (loc : Ploc.t) ->
           (List.map
              (fun (n, b, t) ->
                 CLocalAssum ([n], Generalized (Implicit, Implicit, b), t))
              tc :
            'closed_binder));
      [Gramext.Stoken ("", "`(");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj
               (typeclass_constraint : 'typeclass_constraint Gram.Entry.e)),
          Gramext.Stoken ("", ","), false);
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (tc : 'typeclass_constraint list) _ (loc : Ploc.t) ->
           (List.map
              (fun (n, b, t) ->
                 CLocalAssum ([n], Generalized (Implicit, Explicit, b), t))
              tc :
            'closed_binder));
      [Gramext.Stoken ("", "{");
       Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e));
       Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e)));
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (idl : 'name list) (id : 'name) _ (loc : Ploc.t) ->
           (List.map
              (fun id ->
                 CLocalAssum
                   ([id], Default Implicit,
                    (@@) (CAst.make ~loc:((!@) loc))
                      (CHole (None, IntroAnonymous, None))))
              (id :: idl) :
            'closed_binder));
      [Gramext.Stoken ("", "{");
       Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (c : 'lconstr) _ (id : 'name) _ (loc : Ploc.t) ->
           ([CLocalAssum ([id], Default Implicit, c)] : 'closed_binder));
      [Gramext.Stoken ("", "{");
       Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e));
       Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e)));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (c : 'lconstr) _ (idl : 'name list) (id : 'name) _
             (loc : Ploc.t) ->
           ([CLocalAssum (id :: idl, Default Implicit, c)] : 'closed_binder));
      [Gramext.Stoken ("", "{");
       Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e));
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (id : 'name) _ (loc : Ploc.t) ->
           ([CLocalAssum
               ([id], Default Implicit,
                (@@) (CAst.make ~loc:((!@) loc))
                  (CHole (None, IntroAnonymous, None)))] :
            'closed_binder));
      [Gramext.Stoken ("", "(");
       Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (c : 'lconstr) _ (t : 'lconstr) _ (id : 'name) _
             (loc : Ploc.t) ->
           ([CLocalDef (id, c, Some t)] : 'closed_binder));
      [Gramext.Stoken ("", "(");
       Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (c : 'lconstr) _ (id : 'name) _ (loc : Ploc.t) ->
           (match c.CAst.v with
              CCast (c, CastConv t) -> [CLocalDef (id, c, Some t)]
            | _ -> [CLocalDef (id, c, None)] :
            'closed_binder));
      [Gramext.Stoken ("", "(");
       Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (c : 'lconstr) _ (id : 'name) _ (loc : Ploc.t) ->
           ([CLocalAssum ([id], Default Explicit, c)] : 'closed_binder));
      [Gramext.Stoken ("", "(");
       Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e));
       Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e)));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (c : 'lconstr) _ (idl : 'name list) (id : 'name) _
             (loc : Ploc.t) ->
           ([CLocalAssum (id :: idl, Default Explicit, c)] :
            'closed_binder))]];
  Gram.extend (typeclass_constraint : 'typeclass_constraint Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200")],
      Gramext.action
        (fun (c : 'operconstr) (loc : Ploc.t) ->
           (CAst.make ~loc:((!@) loc) Anonymous, false, c :
            'typeclass_constraint));
      [Gramext.Snterm
         (Gram.Entry.obj (name_colon : 'name_colon Gram.Entry.e));
       Gramext.srules
         [[], Gramext.action (fun (loc : Ploc.t) -> (false : 'e__7));
          [Gramext.Stoken ("", "!")],
          Gramext.action (fun _ (loc : Ploc.t) -> (true : 'e__7))];
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200")],
      Gramext.action
        (fun (c : 'operconstr) (expl : 'e__7) (iid : 'name_colon)
             (loc : Ploc.t) ->
           (CAst.make ~loc:((!@) loc) iid, expl, c : 'typeclass_constraint));
      [Gramext.Stoken ("", "{");
       Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e));
       Gramext.Stoken ("", "}"); Gramext.Stoken ("", ":");
       Gramext.srules
         [[], Gramext.action (fun (loc : Ploc.t) -> (false : 'e__6));
          [Gramext.Stoken ("", "!")],
          Gramext.action (fun _ (loc : Ploc.t) -> (true : 'e__6))];
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200")],
      Gramext.action
        (fun (c : 'operconstr) (expl : 'e__6) _ _ (id : 'name) _
             (loc : Ploc.t) ->
           (id, expl, c : 'typeclass_constraint));
      [Gramext.Stoken ("", "!");
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200")],
      Gramext.action
        (fun (c : 'operconstr) _ (loc : Ploc.t) ->
           (CAst.make ~loc:((!@) loc) Anonymous, true, c :
            'typeclass_constraint))]];
  Gram.extend (type_cstr : 'type_cstr Gram.Entry.e) None
    [None, None,
     [[Gramext.Sopt
         (Gramext.srules
            [[Gramext.Stoken ("", ":");
              Gramext.Snterm
                (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
             Gramext.action
               (fun (c : 'lconstr) _ (loc : Ploc.t) -> (c : 'e__8))])],
      Gramext.action
        (fun (c : 'e__8 option) (loc : Ploc.t) ->
           (Loc.tag ~loc:((!@) loc) c : 'type_cstr))]]
