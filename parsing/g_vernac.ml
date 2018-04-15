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
open Names
open Vernacexpr
open Constrexpr
open Constrexpr_ops
open Extend
open Decl_kinds
open Declarations
open Misctypes
open Tok (* necessary for camlp5 *)

open Pcoq
open Pcoq.Prim
open Pcoq.Constr
open Pcoq.Vernac_
open Pcoq.Module

let vernac_kw = [";"; ","; ">->"; ":<"; "<:"; "where"; "at"]
let _ = List.iter CLexer.add_keyword vernac_kw

(* Rem: do not join the different GEXTEND into one, it breaks native *)
(* compilation on PowerPC and Sun architectures *)

let query_command = Gram.entry_create "vernac:query_command"

let subprf = Gram.entry_create "vernac:subprf"

let class_rawexpr = Gram.entry_create "vernac:class_rawexpr"
let thm_token = Gram.entry_create "vernac:thm_token"
let def_body = Gram.entry_create "vernac:def_body"
let decl_notation = Gram.entry_create "vernac:decl_notation"
let record_field = Gram.entry_create "vernac:record_field"
let of_type_with_opt_coercion =
  Gram.entry_create "vernac:of_type_with_opt_coercion"
let instance_name = Gram.entry_create "vernac:instance_name"
let section_subset_expr = Gram.entry_create "vernac:section_subset_expr"

let make_bullet s =
  let n = String.length s in
  match s.[0] with
    '-' -> Dash n
  | '+' -> Plus n
  | '*' -> Star n
  | _ -> assert false

let parse_compat_version ?(allow_old = true) =
  let open Flags in
  function
    "8.8" -> Current
  | "8.7" -> V8_7
  | "8.6" -> V8_6
  | "8.5" | "8.4" | "8.3" | "8.2" | "8.1" | "8.0" as s ->
      CErrors.user_err ~hdr:"get_compat_version"
        Pp
        .((++) ((++) (str "Compatibility with version ") (str s))
          (str " not supported."))
  | s ->
      CErrors.user_err ~hdr:"get_compat_version"
        Pp
        .((++) ((++) (str "Unknown compatibility version \"") (str s))
          (str "\"."))

let _ =
  let _ = (vernac_control : 'vernac_control Gram.Entry.e)
  and _ = (gallina_ext : 'gallina_ext Gram.Entry.e)
  and _ = (noedit_mode : 'noedit_mode Gram.Entry.e)
  and _ = (subprf : 'subprf Gram.Entry.e) in
  let grammar_entry_create = Gram.Entry.create in
  let vernac : 'vernac Gram.Entry.e = grammar_entry_create "vernac"
  and vernac_poly : 'vernac_poly Gram.Entry.e =
    grammar_entry_create "vernac_poly"
  and vernac_aux : 'vernac_aux Gram.Entry.e =
    grammar_entry_create "vernac_aux"
  and located_vernac : 'located_vernac Gram.Entry.e =
    grammar_entry_create "located_vernac"
  in
  Gram.extend (vernac_control : 'vernac_control Gram.Entry.e)
    (Some Gramext.First)
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (vernac : 'vernac Gram.Entry.e))],
      Gramext.action
        (fun (f, v : 'vernac) (loc : Ploc.t) ->
           (VernacExpr (f, v) : 'vernac_control));
      [Gramext.Stoken ("IDENT", "Fail"); Gramext.Sself],
      Gramext.action
        (fun (v : 'vernac_control) _ (loc : Ploc.t) ->
           (VernacFail v : 'vernac_control));
      [Gramext.Stoken ("IDENT", "Timeout");
       Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e));
       Gramext.Sself],
      Gramext.action
        (fun (v : 'vernac_control) (n : 'natural) _ (loc : Ploc.t) ->
           (VernacTimeout (n, v) : 'vernac_control));
      [Gramext.Stoken ("IDENT", "Redirect");
       Gramext.Snterm (Gram.Entry.obj (ne_string : 'ne_string Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (located_vernac : 'located_vernac Gram.Entry.e))],
      Gramext.action
        (fun (c : 'located_vernac) (s : 'ne_string) _ (loc : Ploc.t) ->
           (VernacRedirect (s, c) : 'vernac_control));
      [Gramext.Stoken ("IDENT", "Time");
       Gramext.Snterm
         (Gram.Entry.obj (located_vernac : 'located_vernac Gram.Entry.e))],
      Gramext.action
        (fun (c : 'located_vernac) _ (loc : Ploc.t) ->
           (VernacTime (false, c) : 'vernac_control))]];
  Gram.extend (vernac : 'vernac Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (vernac_poly : 'vernac_poly Gram.Entry.e))],
      Gramext.action (fun (v : 'vernac_poly) (loc : Ploc.t) -> (v : 'vernac));
      [Gramext.Stoken ("IDENT", "Global");
       Gramext.Snterm
         (Gram.Entry.obj (vernac_poly : 'vernac_poly Gram.Entry.e))],
      Gramext.action
        (fun (f, v : 'vernac_poly) _ (loc : Ploc.t) ->
           (VernacLocal false :: f, v : 'vernac));
      [Gramext.Stoken ("IDENT", "Local");
       Gramext.Snterm
         (Gram.Entry.obj (vernac_poly : 'vernac_poly Gram.Entry.e))],
      Gramext.action
        (fun (f, v : 'vernac_poly) _ (loc : Ploc.t) ->
           (VernacLocal true :: f, v : 'vernac))]];
  Gram.extend (vernac_poly : 'vernac_poly Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (vernac_aux : 'vernac_aux Gram.Entry.e))],
      Gramext.action
        (fun (v : 'vernac_aux) (loc : Ploc.t) -> (v : 'vernac_poly));
      [Gramext.Stoken ("IDENT", "Monomorphic");
       Gramext.Snterm
         (Gram.Entry.obj (vernac_aux : 'vernac_aux Gram.Entry.e))],
      Gramext.action
        (fun (f, v : 'vernac_aux) _ (loc : Ploc.t) ->
           (VernacPolymorphic false :: f, v : 'vernac_poly));
      [Gramext.Stoken ("IDENT", "Polymorphic");
       Gramext.Snterm
         (Gram.Entry.obj (vernac_aux : 'vernac_aux Gram.Entry.e))],
      Gramext.action
        (fun (f, v : 'vernac_aux) _ (loc : Ploc.t) ->
           (VernacPolymorphic true :: f, v : 'vernac_poly))]];
  Gram.extend (vernac_aux : 'vernac_aux Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (subprf : 'subprf Gram.Entry.e))],
      Gramext.action
        (fun (c : 'subprf) (loc : Ploc.t) -> ([], c : 'vernac_aux));
      [Gramext.Snterm (Gram.Entry.obj (syntax : 'syntax Gram.Entry.e));
       Gramext.Stoken ("", ".")],
      Gramext.action
        (fun _ (c : 'syntax) (loc : Ploc.t) -> ([], c : 'vernac_aux));
      [Gramext.Snterm (Gram.Entry.obj (command : 'command Gram.Entry.e));
       Gramext.Stoken ("", ".")],
      Gramext.action
        (fun _ (c : 'command) (loc : Ploc.t) -> ([], c : 'vernac_aux));
      [Gramext.Snterm
         (Gram.Entry.obj (gallina_ext : 'gallina_ext Gram.Entry.e));
       Gramext.Stoken ("", ".")],
      Gramext.action
        (fun _ (g : 'gallina_ext) (loc : Ploc.t) -> ([], g : 'vernac_aux));
      [Gramext.Snterm (Gram.Entry.obj (gallina : 'gallina Gram.Entry.e));
       Gramext.Stoken ("", ".")],
      Gramext.action
        (fun _ (g : 'gallina) (loc : Ploc.t) -> ([], g : 'vernac_aux));
      [Gramext.Stoken ("IDENT", "Program");
       Gramext.Snterm
         (Gram.Entry.obj (gallina_ext : 'gallina_ext Gram.Entry.e));
       Gramext.Stoken ("", ".")],
      Gramext.action
        (fun _ (g : 'gallina_ext) _ (loc : Ploc.t) ->
           ([VernacProgram], g : 'vernac_aux));
      [Gramext.Stoken ("IDENT", "Program");
       Gramext.Snterm (Gram.Entry.obj (gallina : 'gallina Gram.Entry.e));
       Gramext.Stoken ("", ".")],
      Gramext.action
        (fun _ (g : 'gallina) _ (loc : Ploc.t) ->
           ([VernacProgram], g : 'vernac_aux))]];
  Gram.extend (vernac_aux : 'vernac_aux Gram.Entry.e) (Some Gramext.Last)
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (command_entry : 'command_entry Gram.Entry.e))],
      Gramext.action
        (fun (prfcom : 'command_entry) (loc : Ploc.t) ->
           ([], prfcom : 'vernac_aux))]];
  Gram.extend (noedit_mode : 'noedit_mode Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (query_command : 'query_command Gram.Entry.e))],
      Gramext.action
        (fun (c : 'query_command) (loc : Ploc.t) ->
           (c None : 'noedit_mode))]];
  Gram.extend (subprf : 'subprf Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "}")],
      Gramext.action (fun _ (loc : Ploc.t) -> (VernacEndSubproof : 'subprf));
      [Gramext.Stoken ("", "{")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (VernacSubproof None : 'subprf));
      [Gramext.Stoken ("BULLET", "")],
      Gramext.action
        (fun (s : string) (loc : Ploc.t) ->
           (VernacBullet (make_bullet s) : 'subprf))]];
  Gram.extend (located_vernac : 'located_vernac Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (vernac_control : 'vernac_control Gram.Entry.e))],
      Gramext.action
        (fun (v : 'vernac_control) (loc : Ploc.t) ->
           (CAst.make ~loc:((!@) loc) v : 'located_vernac))]]

let warn_plural_command =
  CWarnings.create ~name:"plural-command" ~category:"pedantic"
    ~default:CWarnings.Disabled
    (fun kwd ->
       strbrk
         (Printf.sprintf "Command \"%s\" expects more than one assumption."
            kwd))

let test_plural_form loc kwd =
  function
    [_, ([_], _)] -> warn_plural_command ~loc:((!@) loc) kwd
  | _ -> ()

let test_plural_form_types loc kwd =
  function
    [[_], _] -> warn_plural_command ~loc:((!@) loc) kwd
  | _ -> ()

let lname_of_lident : lident -> lname = CAst.map (fun s -> Name s)

let name_of_ident_decl : ident_decl -> name_decl = on_fst lname_of_lident

(* Gallina declarations *)
let _ =
  let _ = (gallina : 'gallina Gram.Entry.e)
  and _ = (gallina_ext : 'gallina_ext Gram.Entry.e)
  and _ = (thm_token : 'thm_token Gram.Entry.e)
  and _ = (def_body : 'def_body Gram.Entry.e)
  and _ =
    (of_type_with_opt_coercion : 'of_type_with_opt_coercion Gram.Entry.e)
  and _ = (record_field : 'record_field Gram.Entry.e)
  and _ = (decl_notation : 'decl_notation Gram.Entry.e)
  and _ = (rec_definition : 'rec_definition Gram.Entry.e)
  and _ = (ident_decl : 'ident_decl Gram.Entry.e)
  and _ = (univ_decl : 'univ_decl Gram.Entry.e) in
  let grammar_entry_create = Gram.Entry.create in
  let def_token : 'def_token Gram.Entry.e = grammar_entry_create "def_token"
  and assumption_token : 'assumption_token Gram.Entry.e =
    grammar_entry_create "assumption_token"
  and assumptions_token : 'assumptions_token Gram.Entry.e =
    grammar_entry_create "assumptions_token"
  and inline : 'inline Gram.Entry.e = grammar_entry_create "inline"
  and univ_constraint : 'univ_constraint Gram.Entry.e =
    grammar_entry_create "univ_constraint"
  and finite_token : 'finite_token Gram.Entry.e =
    grammar_entry_create "finite_token"
  and cumulativity_token : 'cumulativity_token Gram.Entry.e =
    grammar_entry_create "cumulativity_token"
  and private_token : 'private_token Gram.Entry.e =
    grammar_entry_create "private_token"
  and reduce : 'reduce Gram.Entry.e = grammar_entry_create "reduce"
  and one_decl_notation : 'one_decl_notation Gram.Entry.e =
    grammar_entry_create "one_decl_notation"
  and opt_constructors_or_fields : 'opt_constructors_or_fields Gram.Entry.e =
    (* Inductives and records *)
    grammar_entry_create "opt_constructors_or_fields"
  and inductive_definition : 'inductive_definition Gram.Entry.e =
    grammar_entry_create "inductive_definition"
  and constructor_list_or_record_decl : 'constructor_list_or_record_decl Gram.Entry.e =
    grammar_entry_create "constructor_list_or_record_decl"
  and opt_coercion : 'opt_coercion Gram.Entry.e =
    (*
      csort:
        [ [ s = sort -> CSort (loc,s) ] ]
      ;
    *)
    grammar_entry_create "opt_coercion"
  and corec_definition : 'corec_definition Gram.Entry.e =
    grammar_entry_create "corec_definition"
  and type_cstr : 'type_cstr Gram.Entry.e = grammar_entry_create "type_cstr"
  and scheme : 'scheme Gram.Entry.e =
    (* Inductive schemes *)
    grammar_entry_create "scheme"
  and scheme_kind : 'scheme_kind Gram.Entry.e =
    grammar_entry_create "scheme_kind"
  and record_fields : 'record_fields Gram.Entry.e =
    grammar_entry_create "record_fields"
  and record_binder_body : 'record_binder_body Gram.Entry.e =
    grammar_entry_create "record_binder_body"
  and record_binder : 'record_binder Gram.Entry.e =
    grammar_entry_create "record_binder"
  and assum_list : 'assum_list Gram.Entry.e =
    grammar_entry_create "assum_list"
  and assum_coe : 'assum_coe Gram.Entry.e = grammar_entry_create "assum_coe"
  and simple_assum_coe : 'simple_assum_coe Gram.Entry.e =
    grammar_entry_create "simple_assum_coe"
  and constructor_type : 'constructor_type Gram.Entry.e =
    grammar_entry_create "constructor_type"
  and constructor : 'constructor Gram.Entry.e =
    grammar_entry_create "constructor"
  in
  Gram.extend (gallina : 'gallina Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "Constraint");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj
               (univ_constraint : 'univ_constraint Gram.Entry.e)),
          Gramext.Stoken ("", ","), false)],
      Gramext.action
        (fun (l : 'univ_constraint list) _ (loc : Ploc.t) ->
           (VernacConstraint l : 'gallina));
      [Gramext.Stoken ("IDENT", "Universes");
       Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (identref : 'identref Gram.Entry.e)))],
      Gramext.action
        (fun (l : 'identref list) _ (loc : Ploc.t) ->
           (VernacUniverse l : 'gallina));
      [Gramext.Stoken ("IDENT", "Universe");
       Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (identref : 'identref Gram.Entry.e)))],
      Gramext.action
        (fun (l : 'identref list) _ (loc : Ploc.t) ->
           (VernacUniverse l : 'gallina));
      [Gramext.Stoken ("IDENT", "Register");
       Gramext.Stoken ("IDENT", "Inline");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e))],
      Gramext.action
        (fun (id : 'identref) _ _ (loc : Ploc.t) ->
           (VernacRegister (id, RegisterInline) : 'gallina));
      [Gramext.Stoken ("IDENT", "Combined");
       Gramext.Stoken ("IDENT", "Scheme");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Stoken ("IDENT", "from");
       Gramext.Slist1sep
         (Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e)),
          Gramext.Stoken ("", ","), false)],
      Gramext.action
        (fun (l : 'identref list) _ (id : 'identref) _ _ (loc : Ploc.t) ->
           (VernacCombinedScheme (id, l) : 'gallina));
      [Gramext.Stoken ("IDENT", "Scheme");
       Gramext.Slist1sep
         (Gramext.Snterm (Gram.Entry.obj (scheme : 'scheme Gram.Entry.e)),
          Gramext.Stoken ("", "with"), false)],
      Gramext.action
        (fun (l : 'scheme list) _ (loc : Ploc.t) ->
           (VernacScheme l : 'gallina));
      [Gramext.Stoken ("IDENT", "Let"); Gramext.Stoken ("", "CoFixpoint");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj
               (corec_definition : 'corec_definition Gram.Entry.e)),
          Gramext.Stoken ("", "with"), false)],
      Gramext.action
        (fun (corecs : 'corec_definition list) _ _ (loc : Ploc.t) ->
           (VernacCoFixpoint (DoDischarge, corecs) : 'gallina));
      [Gramext.Stoken ("", "CoFixpoint");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj
               (corec_definition : 'corec_definition Gram.Entry.e)),
          Gramext.Stoken ("", "with"), false)],
      Gramext.action
        (fun (corecs : 'corec_definition list) _ (loc : Ploc.t) ->
           (VernacCoFixpoint (NoDischarge, corecs) : 'gallina));
      [Gramext.Stoken ("IDENT", "Let"); Gramext.Stoken ("", "Fixpoint");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj (rec_definition : 'rec_definition Gram.Entry.e)),
          Gramext.Stoken ("", "with"), false)],
      Gramext.action
        (fun (recs : 'rec_definition list) _ _ (loc : Ploc.t) ->
           (VernacFixpoint (DoDischarge, recs) : 'gallina));
      [Gramext.Stoken ("", "Fixpoint");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj (rec_definition : 'rec_definition Gram.Entry.e)),
          Gramext.Stoken ("", "with"), false)],
      Gramext.action
        (fun (recs : 'rec_definition list) _ (loc : Ploc.t) ->
           (VernacFixpoint (NoDischarge, recs) : 'gallina));
      [Gramext.Snterm
         (Gram.Entry.obj
            (cumulativity_token : 'cumulativity_token Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (private_token : 'private_token Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (finite_token : 'finite_token Gram.Entry.e));
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj
               (inductive_definition : 'inductive_definition Gram.Entry.e)),
          Gramext.Stoken ("", "with"), false)],
      Gramext.action
        (fun (indl : 'inductive_definition list) (f : 'finite_token)
             (priv : 'private_token) (cum : 'cumulativity_token)
             (loc : Ploc.t) ->
           (let (k, f) = f in
            let indl =
              List.map (fun ((a, b, c, d), e) -> (a, b, c, k, d), e) indl
            in
            let cum =
              match cum with
                Some true -> LocalCumulativity
              | Some false -> LocalNonCumulativity
              | None ->
                  if Flags.is_polymorphic_inductive_cumulativity () then
                    GlobalCumulativity
                  else GlobalNonCumulativity
            in
            VernacInductive (cum, priv, f, indl) :
            'gallina));
      [Gramext.Stoken ("IDENT", "Let");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (def_body : 'def_body Gram.Entry.e))],
      Gramext.action
        (fun (b : 'def_body) (id : 'identref) _ (loc : Ploc.t) ->
           (VernacDefinition
              ((DoDischarge, Let), (lname_of_lident id, None), b) :
            'gallina));
      [Gramext.Snterm (Gram.Entry.obj (def_token : 'def_token Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (ident_decl : 'ident_decl Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (def_body : 'def_body Gram.Entry.e))],
      Gramext.action
        (fun (b : 'def_body) (id : 'ident_decl) (d : 'def_token)
             (loc : Ploc.t) ->
           (VernacDefinition (d, name_of_ident_decl id, b) : 'gallina));
      [Gramext.Snterm
         (Gram.Entry.obj
            (assumptions_token : 'assumptions_token Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (inline : 'inline Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (assum_list : 'assum_list Gram.Entry.e))],
      Gramext.action
        (fun (bl : 'assum_list) (nl : 'inline)
             (kwd, stre : 'assumptions_token) (loc : Ploc.t) ->
           (test_plural_form loc kwd bl; VernacAssumption (stre, nl, bl) :
            'gallina));
      [Gramext.Snterm
         (Gram.Entry.obj (assumption_token : 'assumption_token Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (inline : 'inline Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (assum_list : 'assum_list Gram.Entry.e))],
      Gramext.action
        (fun (bl : 'assum_list) (nl : 'inline) (stre : 'assumption_token)
             (loc : Ploc.t) ->
           (VernacAssumption (stre, nl, bl) : 'gallina));
      [Gramext.Snterm (Gram.Entry.obj (thm_token : 'thm_token Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (ident_decl : 'ident_decl Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (binders : 'binders Gram.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Slist0
         (Gramext.srules
            [[Gramext.Stoken ("", "with");
              Gramext.Snterm
                (Gram.Entry.obj (ident_decl : 'ident_decl Gram.Entry.e));
              Gramext.Snterm
                (Gram.Entry.obj (binders : 'binders Gram.Entry.e));
              Gramext.Stoken ("", ":");
              Gramext.Snterm
                (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
             Gramext.action
               (fun (c : 'lconstr) _ (bl : 'binders) (id : 'ident_decl) _
                    (loc : Ploc.t) ->
                  (id, (bl, c) : 'e__1))])],
      Gramext.action
        (fun (l : 'e__1 list) (c : 'lconstr) _ (bl : 'binders)
             (id : 'ident_decl) (thm : 'thm_token) (loc : Ploc.t) ->
           (VernacStartTheoremProof (thm, (id, (bl, c)) :: l) : 'gallina))]];
  Gram.extend (thm_token : 'thm_token Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "Property")],
      Gramext.action (fun _ (loc : Ploc.t) -> (Property : 'thm_token));
      [Gramext.Stoken ("IDENT", "Proposition")],
      Gramext.action (fun _ (loc : Ploc.t) -> (Proposition : 'thm_token));
      [Gramext.Stoken ("IDENT", "Corollary")],
      Gramext.action (fun _ (loc : Ploc.t) -> (Corollary : 'thm_token));
      [Gramext.Stoken ("IDENT", "Remark")],
      Gramext.action (fun _ (loc : Ploc.t) -> (Remark : 'thm_token));
      [Gramext.Stoken ("IDENT", "Fact")],
      Gramext.action (fun _ (loc : Ploc.t) -> (Fact : 'thm_token));
      [Gramext.Stoken ("IDENT", "Lemma")],
      Gramext.action (fun _ (loc : Ploc.t) -> (Lemma : 'thm_token));
      [Gramext.Stoken ("", "Theorem")],
      Gramext.action (fun _ (loc : Ploc.t) -> (Theorem : 'thm_token))]];
  Gram.extend (def_token : 'def_token Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "SubClass")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (NoDischarge, SubClass : 'def_token));
      [Gramext.Stoken ("IDENT", "Example")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (NoDischarge, Example : 'def_token));
      [Gramext.Stoken ("", "Definition")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (NoDischarge, Definition : 'def_token))]];
  Gram.extend (assumption_token : 'assumption_token Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "Conjecture")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           (NoDischarge, Conjectural : 'assumption_token));
      [Gramext.Stoken ("", "Parameter")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           (NoDischarge, Definitional : 'assumption_token));
      [Gramext.Stoken ("", "Axiom")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (NoDischarge, Logical : 'assumption_token));
      [Gramext.Stoken ("", "Variable")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           (DoDischarge, Definitional : 'assumption_token));
      [Gramext.Stoken ("", "Hypothesis")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           (DoDischarge, Logical : 'assumption_token))]];
  Gram.extend (assumptions_token : 'assumptions_token Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "Conjectures")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           ("Conjectures", (NoDischarge, Conjectural) : 'assumptions_token));
      [Gramext.Stoken ("IDENT", "Parameters")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           ("Parameters", (NoDischarge, Definitional) : 'assumptions_token));
      [Gramext.Stoken ("IDENT", "Axioms")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           ("Axioms", (NoDischarge, Logical) : 'assumptions_token));
      [Gramext.Stoken ("IDENT", "Variables")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           ("Variables", (DoDischarge, Definitional) : 'assumptions_token));
      [Gramext.Stoken ("IDENT", "Hypotheses")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           ("Hypotheses", (DoDischarge, Logical) : 'assumptions_token))]];
  Gram.extend (inline : 'inline Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> (NoInline : 'inline));
      [Gramext.Stoken ("IDENT", "Inline")],
      Gramext.action (fun _ (loc : Ploc.t) -> (DefaultInline : 'inline));
      [Gramext.Stoken ("IDENT", "Inline"); Gramext.Stoken ("", "(");
       Gramext.Stoken ("INT", ""); Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (i : string) _ _ (loc : Ploc.t) ->
           (InlineAt (int_of_string i) : 'inline))]];
  Gram.extend (univ_constraint : 'univ_constraint Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (universe_level : 'universe_level Gram.Entry.e));
       Gramext.srules
         [[Gramext.Stoken ("", "<=")],
          Gramext.action (fun _ (loc : Ploc.t) -> (Univ.Le : 'e__2));
          [Gramext.Stoken ("", "=")],
          Gramext.action (fun _ (loc : Ploc.t) -> (Univ.Eq : 'e__2));
          [Gramext.Stoken ("", "<")],
          Gramext.action (fun _ (loc : Ploc.t) -> (Univ.Lt : 'e__2))];
       Gramext.Snterm
         (Gram.Entry.obj (universe_level : 'universe_level Gram.Entry.e))],
      Gramext.action
        (fun (r : 'universe_level) (ord : 'e__2) (l : 'universe_level)
             (loc : Ploc.t) ->
           (l, ord, r : 'univ_constraint))]];
  Gram.extend (univ_decl : 'univ_decl Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "@{");
       Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj (identref : 'identref Gram.Entry.e)));
       Gramext.srules
         [[], Gramext.action (fun (loc : Ploc.t) -> (false : 'e__3));
          [Gramext.Stoken ("", "+")],
          Gramext.action (fun _ (loc : Ploc.t) -> (true : 'e__3))];
       Gramext.srules
         [[Gramext.srules
             [[Gramext.Stoken ("", "|}")],
              Gramext.action (fun _ (loc : Ploc.t) -> (false : 'e__5));
              [Gramext.Stoken ("", "}")],
              Gramext.action (fun _ (loc : Ploc.t) -> (true : 'e__5))]],
          Gramext.action
            (fun (ext : 'e__5) (loc : Ploc.t) -> ([], ext : 'e__6));
          [Gramext.Stoken ("", "|");
           Gramext.Slist0sep
             (Gramext.Snterm
                (Gram.Entry.obj
                   (univ_constraint : 'univ_constraint Gram.Entry.e)),
              Gramext.Stoken ("", ","), false);
           Gramext.srules
             [[], Gramext.action (fun (loc : Ploc.t) -> (false : 'e__4));
              [Gramext.Stoken ("", "+")],
              Gramext.action (fun _ (loc : Ploc.t) -> (true : 'e__4))];
           Gramext.Stoken ("", "}")],
          Gramext.action
            (fun _ (ext : 'e__4) (l' : 'univ_constraint list) _
                 (loc : Ploc.t) ->
               (l', ext : 'e__6))]],
      Gramext.action
        (fun (cs : 'e__6) (ext : 'e__3) (l : 'identref list) _
             (loc : Ploc.t) ->
           ({univdecl_instance = l; univdecl_extensible_instance = ext;
             univdecl_constraints = fst cs;
             univdecl_extensible_constraints = snd cs} :
            'univ_decl))]];
  Gram.extend (ident_decl : 'ident_decl Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Sopt
         (Gramext.Snterm
            (Gram.Entry.obj (univ_decl : 'univ_decl Gram.Entry.e)))],
      Gramext.action
        (fun (l : 'univ_decl option) (i : 'identref) (loc : Ploc.t) ->
           (i, l : 'ident_decl))]];
  Gram.extend (finite_token : 'finite_token Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "Class")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (Class true, BiFinite : 'finite_token));
      [Gramext.Stoken ("IDENT", "Structure")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (Structure, BiFinite : 'finite_token));
      [Gramext.Stoken ("IDENT", "Record")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (Record, BiFinite : 'finite_token));
      [Gramext.Stoken ("IDENT", "Variant")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (Variant, BiFinite : 'finite_token));
      [Gramext.Stoken ("IDENT", "CoInductive")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (CoInductive, CoFinite : 'finite_token));
      [Gramext.Stoken ("IDENT", "Inductive")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (Inductive_kw, Finite : 'finite_token))]];
  Gram.extend (cumulativity_token : 'cumulativity_token Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> (None : 'cumulativity_token));
      [Gramext.Stoken ("IDENT", "NonCumulative")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (Some false : 'cumulativity_token));
      [Gramext.Stoken ("IDENT", "Cumulative")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (Some true : 'cumulativity_token))]];
  Gram.extend (private_token : 'private_token Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> (false : 'private_token));
      [Gramext.Stoken ("IDENT", "Private")],
      Gramext.action (fun _ (loc : Ploc.t) -> (true : 'private_token))]];
  Gram.extend (def_body : 'def_body Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (binders : 'binders Gram.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
      Gramext.action
        (fun (t : 'lconstr) _ (bl : 'binders) (loc : Ploc.t) ->
           (ProveBody (bl, t) : 'def_body));
      [Gramext.Snterm (Gram.Entry.obj (binders : 'binders Gram.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm (Gram.Entry.obj (reduce : 'reduce Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'lconstr) (red : 'reduce) _ (t : 'lconstr) _ (bl : 'binders)
             (loc : Ploc.t) ->
           (let ((bl, c), tyo) =
              if List.exists
                   (function
                      CLocalPattern _ -> true
                    | _ -> false)
                   bl
              then
                let c =
                  (@@) (CAst.make ~loc:((!@) loc)) (CCast (c, CastConv t))
                in
                ([], mkCLambdaN ~loc:((!@) loc) bl c), None
              else (bl, c), Some t
            in
            DefineBody (bl, red, c, tyo) :
            'def_body));
      [Gramext.Snterm (Gram.Entry.obj (binders : 'binders Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm (Gram.Entry.obj (reduce : 'reduce Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'lconstr) (red : 'reduce) _ (bl : 'binders)
             (loc : Ploc.t) ->
           (if List.exists
                 (function
                    CLocalPattern _ -> true
                  | _ -> false)
                 bl
            then
              let c = mkCLambdaN ~loc:((!@) loc) bl c in
              DefineBody ([], red, c, None)
            else
              match c with
                {CAst.v = CCast (c, CastConv t)} ->
                  DefineBody (bl, red, c, Some t)
              | _ -> DefineBody (bl, red, c, None) :
            'def_body))]];
  Gram.extend (reduce : 'reduce Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> (None : 'reduce));
      [Gramext.Stoken ("IDENT", "Eval");
       Gramext.Snterm (Gram.Entry.obj (red_expr : 'red_expr Gram.Entry.e));
       Gramext.Stoken ("", "in")],
      Gramext.action
        (fun _ (r : 'red_expr) _ (loc : Ploc.t) -> (Some r : 'reduce))]];
  Gram.extend (one_decl_notation : 'one_decl_notation Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (ne_lstring : 'ne_lstring Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.Sopt
         (Gramext.srules
            [[Gramext.Stoken ("", ":"); Gramext.Stoken ("IDENT", "")],
             Gramext.action
               (fun (sc : string) _ (loc : Ploc.t) -> (sc : 'e__7))])],
      Gramext.action
        (fun (scopt : 'e__7 option) (c : 'constr) _ (ntn : 'ne_lstring)
             (loc : Ploc.t) ->
           (ntn, c, scopt : 'one_decl_notation))]];
  Gram.extend (decl_notation : 'decl_notation Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> ([] : 'decl_notation));
      [Gramext.Stoken ("", "where");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj
               (one_decl_notation : 'one_decl_notation Gram.Entry.e)),
          Gramext.Stoken ("IDENT", "and"), false)],
      Gramext.action
        (fun (l : 'one_decl_notation list) _ (loc : Ploc.t) ->
           (l : 'decl_notation))]];
  Gram.extend
    (opt_constructors_or_fields : 'opt_constructors_or_fields Gram.Entry.e)
    None
    [None, None,
     [[],
      Gramext.action
        (fun (loc : Ploc.t) ->
           (RecordDecl (None, []) : 'opt_constructors_or_fields));
      [Gramext.Stoken ("", ":=");
       Gramext.Snterm
         (Gram.Entry.obj
            (constructor_list_or_record_decl :
             'constructor_list_or_record_decl Gram.Entry.e))],
      Gramext.action
        (fun (lc : 'constructor_list_or_record_decl) _ (loc : Ploc.t) ->
           (lc : 'opt_constructors_or_fields))]];
  Gram.extend (inductive_definition : 'inductive_definition Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (opt_coercion : 'opt_coercion Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (ident_decl : 'ident_decl Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (binders : 'binders Gram.Entry.e));
       Gramext.Sopt
         (Gramext.srules
            [[Gramext.Stoken ("", ":");
              Gramext.Snterm
                (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
             Gramext.action
               (fun (c : 'lconstr) _ (loc : Ploc.t) -> (c : 'e__8))]);
       Gramext.Snterm
         (Gram.Entry.obj
            (opt_constructors_or_fields :
             'opt_constructors_or_fields Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (decl_notation : 'decl_notation Gram.Entry.e))],
      Gramext.action
        (fun (ntn : 'decl_notation) (lc : 'opt_constructors_or_fields)
             (c : 'e__8 option) (indpar : 'binders) (id : 'ident_decl)
             (oc : 'opt_coercion) (loc : Ploc.t) ->
           (((oc, id), indpar, c, lc), ntn : 'inductive_definition))]];
  Gram.extend
    (constructor_list_or_record_decl :
     'constructor_list_or_record_decl Gram.Entry.e)
    None
    [None, None,
     [[],
      Gramext.action
        (fun (loc : Ploc.t) ->
           (Constructors [] : 'constructor_list_or_record_decl));
      [Gramext.Stoken ("", "{");
       Gramext.Snterm
         (Gram.Entry.obj (record_fields : 'record_fields Gram.Entry.e));
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (fs : 'record_fields) _ (loc : Ploc.t) ->
           (RecordDecl (None, fs) : 'constructor_list_or_record_decl));
      [Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Stoken ("", "{");
       Gramext.Snterm
         (Gram.Entry.obj (record_fields : 'record_fields Gram.Entry.e));
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (fs : 'record_fields) _ (cstr : 'identref) (loc : Ploc.t) ->
           (RecordDecl (Some cstr, fs) : 'constructor_list_or_record_decl));
      [Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj
            (constructor_type : 'constructor_type Gram.Entry.e))],
      Gramext.action
        (fun (c : 'constructor_type) (id : 'identref) (loc : Ploc.t) ->
           (Constructors [c id] : 'constructor_list_or_record_decl));
      [Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (constructor_type : 'constructor_type Gram.Entry.e));
       Gramext.Stoken ("", "|");
       Gramext.Slist0sep
         (Gramext.Snterm
            (Gram.Entry.obj (constructor : 'constructor Gram.Entry.e)),
          Gramext.Stoken ("", "|"), false)],
      Gramext.action
        (fun (l : 'constructor list) _ (c : 'constructor_type)
             (id : 'identref) (loc : Ploc.t) ->
           (Constructors (c id :: l) : 'constructor_list_or_record_decl));
      [Gramext.Stoken ("", "|");
       Gramext.Slist1sep
         (Gramext.Snterm
            (Gram.Entry.obj (constructor : 'constructor Gram.Entry.e)),
          Gramext.Stoken ("", "|"), false)],
      Gramext.action
        (fun (l : 'constructor list) _ (loc : Ploc.t) ->
           (Constructors l : 'constructor_list_or_record_decl))]];
  Gram.extend (opt_coercion : 'opt_coercion Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> (false : 'opt_coercion));
      [Gramext.Stoken ("", ">")],
      Gramext.action (fun _ (loc : Ploc.t) -> (true : 'opt_coercion))]];
  Gram.extend (rec_definition : 'rec_definition Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (ident_decl : 'ident_decl Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (binders_fixannot : 'binders_fixannot Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (type_cstr : 'type_cstr Gram.Entry.e));
       Gramext.Sopt
         (Gramext.srules
            [[Gramext.Stoken ("", ":=");
              Gramext.Snterm
                (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
             Gramext.action
               (fun (def : 'lconstr) _ (loc : Ploc.t) -> (def : 'e__9))]);
       Gramext.Snterm
         (Gram.Entry.obj (decl_notation : 'decl_notation Gram.Entry.e))],
      Gramext.action
        (fun (ntn : 'decl_notation) (def : 'e__9 option) (ty : 'type_cstr)
             (bl : 'binders_fixannot) (id : 'ident_decl) (loc : Ploc.t) ->
           (let (bl, annot) = bl in (id, annot, bl, ty, def), ntn :
            'rec_definition))]];
  Gram.extend (corec_definition : 'corec_definition Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (ident_decl : 'ident_decl Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (binders : 'binders Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (type_cstr : 'type_cstr Gram.Entry.e));
       Gramext.Sopt
         (Gramext.srules
            [[Gramext.Stoken ("", ":=");
              Gramext.Snterm
                (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
             Gramext.action
               (fun (def : 'lconstr) _ (loc : Ploc.t) -> (def : 'e__10))]);
       Gramext.Snterm
         (Gram.Entry.obj (decl_notation : 'decl_notation Gram.Entry.e))],
      Gramext.action
        (fun (ntn : 'decl_notation) (def : 'e__10 option) (ty : 'type_cstr)
             (bl : 'binders) (id : 'ident_decl) (loc : Ploc.t) ->
           ((id, bl, ty, def), ntn : 'corec_definition))]];
  Gram.extend (type_cstr : 'type_cstr Gram.Entry.e) None
    [None, None,
     [[],
      Gramext.action
        (fun (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc))
              (CHole (None, Misctypes.IntroAnonymous, None)) :
            'type_cstr));
      [Gramext.Stoken ("", ":");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'lconstr) _ (loc : Ploc.t) -> (c : 'type_cstr))]];
  Gram.extend (scheme : 'scheme Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm
         (Gram.Entry.obj (scheme_kind : 'scheme_kind Gram.Entry.e))],
      Gramext.action
        (fun (kind : 'scheme_kind) _ (id : 'identref) (loc : Ploc.t) ->
           (Some id, kind : 'scheme));
      [Gramext.Snterm
         (Gram.Entry.obj (scheme_kind : 'scheme_kind Gram.Entry.e))],
      Gramext.action
        (fun (kind : 'scheme_kind) (loc : Ploc.t) ->
           (None, kind : 'scheme))]];
  Gram.extend (scheme_kind : 'scheme_kind Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "Equality"); Gramext.Stoken ("", "for");
       Gramext.Snterm
         (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e))],
      Gramext.action
        (fun (ind : 'smart_global) _ _ (loc : Ploc.t) ->
           (EqualityScheme ind : 'scheme_kind));
      [Gramext.Stoken ("IDENT", "Case"); Gramext.Stoken ("", "for");
       Gramext.Snterm
         (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e));
       Gramext.Stoken ("IDENT", "Sort");
       Gramext.Snterm
         (Gram.Entry.obj (sort_family : 'sort_family Gram.Entry.e))],
      Gramext.action
        (fun (s : 'sort_family) _ (ind : 'smart_global) _ _ (loc : Ploc.t) ->
           (CaseScheme (false, ind, s) : 'scheme_kind));
      [Gramext.Stoken ("IDENT", "Elimination"); Gramext.Stoken ("", "for");
       Gramext.Snterm
         (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e));
       Gramext.Stoken ("IDENT", "Sort");
       Gramext.Snterm
         (Gram.Entry.obj (sort_family : 'sort_family Gram.Entry.e))],
      Gramext.action
        (fun (s : 'sort_family) _ (ind : 'smart_global) _ _ (loc : Ploc.t) ->
           (CaseScheme (true, ind, s) : 'scheme_kind));
      [Gramext.Stoken ("IDENT", "Minimality"); Gramext.Stoken ("", "for");
       Gramext.Snterm
         (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e));
       Gramext.Stoken ("IDENT", "Sort");
       Gramext.Snterm
         (Gram.Entry.obj (sort_family : 'sort_family Gram.Entry.e))],
      Gramext.action
        (fun (s : 'sort_family) _ (ind : 'smart_global) _ _ (loc : Ploc.t) ->
           (InductionScheme (false, ind, s) : 'scheme_kind));
      [Gramext.Stoken ("IDENT", "Induction"); Gramext.Stoken ("", "for");
       Gramext.Snterm
         (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e));
       Gramext.Stoken ("IDENT", "Sort");
       Gramext.Snterm
         (Gram.Entry.obj (sort_family : 'sort_family Gram.Entry.e))],
      Gramext.action
        (fun (s : 'sort_family) _ (ind : 'smart_global) _ _ (loc : Ploc.t) ->
           (InductionScheme (true, ind, s) : 'scheme_kind))]];
  Gram.extend (record_field : 'record_field Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (record_binder : 'record_binder Gram.Entry.e));
       Gramext.Sopt
         (Gramext.srules
            [[Gramext.Stoken ("", "|");
              Gramext.Snterm
                (Gram.Entry.obj (natural : 'natural Gram.Entry.e))],
             Gramext.action
               (fun (n : 'natural) _ (loc : Ploc.t) -> (n : 'e__11))]);
       Gramext.Snterm
         (Gram.Entry.obj (decl_notation : 'decl_notation Gram.Entry.e))],
      Gramext.action
        (fun (ntn : 'decl_notation) (pri : 'e__11 option)
             (bd : 'record_binder) (loc : Ploc.t) ->
           ((bd, pri), ntn : 'record_field))]];
  Gram.extend (record_fields : 'record_fields Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> ([] : 'record_fields));
      [Gramext.Snterm
         (Gram.Entry.obj (record_field : 'record_field Gram.Entry.e))],
      Gramext.action
        (fun (f : 'record_field) (loc : Ploc.t) -> ([f] : 'record_fields));
      [Gramext.Snterm
         (Gram.Entry.obj (record_field : 'record_field Gram.Entry.e));
       Gramext.Stoken ("", ";")],
      Gramext.action
        (fun _ (f : 'record_field) (loc : Ploc.t) -> ([f] : 'record_fields));
      [Gramext.Snterm
         (Gram.Entry.obj (record_field : 'record_field Gram.Entry.e));
       Gramext.Stoken ("", ";"); Gramext.Sself],
      Gramext.action
        (fun (fs : 'record_fields) _ (f : 'record_field) (loc : Ploc.t) ->
           (f :: fs : 'record_fields))]];
  Gram.extend (record_binder_body : 'record_binder_body Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (binders : 'binders Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
      Gramext.action
        (fun (b : 'lconstr) _ (l : 'binders) (loc : Ploc.t) ->
           (fun id ->
              match b.CAst.v with
                CCast (b', (CastConv t (* | CastVM t | CastNative t *))) ->
                  None,
                  DefExpr
                    (id, mkCLambdaN ~loc:((!@) loc) l b',
                     Some (mkCProdN ~loc:((!@) loc) l t))
              | _ ->
                  None, DefExpr (id, mkCLambdaN ~loc:((!@) loc) l b, None) :
            'record_binder_body));
      [Gramext.Snterm (Gram.Entry.obj (binders : 'binders Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj
            (of_type_with_opt_coercion :
             'of_type_with_opt_coercion Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
      Gramext.action
        (fun (b : 'lconstr) _ (t : 'lconstr) (oc : 'of_type_with_opt_coercion)
             (l : 'binders) (loc : Ploc.t) ->
           (fun id ->
              oc,
              DefExpr
                (id, mkCLambdaN ~loc:((!@) loc) l b,
                 Some (mkCProdN ~loc:((!@) loc) l t)) :
            'record_binder_body));
      [Gramext.Snterm (Gram.Entry.obj (binders : 'binders Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj
            (of_type_with_opt_coercion :
             'of_type_with_opt_coercion Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
      Gramext.action
        (fun (t : 'lconstr) (oc : 'of_type_with_opt_coercion) (l : 'binders)
             (loc : Ploc.t) ->
           (fun id -> oc, AssumExpr (id, mkCProdN ~loc:((!@) loc) l t) :
            'record_binder_body))]];
  Gram.extend (record_binder : 'record_binder Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj
            (record_binder_body : 'record_binder_body Gram.Entry.e))],
      Gramext.action
        (fun (f : 'record_binder_body) (id : 'name) (loc : Ploc.t) ->
           (f id : 'record_binder));
      [Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e))],
      Gramext.action
        (fun (id : 'name) (loc : Ploc.t) ->
           (None,
            AssumExpr
              (id,
               (@@) (CAst.make ~loc:((!@) loc))
                 (CHole (None, Misctypes.IntroAnonymous, None))) :
            'record_binder))]];
  Gram.extend (assum_list : 'assum_list Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj
            (simple_assum_coe : 'simple_assum_coe Gram.Entry.e))],
      Gramext.action
        (fun (b : 'simple_assum_coe) (loc : Ploc.t) -> ([b] : 'assum_list));
      [Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (assum_coe : 'assum_coe Gram.Entry.e)))],
      Gramext.action
        (fun (bl : 'assum_coe list) (loc : Ploc.t) -> (bl : 'assum_list))]];
  Gram.extend (assum_coe : 'assum_coe Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "(");
       Gramext.Snterm
         (Gram.Entry.obj (simple_assum_coe : 'simple_assum_coe Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (a : 'simple_assum_coe) _ (loc : Ploc.t) ->
           (a : 'assum_coe))]];
  Gram.extend (simple_assum_coe : 'simple_assum_coe Gram.Entry.e) None
    [None, None,
     [[Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (ident_decl : 'ident_decl Gram.Entry.e)));
       Gramext.Snterm
         (Gram.Entry.obj
            (of_type_with_opt_coercion :
             'of_type_with_opt_coercion Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'lconstr) (oc : 'of_type_with_opt_coercion)
             (idl : 'ident_decl list) (loc : Ploc.t) ->
           (not (Option.is_empty oc), (idl, c) : 'simple_assum_coe))]];
  Gram.extend (constructor_type : 'constructor_type Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (binders : 'binders Gram.Entry.e));
       Gramext.srules
         [[],
          Gramext.action
            (fun (loc : Ploc.t) ->
               (fun l id ->
                  false,
                  (id,
                   mkCProdN ~loc:((!@) loc) l
                     ((@@) (CAst.make ~loc:((!@) loc))
                        (CHole (None, Misctypes.IntroAnonymous, None)))) :
                'e__12));
          [Gramext.Snterm
             (Gram.Entry.obj
                (of_type_with_opt_coercion :
                 'of_type_with_opt_coercion Gram.Entry.e));
           Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
          Gramext.action
            (fun (c : 'lconstr) (coe : 'of_type_with_opt_coercion)
                 (loc : Ploc.t) ->
               (fun l id ->
                  not (Option.is_empty coe),
                  (id, mkCProdN ~loc:((!@) loc) l c) :
                'e__12))]],
      Gramext.action
        (fun (t : 'e__12) (l : 'binders) (loc : Ploc.t) ->
           (t l : 'constructor_type))]];
  Gram.extend (constructor : 'constructor Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj
            (constructor_type : 'constructor_type Gram.Entry.e))],
      Gramext.action
        (fun (c : 'constructor_type) (id : 'identref) (loc : Ploc.t) ->
           (c id : 'constructor))]];
  Gram.extend
    (of_type_with_opt_coercion : 'of_type_with_opt_coercion Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", ":")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (None : 'of_type_with_opt_coercion));
      [Gramext.Stoken ("", ":"); Gramext.Stoken ("", ">")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) -> (Some true : 'of_type_with_opt_coercion));
      [Gramext.Stoken ("", ":"); Gramext.Stoken ("", ">");
       Gramext.Stoken ("", ">")],
      Gramext.action
        (fun _ _ _ (loc : Ploc.t) ->
           (Some false : 'of_type_with_opt_coercion));
      [Gramext.Stoken ("", ":>")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (Some true : 'of_type_with_opt_coercion));
      [Gramext.Stoken ("", ":>"); Gramext.Stoken ("", ">")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) -> (Some false : 'of_type_with_opt_coercion));
      [Gramext.Stoken ("", ":>>")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (Some false : 'of_type_with_opt_coercion))]]

let only_starredidentrefs =
  Gram.Entry.of_parser "test_only_starredidentrefs"
    (fun strm ->
       let rec aux n =
         match Util.stream_nth n strm with
           KEYWORD "." -> ()
         | KEYWORD ")" -> ()
         | IDENT _ | KEYWORD "Type" | KEYWORD "*" -> aux (n + 1)
         | _ -> raise Stream.Failure
       in
       aux 0)
let starredidentreflist_to_expr l =
  match l with
    [] -> SsEmpty
  | x :: xs -> List.fold_right (fun i acc -> SsUnion (i, acc)) xs x

let warn_deprecated_include_type =
  CWarnings.create ~name:"deprecated-include-type" ~category:"deprecated"
    (fun () -> strbrk "Include Type is deprecated; use Include instead")

(* Modules and Sections *)
let _ =
  let _ = (gallina_ext : 'gallina_ext Gram.Entry.e)
  and _ = (module_expr : 'module_expr Gram.Entry.e)
  and _ = (module_type : 'module_type Gram.Entry.e)
  and _ = (section_subset_expr : 'section_subset_expr Gram.Entry.e) in
  let grammar_entry_create = Gram.Entry.create in
  let export_token : 'export_token Gram.Entry.e =
    grammar_entry_create "export_token"
  and ext_module_type : 'ext_module_type Gram.Entry.e =
    grammar_entry_create "ext_module_type"
  and ext_module_expr : 'ext_module_expr Gram.Entry.e =
    grammar_entry_create "ext_module_expr"
  and check_module_type : 'check_module_type Gram.Entry.e =
    grammar_entry_create "check_module_type"
  and check_module_types : 'check_module_types Gram.Entry.e =
    grammar_entry_create "check_module_types"
  and of_module_type : 'of_module_type Gram.Entry.e =
    grammar_entry_create "of_module_type"
  and is_module_type : 'is_module_type Gram.Entry.e =
    grammar_entry_create "is_module_type"
  and is_module_expr : 'is_module_expr Gram.Entry.e =
    grammar_entry_create "is_module_expr"
  and functor_app_annot : 'functor_app_annot Gram.Entry.e =
    grammar_entry_create "functor_app_annot"
  and module_expr_inl : 'module_expr_inl Gram.Entry.e =
    grammar_entry_create "module_expr_inl"
  and module_type_inl : 'module_type_inl Gram.Entry.e =
    grammar_entry_create "module_type_inl"
  and module_binder : 'module_binder Gram.Entry.e =
    (* Module binder  *)
    grammar_entry_create "module_binder"
  and module_expr_atom : 'module_expr_atom Gram.Entry.e =
    grammar_entry_create "module_expr_atom"
  and with_declaration : 'with_declaration Gram.Entry.e =
    grammar_entry_create "with_declaration"
  and starredidentref : 'starredidentref Gram.Entry.e =
    grammar_entry_create "starredidentref"
  and ssexpr : 'ssexpr Gram.Entry.e = grammar_entry_create "ssexpr" in
  Gram.extend (gallina_ext : 'gallina_ext Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "Include"); Gramext.Stoken ("", "Type");
       Gramext.Snterm
         (Gram.Entry.obj (module_type_inl : 'module_type_inl Gram.Entry.e));
       Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj
               (ext_module_type : 'ext_module_type Gram.Entry.e)))],
      Gramext.action
        (fun (l : 'ext_module_type list) (e : 'module_type_inl) _ _
             (loc : Ploc.t) ->
           (warn_deprecated_include_type ~loc:((!@) loc) ();
            VernacInclude (e :: l) :
            'gallina_ext));
      [Gramext.Stoken ("IDENT", "Include");
       Gramext.Snterm
         (Gram.Entry.obj (module_type_inl : 'module_type_inl Gram.Entry.e));
       Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj
               (ext_module_expr : 'ext_module_expr Gram.Entry.e)))],
      Gramext.action
        (fun (l : 'ext_module_expr list) (e : 'module_type_inl) _
             (loc : Ploc.t) ->
           (VernacInclude (e :: l) : 'gallina_ext));
      [Gramext.Stoken ("IDENT", "Export");
       Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e)))],
      Gramext.action
        (fun (qidl : 'global list) _ (loc : Ploc.t) ->
           (VernacImport (true, qidl) : 'gallina_ext));
      [Gramext.Stoken ("IDENT", "Import");
       Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e)))],
      Gramext.action
        (fun (qidl : 'global list) _ (loc : Ploc.t) ->
           (VernacImport (false, qidl) : 'gallina_ext));
      [Gramext.Stoken ("IDENT", "From");
       Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e));
       Gramext.Stoken ("IDENT", "Require");
       Gramext.Snterm
         (Gram.Entry.obj (export_token : 'export_token Gram.Entry.e));
       Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e)))],
      Gramext.action
        (fun (qidl : 'global list) (export : 'export_token) _ (ns : 'global) _
             (loc : Ploc.t) ->
           (VernacRequire (Some ns, export, qidl) : 'gallina_ext));
      [Gramext.Stoken ("IDENT", "Require");
       Gramext.Snterm
         (Gram.Entry.obj (export_token : 'export_token Gram.Entry.e));
       Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e)))],
      Gramext.action
        (fun (qidl : 'global list) (export : 'export_token) _
             (loc : Ploc.t) ->
           (VernacRequire (None, export, qidl) : 'gallina_ext));
      [Gramext.Stoken ("IDENT", "Collection");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm
         (Gram.Entry.obj
            (section_subset_expr : 'section_subset_expr Gram.Entry.e))],
      Gramext.action
        (fun (expr : 'section_subset_expr) _ (id : 'identref) _
             (loc : Ploc.t) ->
           (VernacNameSectionHypSet (id, expr) : 'gallina_ext));
      [Gramext.Stoken ("IDENT", "End");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e))],
      Gramext.action
        (fun (id : 'identref) _ (loc : Ploc.t) ->
           (VernacEndSegment id : 'gallina_ext));
      [Gramext.Stoken ("IDENT", "Chapter");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e))],
      Gramext.action
        (fun (id : 'identref) _ (loc : Ploc.t) ->
           (VernacBeginSection id : 'gallina_ext));
      [Gramext.Stoken ("IDENT", "Section");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e))],
      Gramext.action
        (fun (id : 'identref) _ (loc : Ploc.t) ->
           (VernacBeginSection id : 'gallina_ext));
      [Gramext.Stoken ("IDENT", "Declare");
       Gramext.Stoken ("IDENT", "Module");
       Gramext.Snterm
         (Gram.Entry.obj (export_token : 'export_token Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj (module_binder : 'module_binder Gram.Entry.e)));
       Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Gram.Entry.obj (module_type_inl : 'module_type_inl Gram.Entry.e))],
      Gramext.action
        (fun (mty : 'module_type_inl) _ (bl : 'module_binder list)
             (id : 'identref) (export : 'export_token) _ _ (loc : Ploc.t) ->
           (VernacDeclareModule (export, id, bl, mty) : 'gallina_ext));
      [Gramext.Stoken ("IDENT", "Module"); Gramext.Stoken ("", "Type");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj (module_binder : 'module_binder Gram.Entry.e)));
       Gramext.Snterm
         (Gram.Entry.obj
            (check_module_types : 'check_module_types Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (is_module_type : 'is_module_type Gram.Entry.e))],
      Gramext.action
        (fun (body : 'is_module_type) (sign : 'check_module_types)
             (bl : 'module_binder list) (id : 'identref) _ _ (loc : Ploc.t) ->
           (VernacDeclareModuleType (id, bl, sign, body) : 'gallina_ext));
      [(* Interactive module declaration *)
       Gramext.
       Stoken
         ("IDENT", "Module");
       Gramext.Snterm
         (Gram.Entry.obj (export_token : 'export_token Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj (module_binder : 'module_binder Gram.Entry.e)));
       Gramext.Snterm
         (Gram.Entry.obj (of_module_type : 'of_module_type Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (is_module_expr : 'is_module_expr Gram.Entry.e))],
      Gramext.action
        (fun (body : 'is_module_expr) (sign : 'of_module_type)
             (bl : 'module_binder list) (id : 'identref)
             (export : 'export_token) _ (loc : Ploc.t) ->
           (VernacDefineModule (export, id, bl, sign, body) :
            'gallina_ext))]];
  Gram.extend (export_token : 'export_token Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> (None : 'export_token));
      [Gramext.Stoken ("IDENT", "Export")],
      Gramext.action (fun _ (loc : Ploc.t) -> (Some true : 'export_token));
      [Gramext.Stoken ("IDENT", "Import")],
      Gramext.action (fun _ (loc : Ploc.t) -> (Some false : 'export_token))]];
  Gram.extend (ext_module_type : 'ext_module_type Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "<+");
       Gramext.Snterm
         (Gram.Entry.obj (module_type_inl : 'module_type_inl Gram.Entry.e))],
      Gramext.action
        (fun (mty : 'module_type_inl) _ (loc : Ploc.t) ->
           (mty : 'ext_module_type))]];
  Gram.extend (ext_module_expr : 'ext_module_expr Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "<+");
       Gramext.Snterm
         (Gram.Entry.obj (module_expr_inl : 'module_expr_inl Gram.Entry.e))],
      Gramext.action
        (fun (mexpr : 'module_expr_inl) _ (loc : Ploc.t) ->
           (mexpr : 'ext_module_expr))]];
  Gram.extend (check_module_type : 'check_module_type Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "<:");
       Gramext.Snterm
         (Gram.Entry.obj (module_type_inl : 'module_type_inl Gram.Entry.e))],
      Gramext.action
        (fun (mty : 'module_type_inl) _ (loc : Ploc.t) ->
           (mty : 'check_module_type))]];
  Gram.extend (check_module_types : 'check_module_types Gram.Entry.e) None
    [None, None,
     [[Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj
               (check_module_type : 'check_module_type Gram.Entry.e)))],
      Gramext.action
        (fun (mtys : 'check_module_type list) (loc : Ploc.t) ->
           (mtys : 'check_module_types))]];
  Gram.extend (of_module_type : 'of_module_type Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj
            (check_module_types : 'check_module_types Gram.Entry.e))],
      Gramext.action
        (fun (mtys : 'check_module_types) (loc : Ploc.t) ->
           (Check mtys : 'of_module_type));
      [Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Gram.Entry.obj (module_type_inl : 'module_type_inl Gram.Entry.e))],
      Gramext.action
        (fun (mty : 'module_type_inl) _ (loc : Ploc.t) ->
           (Enforce mty : 'of_module_type))]];
  Gram.extend (is_module_type : 'is_module_type Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> ([] : 'is_module_type));
      [Gramext.Stoken ("", ":=");
       Gramext.Snterm
         (Gram.Entry.obj (module_type_inl : 'module_type_inl Gram.Entry.e));
       Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj
               (ext_module_type : 'ext_module_type Gram.Entry.e)))],
      Gramext.action
        (fun (l : 'ext_module_type list) (mty : 'module_type_inl) _
             (loc : Ploc.t) ->
           (mty :: l : 'is_module_type))]];
  Gram.extend (is_module_expr : 'is_module_expr Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> ([] : 'is_module_expr));
      [Gramext.Stoken ("", ":=");
       Gramext.Snterm
         (Gram.Entry.obj (module_expr_inl : 'module_expr_inl Gram.Entry.e));
       Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj
               (ext_module_expr : 'ext_module_expr Gram.Entry.e)))],
      Gramext.action
        (fun (l : 'ext_module_expr list) (mexpr : 'module_expr_inl) _
             (loc : Ploc.t) ->
           (mexpr :: l : 'is_module_expr))]];
  Gram.extend (functor_app_annot : 'functor_app_annot Gram.Entry.e) None
    [None, None,
     [[],
      Gramext.action
        (fun (loc : Ploc.t) -> (DefaultInline : 'functor_app_annot));
      [Gramext.Stoken ("", "["); Gramext.Stoken ("IDENT", "no");
       Gramext.Stoken ("IDENT", "inline"); Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ _ _ _ (loc : Ploc.t) -> (NoInline : 'functor_app_annot));
      [Gramext.Stoken ("", "["); Gramext.Stoken ("IDENT", "inline");
       Gramext.Stoken ("", "at"); Gramext.Stoken ("IDENT", "level");
       Gramext.Stoken ("INT", ""); Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (i : string) _ _ _ _ (loc : Ploc.t) ->
           (InlineAt (int_of_string i) : 'functor_app_annot))]];
  Gram.extend (module_expr_inl : 'module_expr_inl Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (module_expr : 'module_expr Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj
            (functor_app_annot : 'functor_app_annot Gram.Entry.e))],
      Gramext.action
        (fun (a : 'functor_app_annot) (me : 'module_expr) (loc : Ploc.t) ->
           (me, a : 'module_expr_inl));
      [Gramext.Stoken ("", "!");
       Gramext.Snterm
         (Gram.Entry.obj (module_expr : 'module_expr Gram.Entry.e))],
      Gramext.action
        (fun (me : 'module_expr) _ (loc : Ploc.t) ->
           (me, NoInline : 'module_expr_inl))]];
  Gram.extend (module_type_inl : 'module_type_inl Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (module_type : 'module_type Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj
            (functor_app_annot : 'functor_app_annot Gram.Entry.e))],
      Gramext.action
        (fun (a : 'functor_app_annot) (me : 'module_type) (loc : Ploc.t) ->
           (me, a : 'module_type_inl));
      [Gramext.Stoken ("", "!");
       Gramext.Snterm
         (Gram.Entry.obj (module_type : 'module_type Gram.Entry.e))],
      Gramext.action
        (fun (me : 'module_type) _ (loc : Ploc.t) ->
           (me, NoInline : 'module_type_inl))]];
  Gram.extend (module_binder : 'module_binder Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "(");
       Gramext.Snterm
         (Gram.Entry.obj (export_token : 'export_token Gram.Entry.e));
       Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (identref : 'identref Gram.Entry.e)));
       Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Gram.Entry.obj (module_type_inl : 'module_type_inl Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (mty : 'module_type_inl) _ (idl : 'identref list)
             (export : 'export_token) _ (loc : Ploc.t) ->
           (export, idl, mty : 'module_binder))]];
  Gram.extend (module_expr : 'module_expr Gram.Entry.e) None
    [None, None,
     [[Gramext.Sself;
       Gramext.Snterm
         (Gram.Entry.obj
            (module_expr_atom : 'module_expr_atom Gram.Entry.e))],
      Gramext.action
        (fun (me2 : 'module_expr_atom) (me1 : 'module_expr) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CMapply (me1, me2)) :
            'module_expr));
      [Gramext.Snterm
         (Gram.Entry.obj
            (module_expr_atom : 'module_expr_atom Gram.Entry.e))],
      Gramext.action
        (fun (me : 'module_expr_atom) (loc : Ploc.t) ->
           (me : 'module_expr))]];
  Gram.extend (module_expr_atom : 'module_expr_atom Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "(");
       Gramext.Snterm
         (Gram.Entry.obj (module_expr : 'module_expr Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (me : 'module_expr) _ (loc : Ploc.t) ->
           (me : 'module_expr_atom));
      [Gramext.Snterm (Gram.Entry.obj (qualid : 'qualid Gram.Entry.e))],
      Gramext.action
        (fun (qid : 'qualid) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CMident qid.CAst.v) :
            'module_expr_atom))]];
  Gram.extend (with_declaration : 'with_declaration Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "Module");
       Gramext.Snterm
         (Gram.Entry.obj (fullyqualid : 'fullyqualid Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm (Gram.Entry.obj (qualid : 'qualid Gram.Entry.e))],
      Gramext.action
        (fun (qid : 'qualid) _ (fqid : 'fullyqualid) _ (loc : Ploc.t) ->
           (CWith_Module (fqid, qid) : 'with_declaration));
      [Gramext.Stoken ("", "Definition");
       Gramext.Snterm
         (Gram.Entry.obj (fullyqualid : 'fullyqualid Gram.Entry.e));
       Gramext.Sopt
         (Gramext.Snterm
            (Gram.Entry.obj (univ_decl : 'univ_decl Gram.Entry.e)));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm
         (Gram.Entry.obj (Constr.lconstr : 'Constr__lconstr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'Constr__lconstr) _ (udecl : 'univ_decl option)
             (fqid : 'fullyqualid) _ (loc : Ploc.t) ->
           (CWith_Definition (fqid, udecl, c) : 'with_declaration))]];
  Gram.extend (module_type : 'module_type Gram.Entry.e) None
    [None, None,
     [[Gramext.Sself; Gramext.Stoken ("", "with");
       Gramext.Snterm
         (Gram.Entry.obj
            (with_declaration : 'with_declaration Gram.Entry.e))],
      Gramext.action
        (fun (decl : 'with_declaration) _ (mty : 'module_type)
             (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CMwith (mty, decl)) :
            'module_type));
      [Gramext.Sself;
       Gramext.Snterm
         (Gram.Entry.obj
            (module_expr_atom : 'module_expr_atom Gram.Entry.e))],
      Gramext.action
        (fun (me : 'module_expr_atom) (mty : 'module_type) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CMapply (mty, me)) :
            'module_type));
      [Gramext.Stoken ("", "("); Gramext.Sself; Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (mt : 'module_type) _ (loc : Ploc.t) -> (mt : 'module_type));
      [Gramext.Snterm (Gram.Entry.obj (qualid : 'qualid Gram.Entry.e))],
      Gramext.action
        (fun (qid : 'qualid) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (CMident qid.CAst.v) :
            'module_type))]];
  Gram.extend (section_subset_expr : 'section_subset_expr Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (ssexpr : 'ssexpr Gram.Entry.e))],
      Gramext.action
        (fun (e : 'ssexpr) (loc : Ploc.t) -> (e : 'section_subset_expr));
      [Gramext.Snterm
         (Gram.Entry.obj
            (only_starredidentrefs : 'only_starredidentrefs Gram.Entry.e));
       Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj
               (starredidentref : 'starredidentref Gram.Entry.e)))],
      Gramext.action
        (fun (l : 'starredidentref list) _ (loc : Ploc.t) ->
           (starredidentreflist_to_expr l : 'section_subset_expr))]];
  Gram.extend (starredidentref : 'starredidentref Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "Type"); Gramext.Stoken ("", "*")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) -> (SsFwdClose SsType : 'starredidentref));
      [Gramext.Stoken ("", "Type")],
      Gramext.action (fun _ (loc : Ploc.t) -> (SsType : 'starredidentref));
      [Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Stoken ("", "*")],
      Gramext.action
        (fun _ (i : 'identref) (loc : Ploc.t) ->
           (SsFwdClose (SsSingl i) : 'starredidentref));
      [Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e))],
      Gramext.action
        (fun (i : 'identref) (loc : Ploc.t) ->
           (SsSingl i : 'starredidentref))]];
  Gram.extend (ssexpr : 'ssexpr Gram.Entry.e) None
    [Some "35", None,
     [[Gramext.Stoken ("", "-"); Gramext.Sself],
      Gramext.action
        (fun (e : 'ssexpr) _ (loc : Ploc.t) -> (SsCompl e : 'ssexpr))];
     Some "50", None,
     [[Gramext.Sself; Gramext.Stoken ("", "+"); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'ssexpr) _ (e1 : 'ssexpr) (loc : Ploc.t) ->
           (SsUnion (e1, e2) : 'ssexpr));
      [Gramext.Sself; Gramext.Stoken ("", "-"); Gramext.Sself],
      Gramext.action
        (fun (e2 : 'ssexpr) _ (e1 : 'ssexpr) (loc : Ploc.t) ->
           (SsSubstr (e1, e2) : 'ssexpr))];
     Some "0", None,
     [[Gramext.Stoken ("", "("); Gramext.Sself; Gramext.Stoken ("", ")");
       Gramext.Stoken ("", "*")],
      Gramext.action
        (fun _ _ (e : 'ssexpr) _ (loc : Ploc.t) -> (SsFwdClose e : 'ssexpr));
      [Gramext.Stoken ("", "("); Gramext.Sself; Gramext.Stoken ("", ")")],
      Gramext.action (fun _ (e : 'ssexpr) _ (loc : Ploc.t) -> (e : 'ssexpr));
      [Gramext.Stoken ("", "(");
       Gramext.Snterm
         (Gram.Entry.obj
            (only_starredidentrefs : 'only_starredidentrefs Gram.Entry.e));
       Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj
               (starredidentref : 'starredidentref Gram.Entry.e)));
       Gramext.Stoken ("", ")"); Gramext.Stoken ("", "*")],
      Gramext.action
        (fun _ _ (l : 'starredidentref list) _ _ (loc : Ploc.t) ->
           (SsFwdClose (starredidentreflist_to_expr l) : 'ssexpr));
      [Gramext.Stoken ("", "(");
       Gramext.Snterm
         (Gram.Entry.obj
            (only_starredidentrefs : 'only_starredidentrefs Gram.Entry.e));
       Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj
               (starredidentref : 'starredidentref Gram.Entry.e)));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (l : 'starredidentref list) _ _ (loc : Ploc.t) ->
           (starredidentreflist_to_expr l : 'ssexpr));
      [Gramext.Snterm
         (Gram.Entry.obj (starredidentref : 'starredidentref Gram.Entry.e))],
      Gramext.action
        (fun (i : 'starredidentref) (loc : Ploc.t) -> (i : 'ssexpr))]]

let warn_deprecated_arguments_scope =
  CWarnings.create ~name:"deprecated-arguments-scope" ~category:"deprecated"
    (fun () -> strbrk "Arguments Scope is deprecated; use Arguments instead")

let warn_deprecated_implicit_arguments =
  CWarnings.create ~name:"deprecated-implicit-arguments"
    ~category:"deprecated"
    (fun () ->
       strbrk "Implicit Arguments is deprecated; use Arguments instead")

(* Extensions: implicits, coercions, etc. *)
let _ =
  let _ = (gallina_ext : 'gallina_ext Gram.Entry.e)
  and _ = (instance_name : 'instance_name Gram.Entry.e)
  and _ = (hint_info : 'hint_info Gram.Entry.e) in
  let grammar_entry_create = Gram.Entry.create in
  let arguments_modifier : 'arguments_modifier Gram.Entry.e =
    grammar_entry_create "arguments_modifier"
  and implicit_name : 'implicit_name Gram.Entry.e =
    grammar_entry_create "implicit_name"
  and scope : 'scope Gram.Entry.e = grammar_entry_create "scope"
  and argument_spec : 'argument_spec Gram.Entry.e =
    grammar_entry_create "argument_spec"
  and argument_spec_block : 'argument_spec_block Gram.Entry.e =
    (* List of arguments implicit status, scope, modifiers *)
    grammar_entry_create "argument_spec_block"
  and more_implicits_block : 'more_implicits_block Gram.Entry.e =
    (* Same as [argument_spec_block], but with only implicit status and names *)
    grammar_entry_create "more_implicits_block"
  and strategy_level : 'strategy_level Gram.Entry.e =
    grammar_entry_create "strategy_level"
  and reserv_list : 'reserv_list Gram.Entry.e =
    grammar_entry_create "reserv_list"
  and reserv_tuple : 'reserv_tuple Gram.Entry.e =
    grammar_entry_create "reserv_tuple"
  and simple_reserv : 'simple_reserv Gram.Entry.e =
    grammar_entry_create "simple_reserv"
  in
  Gram.extend (gallina_ext : 'gallina_ext Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "Generalizable");
       Gramext.srules
         [[Gramext.srules
             [[Gramext.Stoken ("IDENT", "Variables")],
              Gramext.action
                (fun (x : string) (loc : Ploc.t) -> (x : 'e__22));
              [Gramext.Stoken ("", "Variable")],
              Gramext.action
                (fun (x : string) (loc : Ploc.t) -> (x : 'e__22))];
           Gramext.Slist1
             (Gramext.Snterm
                (Gram.Entry.obj (identref : 'identref Gram.Entry.e)))],
          Gramext.action
            (fun (idl : 'identref list) _ (loc : Ploc.t) ->
               (Some idl : 'e__23));
          [Gramext.Stoken ("IDENT", "No");
           Gramext.Stoken ("IDENT", "Variables")],
          Gramext.action (fun _ _ (loc : Ploc.t) -> (None : 'e__23));
          [Gramext.Stoken ("IDENT", "All");
           Gramext.Stoken ("IDENT", "Variables")],
          Gramext.action (fun _ _ (loc : Ploc.t) -> (Some [] : 'e__23))]],
      Gramext.action
        (fun (gen : 'e__23) _ (loc : Ploc.t) ->
           (VernacGeneralizable gen : 'gallina_ext));
      [Gramext.Stoken ("IDENT", "Implicit");
       Gramext.Stoken ("IDENT", "Types");
       Gramext.Snterm
         (Gram.Entry.obj (reserv_list : 'reserv_list Gram.Entry.e))],
      Gramext.action
        (fun (bl : 'reserv_list) _ _ (loc : Ploc.t) ->
           (test_plural_form_types loc "Implicit Types" bl; VernacReserve bl :
            'gallina_ext));
      [Gramext.Stoken ("IDENT", "Implicit"); Gramext.Stoken ("", "Type");
       Gramext.Snterm
         (Gram.Entry.obj (reserv_list : 'reserv_list Gram.Entry.e))],
      Gramext.action
        (fun (bl : 'reserv_list) _ _ (loc : Ploc.t) ->
           (VernacReserve bl : 'gallina_ext));
      [Gramext.Stoken ("IDENT", "Implicit");
       Gramext.Stoken ("IDENT", "Arguments");
       Gramext.Snterm
         (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e));
       Gramext.Slist0
         (Gramext.srules
            [[Gramext.Stoken ("", "[");
              Gramext.Slist0
                (Gramext.Snterm
                   (Gram.Entry.obj
                      (implicit_name : 'implicit_name Gram.Entry.e)));
              Gramext.Stoken ("", "]")],
             Gramext.action
               (fun _ (l : 'implicit_name list) _ (loc : Ploc.t) ->
                  (List.map (fun (id, b, f) -> ExplByName id, b, f) l :
                   'e__21))])],
      Gramext.action
        (fun (pos : 'e__21 list) (qid : 'smart_global) _ _ (loc : Ploc.t) ->
           (warn_deprecated_implicit_arguments ~loc:((!@) loc) ();
            VernacDeclareImplicits (qid, pos) :
            'gallina_ext));
      [Gramext.Stoken ("IDENT", "Arguments");
       Gramext.Stoken ("IDENT", "Scope");
       Gramext.Snterm
         (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e));
       Gramext.Stoken ("", "[");
       Gramext.Slist0
         (Gramext.srules
            [[Gramext.Stoken ("IDENT", "")],
             Gramext.action
               (fun (sc : string) (loc : Ploc.t) -> (Some sc : 'e__20));
             [Gramext.Stoken ("", "_")],
             Gramext.action (fun _ (loc : Ploc.t) -> (None : 'e__20))]);
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (scl : 'e__20 list) _ (qid : 'smart_global) _ _
             (loc : Ploc.t) ->
           (warn_deprecated_arguments_scope ~loc:((!@) loc) ();
            VernacArgumentsScope (qid, scl) :
            'gallina_ext));
      [Gramext.Stoken ("IDENT", "Arguments");
       Gramext.Snterm
         (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e));
       Gramext.Slist0
         (Gramext.Snterm
            (Gram.Entry.obj
               (argument_spec_block : 'argument_spec_block Gram.Entry.e)));
       Gramext.Sopt
         (Gramext.srules
            [[Gramext.Stoken ("", ",");
              Gramext.Slist1sep
                (Gramext.srules
                   [[Gramext.Slist0
                       (Gramext.Snterm
                          (Gram.Entry.obj
                             (more_implicits_block :
                              'more_implicits_block Gram.Entry.e)))],
                    Gramext.action
                      (fun (impl : 'more_implicits_block list)
                           (loc : Ploc.t) ->
                         (List.flatten impl : 'e__17))],
                 Gramext.Stoken ("", ","), false)],
             Gramext.action
               (fun (impl : 'e__17 list) _ (loc : Ploc.t) ->
                  (impl : 'e__18))]);
       Gramext.Sopt
         (Gramext.srules
            [[Gramext.Stoken ("", ":");
              Gramext.Slist1sep
                (Gramext.Snterm
                   (Gram.Entry.obj
                      (arguments_modifier :
                       'arguments_modifier Gram.Entry.e)),
                 Gramext.Stoken ("", ","), false)],
             Gramext.action
               (fun (l : 'arguments_modifier list) _ (loc : Ploc.t) ->
                  (l : 'e__19))])],
      Gramext.action
        (fun (mods : 'e__19 option) (more_implicits : 'e__18 option)
             (args : 'argument_spec_block list) (qid : 'smart_global) _
             (loc : Ploc.t) ->
           (let mods =
              match mods with
                None -> []
              | Some l -> List.flatten l
            in
            let slash_position = ref None in
            let rec parse_args i =
              function
                [] -> []
              | `Id x :: args -> x :: parse_args (i + 1) args
              | `Slash :: args ->
                  if Option.is_empty !slash_position then
                    begin slash_position := Some i; parse_args i args end
                  else
                    user_err Pp.(str "The \"/\" modifier can occur only once")
            in
            let args = parse_args 0 (List.flatten args) in
            let more_implicits = Option.default [] more_implicits in
            VernacArguments
              (qid, args, more_implicits, !slash_position, mods) :
            'gallina_ext));
      [Gramext.Stoken ("IDENT", "Existing");
       Gramext.Stoken ("IDENT", "Class");
       Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e))],
      Gramext.action
        (fun (is : 'global) _ _ (loc : Ploc.t) ->
           (VernacDeclareClass is : 'gallina_ext));
      [Gramext.Stoken ("IDENT", "Existing");
       Gramext.Stoken ("IDENT", "Instances");
       Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e)));
       Gramext.Sopt
         (Gramext.srules
            [[Gramext.Stoken ("", "|");
              Gramext.Snterm
                (Gram.Entry.obj (natural : 'natural Gram.Entry.e))],
             Gramext.action
               (fun (i : 'natural) _ (loc : Ploc.t) -> (i : 'e__16))])],
      Gramext.action
        (fun (pri : 'e__16 option) (ids : 'global list) _ _ (loc : Ploc.t) ->
           (let info = {hint_priority = pri; hint_pattern = None} in
            let insts = List.map (fun i -> i, info) ids in
            VernacDeclareInstances insts :
            'gallina_ext));
      [Gramext.Stoken ("IDENT", "Existing");
       Gramext.Stoken ("IDENT", "Instance");
       Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (hint_info : 'hint_info Gram.Entry.e))],
      Gramext.action
        (fun (info : 'hint_info) (id : 'global) _ _ (loc : Ploc.t) ->
           (VernacDeclareInstances [id, info] : 'gallina_ext));
      [Gramext.Stoken ("IDENT", "Instance");
       Gramext.Snterm
         (Gram.Entry.obj (instance_name : 'instance_name Gram.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.srules
         [[],
          Gramext.action
            (fun (loc : Ploc.t) -> (Decl_kinds.Explicit : 'e__14));
          [Gramext.Stoken ("", "!")],
          Gramext.action
            (fun _ (loc : Ploc.t) -> (Decl_kinds.Implicit : 'e__14))];
       Gramext.Snterml
         (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200");
       Gramext.Snterm (Gram.Entry.obj (hint_info : 'hint_info Gram.Entry.e));
       Gramext.srules
         [[], Gramext.action (fun (loc : Ploc.t) -> (None : 'e__15));
          [Gramext.Stoken ("", ":=");
           Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
          Gramext.action
            (fun (c : 'lconstr) _ (loc : Ploc.t) ->
               (Some (false, c) : 'e__15));
          [Gramext.Stoken ("", ":="); Gramext.Stoken ("", "{");
           Gramext.Snterm
             (Gram.Entry.obj
                (record_declaration : 'record_declaration Gram.Entry.e));
           Gramext.Stoken ("", "}")],
          Gramext.action
            (fun _ (r : 'record_declaration) _ _ (loc : Ploc.t) ->
               (Some (true, r) : 'e__15))]],
      Gramext.action
        (fun (props : 'e__15) (info : 'hint_info) (t : 'operconstr)
             (expl : 'e__14) _ (namesup : 'instance_name) _ (loc : Ploc.t) ->
           (VernacInstance
              (false, snd namesup, (fst namesup, expl, t), props, info) :
            'gallina_ext));
      [Gramext.Stoken ("IDENT", "Context");
       Gramext.Snterm (Gram.Entry.obj (binders : 'binders Gram.Entry.e))],
      Gramext.action
        (fun (c : 'binders) _ (loc : Ploc.t) ->
           (VernacContext c : 'gallina_ext));
      [Gramext.Stoken ("IDENT", "Coercion");
       Gramext.Snterm
         (Gram.Entry.obj (by_notation : 'by_notation Gram.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Gram.Entry.obj (class_rawexpr : 'class_rawexpr Gram.Entry.e));
       Gramext.Stoken ("", ">->");
       Gramext.Snterm
         (Gram.Entry.obj (class_rawexpr : 'class_rawexpr Gram.Entry.e))],
      Gramext.action
        (fun (t : 'class_rawexpr) _ (s : 'class_rawexpr) _
             (ntn : 'by_notation) _ (loc : Ploc.t) ->
           (VernacCoercion
              ((@@) (CAst.make ~loc:((!@) loc)) (ByNotation ntn), s, t) :
            'gallina_ext));
      [Gramext.Stoken ("IDENT", "Coercion");
       Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Gram.Entry.obj (class_rawexpr : 'class_rawexpr Gram.Entry.e));
       Gramext.Stoken ("", ">->");
       Gramext.Snterm
         (Gram.Entry.obj (class_rawexpr : 'class_rawexpr Gram.Entry.e))],
      Gramext.action
        (fun (t : 'class_rawexpr) _ (s : 'class_rawexpr) _ (qid : 'global) _
             (loc : Ploc.t) ->
           (VernacCoercion ((@@) (CAst.make ~loc:((!@) loc)) (AN qid), s, t) :
            'gallina_ext));
      [Gramext.Stoken ("IDENT", "Identity");
       Gramext.Stoken ("IDENT", "Coercion");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Gram.Entry.obj (class_rawexpr : 'class_rawexpr Gram.Entry.e));
       Gramext.Stoken ("", ">->");
       Gramext.Snterm
         (Gram.Entry.obj (class_rawexpr : 'class_rawexpr Gram.Entry.e))],
      Gramext.action
        (fun (t : 'class_rawexpr) _ (s : 'class_rawexpr) _ (f : 'identref) _ _
             (loc : Ploc.t) ->
           (VernacIdentityCoercion (f, s, t) : 'gallina_ext));
      [Gramext.Stoken ("IDENT", "Coercion");
       Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (def_body : 'def_body Gram.Entry.e))],
      Gramext.action
        (fun (d : 'def_body) (qid : 'global) _ (loc : Ploc.t) ->
           (let s = coerce_reference_to_id qid in
            VernacDefinition
              ((NoDischarge, Coercion), (CAst.make (Name s), None), d) :
            'gallina_ext));
      [Gramext.Stoken ("IDENT", "Canonical");
       Gramext.Stoken ("IDENT", "Structure");
       Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (def_body : 'def_body Gram.Entry.e))],
      Gramext.action
        (fun (d : 'def_body) (qid : 'global) _ _ (loc : Ploc.t) ->
           (let s = coerce_reference_to_id qid in
            VernacDefinition
              ((NoDischarge, CanonicalStructure), (CAst.make (Name s), None),
               d) :
            'gallina_ext));
      [Gramext.Stoken ("IDENT", "Canonical");
       Gramext.Stoken ("IDENT", "Structure");
       Gramext.Snterm
         (Gram.Entry.obj (by_notation : 'by_notation Gram.Entry.e))],
      Gramext.action
        (fun (ntn : 'by_notation) _ _ (loc : Ploc.t) ->
           (VernacCanonical
              CAst.((@@) (make ~loc:((!@) loc)) (ByNotation ntn)) :
            'gallina_ext));
      [Gramext.Stoken ("IDENT", "Canonical");
       Gramext.Stoken ("IDENT", "Structure");
       Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e))],
      Gramext.action
        (fun (qid : 'global) _ _ (loc : Ploc.t) ->
           (VernacCanonical CAst.((@@) (make ~loc:((!@) loc)) (AN qid)) :
            'gallina_ext));
      [Gramext.Stoken ("IDENT", "Strategy");
       Gramext.Slist1
         (Gramext.srules
            [[Gramext.Snterm
                (Gram.Entry.obj
                   (strategy_level : 'strategy_level Gram.Entry.e));
              Gramext.Stoken ("", "[");
              Gramext.Slist1
                (Gramext.Snterm
                   (Gram.Entry.obj
                      (smart_global : 'smart_global Gram.Entry.e)));
              Gramext.Stoken ("", "]")],
             Gramext.action
               (fun _ (q : 'smart_global list) _ (v : 'strategy_level)
                    (loc : Ploc.t) ->
                  (v, q : 'e__13))])],
      Gramext.action
        (fun (l : 'e__13 list) _ (loc : Ploc.t) ->
           (VernacSetStrategy l : 'gallina_ext));
      [Gramext.Stoken ("IDENT", "Opaque");
       Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e)))],
      Gramext.action
        (fun (l : 'smart_global list) _ (loc : Ploc.t) ->
           (VernacSetOpacity (Conv_oracle.Opaque, l) : 'gallina_ext));
      [(* Transparent and Opaque *)
       Gramext.
       Stoken
         ("IDENT", "Transparent");
       Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e)))],
      Gramext.action
        (fun (l : 'smart_global list) _ (loc : Ploc.t) ->
           (VernacSetOpacity (Conv_oracle.transparent, l) : 'gallina_ext))]];
  Gram.extend (arguments_modifier : 'arguments_modifier Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "clear");
       Gramext.Stoken ("IDENT", "implicits"); Gramext.Stoken ("IDENT", "and");
       Gramext.Stoken ("IDENT", "scopes")],
      Gramext.action
        (fun _ _ _ _ (loc : Ploc.t) ->
           ([`ClearImplicits; `ClearScopes] : 'arguments_modifier));
      [Gramext.Stoken ("IDENT", "clear"); Gramext.Stoken ("IDENT", "scopes");
       Gramext.Stoken ("IDENT", "and");
       Gramext.Stoken ("IDENT", "implicits")],
      Gramext.action
        (fun _ _ _ _ (loc : Ploc.t) ->
           ([`ClearImplicits; `ClearScopes] : 'arguments_modifier));
      [Gramext.Stoken ("IDENT", "extra"); Gramext.Stoken ("IDENT", "scopes")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) -> ([`ExtraScopes] : 'arguments_modifier));
      [Gramext.Stoken ("IDENT", "assert")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> ([`Assert] : 'arguments_modifier));
      [Gramext.Stoken ("IDENT", "rename")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> ([`Rename] : 'arguments_modifier));
      [Gramext.Stoken ("IDENT", "clear"); Gramext.Stoken ("IDENT", "scopes")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) -> ([`ClearScopes] : 'arguments_modifier));
      [Gramext.Stoken ("IDENT", "clear");
       Gramext.Stoken ("IDENT", "implicits")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) -> ([`ClearImplicits] : 'arguments_modifier));
      [Gramext.Stoken ("IDENT", "default");
       Gramext.Stoken ("IDENT", "implicits")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) ->
           ([`DefaultImplicits] : 'arguments_modifier));
      [Gramext.Stoken ("IDENT", "simpl"); Gramext.Stoken ("IDENT", "never")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) ->
           ([`ReductionNeverUnfold] : 'arguments_modifier));
      [Gramext.Stoken ("IDENT", "simpl");
       Gramext.Stoken ("IDENT", "nomatch")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) ->
           ([`ReductionDontExposeCase] : 'arguments_modifier))]];
  Gram.extend (implicit_name : 'implicit_name Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "[");
       Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e));
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (id : 'ident) _ (loc : Ploc.t) ->
           (id, true, false : 'implicit_name));
      [Gramext.Stoken ("", "["); Gramext.Stoken ("", "!");
       Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e));
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (id : 'ident) _ _ (loc : Ploc.t) ->
           (id, true, true : 'implicit_name));
      [Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e))],
      Gramext.action
        (fun (id : 'ident) (loc : Ploc.t) ->
           (id, false, false : 'implicit_name));
      [Gramext.Stoken ("", "!");
       Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e))],
      Gramext.action
        (fun (id : 'ident) _ (loc : Ploc.t) ->
           (id, false, true : 'implicit_name))]];
  Gram.extend (scope : 'scope Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "%"); Gramext.Stoken ("IDENT", "")],
      Gramext.action
        (fun (key : string) _ (loc : Ploc.t) -> (key : 'scope))]];
  Gram.extend (argument_spec : 'argument_spec Gram.Entry.e) None
    [None, None,
     [[Gramext.Sopt (Gramext.Stoken ("", "!"));
       Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e));
       Gramext.Sopt
         (Gramext.Snterm (Gram.Entry.obj (scope : 'scope Gram.Entry.e)))],
      Gramext.action
        (fun (s : 'scope option) (id : 'name) (b : string option)
             (loc : Ploc.t) ->
           (id.CAst.v, not (Option.is_empty b),
            Option.map (fun x -> CAst.make ~loc:((!@) loc) x) s :
            'argument_spec))]];
  Gram.extend (argument_spec_block : 'argument_spec_block Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "{");
       Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (argument_spec : 'argument_spec Gram.Entry.e)));
       Gramext.Stoken ("", "}");
       Gramext.Sopt
         (Gramext.Snterm (Gram.Entry.obj (scope : 'scope Gram.Entry.e)))],
      Gramext.action
        (fun (sc : 'scope option) _ (items : 'argument_spec list) _
             (loc : Ploc.t) ->
           (let f x =
              match sc, x with
                None, x -> x
              | x, None -> Option.map (fun y -> CAst.make ~loc:((!@) loc) y) x
              | Some _, Some _ -> user_err Pp.(str "scope declared twice")
            in
            List.map
              (fun (name, recarg_like, notation_scope) ->
                 `Id
                   {name = name; recarg_like = recarg_like;
                    notation_scope = f notation_scope;
                    implicit_status = MaximallyImplicit})
              items :
            'argument_spec_block));
      [Gramext.Stoken ("", "[");
       Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (argument_spec : 'argument_spec Gram.Entry.e)));
       Gramext.Stoken ("", "]");
       Gramext.Sopt
         (Gramext.Snterm (Gram.Entry.obj (scope : 'scope Gram.Entry.e)))],
      Gramext.action
        (fun (sc : 'scope option) _ (items : 'argument_spec list) _
             (loc : Ploc.t) ->
           (let f x =
              match sc, x with
                None, x -> x
              | x, None -> Option.map (fun y -> CAst.make ~loc:((!@) loc) y) x
              | Some _, Some _ -> user_err Pp.(str "scope declared twice")
            in
            List.map
              (fun (name, recarg_like, notation_scope) ->
                 `Id
                   {name = name; recarg_like = recarg_like;
                    notation_scope = f notation_scope;
                    implicit_status = Implicit})
              items :
            'argument_spec_block));
      [Gramext.Stoken ("", "(");
       Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (argument_spec : 'argument_spec Gram.Entry.e)));
       Gramext.Stoken ("", ")");
       Gramext.Sopt
         (Gramext.Snterm (Gram.Entry.obj (scope : 'scope Gram.Entry.e)))],
      Gramext.action
        (fun (sc : 'scope option) _ (items : 'argument_spec list) _
             (loc : Ploc.t) ->
           (let f x =
              match sc, x with
                None, x -> x
              | x, None -> Option.map (fun y -> CAst.make ~loc:((!@) loc) y) x
              | Some _, Some _ -> user_err Pp.(str "scope declared twice")
            in
            List.map
              (fun (name, recarg_like, notation_scope) ->
                 `Id
                   {name = name; recarg_like = recarg_like;
                    notation_scope = f notation_scope;
                    implicit_status = NotImplicit})
              items :
            'argument_spec_block));
      [Gramext.Stoken ("", "/")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> ([`Slash] : 'argument_spec_block));
      [Gramext.Snterm
         (Gram.Entry.obj (argument_spec : 'argument_spec Gram.Entry.e))],
      Gramext.action
        (fun (item : 'argument_spec) (loc : Ploc.t) ->
           (let (name, recarg_like, notation_scope) = item in
            [`Id
               {name = name; recarg_like = recarg_like;
                notation_scope = notation_scope;
                implicit_status = NotImplicit}] :
            'argument_spec_block))]];
  Gram.extend (more_implicits_block : 'more_implicits_block Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "{");
       Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e)));
       Gramext.Stoken ("", "}")],
      Gramext.action
        (fun _ (items : 'name list) _ (loc : Ploc.t) ->
           (List.map (fun name -> name.CAst.v, Vernacexpr.MaximallyImplicit)
              items :
            'more_implicits_block));
      [Gramext.Stoken ("", "[");
       Gramext.Slist1
         (Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e)));
       Gramext.Stoken ("", "]")],
      Gramext.action
        (fun _ (items : 'name list) _ (loc : Ploc.t) ->
           (List.map (fun name -> name.CAst.v, Vernacexpr.Implicit) items :
            'more_implicits_block));
      [Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e))],
      Gramext.action
        (fun (name : 'name) (loc : Ploc.t) ->
           ([name.CAst.v, Vernacexpr.NotImplicit] : 'more_implicits_block))]];
  Gram.extend (strategy_level : 'strategy_level Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "transparent")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (Conv_oracle.transparent : 'strategy_level));
      [Gramext.Stoken ("", "-"); Gramext.Stoken ("INT", "")],
      Gramext.action
        (fun (n : string) _ (loc : Ploc.t) ->
           (Conv_oracle.Level (-int_of_string n) : 'strategy_level));
      [Gramext.Stoken ("INT", "")],
      Gramext.action
        (fun (n : string) (loc : Ploc.t) ->
           (Conv_oracle.Level (int_of_string n) : 'strategy_level));
      [Gramext.Stoken ("IDENT", "opaque")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (Conv_oracle.Opaque : 'strategy_level));
      [Gramext.Stoken ("IDENT", "expand")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (Conv_oracle.Expand : 'strategy_level))]];
  Gram.extend (instance_name : 'instance_name Gram.Entry.e) None
    [None, None,
     [[],
      Gramext.action
        (fun (loc : Ploc.t) ->
           ((CAst.make ~loc:((!@) loc) Anonymous, None), [] :
            'instance_name));
      [Gramext.Snterm
         (Gram.Entry.obj (ident_decl : 'ident_decl Gram.Entry.e));
       Gramext.Sopt
         (Gramext.Snterm (Gram.Entry.obj (binders : 'binders Gram.Entry.e)))],
      Gramext.action
        (fun (sup : 'binders option) (name : 'ident_decl) (loc : Ploc.t) ->
           ((CAst.map (fun id -> Name id) (fst name), snd name),
            Option.default [] sup :
            'instance_name))]];
  Gram.extend (hint_info : 'hint_info Gram.Entry.e) None
    [None, None,
     [[],
      Gramext.action
        (fun (loc : Ploc.t) ->
           ({hint_priority = None; hint_pattern = None} : 'hint_info));
      [Gramext.Stoken ("", "|");
       Gramext.Sopt
         (Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e)));
       Gramext.Sopt
         (Gramext.Snterm
            (Gram.Entry.obj
               (constr_pattern : 'constr_pattern Gram.Entry.e)))],
      Gramext.action
        (fun (pat : 'constr_pattern option) (i : 'natural option) _
             (loc : Ploc.t) ->
           ({hint_priority = i; hint_pattern = pat} : 'hint_info))]];
  Gram.extend (reserv_list : 'reserv_list Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (simple_reserv : 'simple_reserv Gram.Entry.e))],
      Gramext.action
        (fun (b : 'simple_reserv) (loc : Ploc.t) -> ([b] : 'reserv_list));
      [Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (reserv_tuple : 'reserv_tuple Gram.Entry.e)))],
      Gramext.action
        (fun (bl : 'reserv_tuple list) (loc : Ploc.t) ->
           (bl : 'reserv_list))]];
  Gram.extend (reserv_tuple : 'reserv_tuple Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "(");
       Gramext.Snterm
         (Gram.Entry.obj (simple_reserv : 'simple_reserv Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (a : 'simple_reserv) _ (loc : Ploc.t) ->
           (a : 'reserv_tuple))]];
  Gram.extend (simple_reserv : 'simple_reserv Gram.Entry.e) None
    [None, None,
     [[Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (identref : 'identref Gram.Entry.e)));
       Gramext.Stoken ("", ":");
       Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
      Gramext.action
        (fun (c : 'lconstr) _ (idl : 'identref list) (loc : Ploc.t) ->
           (idl, c : 'simple_reserv))]]

let _ =
  begin let _ = (command : 'command Gram.Entry.e)
  and _ = (query_command : 'query_command Gram.Entry.e)
  and _ = (class_rawexpr : 'class_rawexpr Gram.Entry.e)
  and _ = (gallina_ext : 'gallina_ext Gram.Entry.e) in
    let grammar_entry_create = Gram.Entry.create in
    let printable : 'printable Gram.Entry.e = grammar_entry_create "printable"
    and locatable : 'locatable Gram.Entry.e = grammar_entry_create "locatable"
    and option_value : 'option_value Gram.Entry.e =
      grammar_entry_create "option_value"
    and option_ref_value : 'option_ref_value Gram.Entry.e =
      grammar_entry_create "option_ref_value"
    and option_table : 'option_table Gram.Entry.e =
      grammar_entry_create "option_table"
    and as_dirpath : 'as_dirpath Gram.Entry.e =
      grammar_entry_create "as_dirpath"
    and ne_in_or_out_modules : 'ne_in_or_out_modules Gram.Entry.e =
      grammar_entry_create "ne_in_or_out_modules"
    and in_or_out_modules : 'in_or_out_modules Gram.Entry.e =
      grammar_entry_create "in_or_out_modules"
    and comment : 'comment Gram.Entry.e = grammar_entry_create "comment"
    and positive_search_mark : 'positive_search_mark Gram.Entry.e =
      grammar_entry_create "positive_search_mark"
    and scope : 'scope Gram.Entry.e = grammar_entry_create "scope"
    and searchabout_query : 'searchabout_query Gram.Entry.e =
      grammar_entry_create "searchabout_query"
    and searchabout_queries : 'searchabout_queries Gram.Entry.e =
      grammar_entry_create "searchabout_queries"
    and univ_name_list : 'univ_name_list Gram.Entry.e =
      grammar_entry_create "univ_name_list"
    in
    Gram.extend (gallina_ext : 'gallina_ext Gram.Entry.e) None
      [None, None,
       [[Gramext.Stoken ("IDENT", "Export");
         Gramext.Stoken ("IDENT", "Unset");
         Gramext.Snterm
           (Gram.Entry.obj (option_table : 'option_table Gram.Entry.e))],
        Gramext.action
          (fun (table : 'option_table) _ _ (loc : Ploc.t) ->
             (VernacUnsetOption (true, table) : 'gallina_ext));
        [Gramext.Stoken ("IDENT", "Export"); Gramext.Stoken ("", "Set");
         Gramext.Snterm
           (Gram.Entry.obj (option_table : 'option_table Gram.Entry.e));
         Gramext.Snterm
           (Gram.Entry.obj (option_value : 'option_value Gram.Entry.e))],
        Gramext.action
          (fun (v : 'option_value) (table : 'option_table) _ _
               (loc : Ploc.t) ->
             (VernacSetOption (true, table, v) : 'gallina_ext))]];
    Gram.extend (command : 'command Gram.Entry.e) None
      [None, None,
       [[Gramext.Stoken ("IDENT", "Remove"); Gramext.Stoken ("IDENT", "");
         Gramext.Slist1
           (Gramext.Snterm
              (Gram.Entry.obj
                 (option_ref_value : 'option_ref_value Gram.Entry.e)))],
        Gramext.action
          (fun (v : 'option_ref_value list) (table : string) _
               (loc : Ploc.t) ->
             (VernacRemoveOption ([table], v) : 'command));
        [Gramext.Stoken ("IDENT", "Remove"); Gramext.Stoken ("IDENT", "");
         Gramext.Stoken ("IDENT", "");
         Gramext.Slist1
           (Gramext.Snterm
              (Gram.Entry.obj
                 (option_ref_value : 'option_ref_value Gram.Entry.e)))],
        Gramext.action
          (fun (v : 'option_ref_value list) (field : string) (table : string)
               _ (loc : Ploc.t) ->
             (VernacRemoveOption ([table; field], v) : 'command));
        [Gramext.Stoken ("IDENT", "Test");
         Gramext.Snterm
           (Gram.Entry.obj (option_table : 'option_table Gram.Entry.e))],
        Gramext.action
          (fun (table : 'option_table) _ (loc : Ploc.t) ->
             (VernacPrintOption table : 'command));
        [Gramext.Stoken ("IDENT", "Test");
         Gramext.Snterm
           (Gram.Entry.obj (option_table : 'option_table Gram.Entry.e));
         Gramext.Stoken ("", "for");
         Gramext.Slist1
           (Gramext.Snterm
              (Gram.Entry.obj
                 (option_ref_value : 'option_ref_value Gram.Entry.e)))],
        Gramext.action
          (fun (v : 'option_ref_value list) _ (table : 'option_table) _
               (loc : Ploc.t) ->
             (VernacMemOption (table, v) : 'command));
        [Gramext.Stoken ("IDENT", "Add"); Gramext.Stoken ("IDENT", "");
         Gramext.Slist1
           (Gramext.Snterm
              (Gram.Entry.obj
                 (option_ref_value : 'option_ref_value Gram.Entry.e)))],
        Gramext.action
          (fun (v : 'option_ref_value list) (table : string) _
               (loc : Ploc.t) ->
             (VernacAddOption ([table], v) : 'command));
        [Gramext.Stoken ("IDENT", "Add"); Gramext.Stoken ("IDENT", "");
         Gramext.Stoken ("IDENT", "");
         Gramext.Slist1
           (Gramext.Snterm
              (Gram.Entry.obj
                 (option_ref_value : 'option_ref_value Gram.Entry.e)))],
        Gramext.action
          (fun (v : 'option_ref_value list) (field : string) (table : string)
               _ (loc : Ploc.t) ->
             (VernacAddOption ([table; field], v) : 'command));
        [Gramext.Stoken ("IDENT", "Print"); Gramext.Stoken ("IDENT", "Table");
         Gramext.Snterm
           (Gram.Entry.obj (option_table : 'option_table Gram.Entry.e))],
        Gramext.action
          (fun (table : 'option_table) _ _ (loc : Ploc.t) ->
             (VernacPrintOption table : 'command));
        [Gramext.Stoken ("IDENT", "Unset");
         Gramext.Snterm
           (Gram.Entry.obj (option_table : 'option_table Gram.Entry.e))],
        Gramext.action
          (fun (table : 'option_table) _ (loc : Ploc.t) ->
             (VernacUnsetOption (false, table) : 'command));
        [Gramext.Stoken ("", "Set");
         Gramext.Snterm
           (Gram.Entry.obj (option_table : 'option_table Gram.Entry.e));
         Gramext.Snterm
           (Gram.Entry.obj (option_value : 'option_value Gram.Entry.e))],
        Gramext.action
          (fun (v : 'option_value) (table : 'option_table) _ (loc : Ploc.t) ->
             (VernacSetOption (false, table, v) : 'command));
        [Gramext.Stoken ("IDENT", "Add"); Gramext.Stoken ("IDENT", "Rec");
         Gramext.Stoken ("IDENT", "ML"); Gramext.Stoken ("IDENT", "Path");
         Gramext.Snterm
           (Gram.Entry.obj (ne_string : 'ne_string Gram.Entry.e))],
        Gramext.action
          (fun (dir : 'ne_string) _ _ _ _ (loc : Ploc.t) ->
             (VernacAddMLPath (true, dir) : 'command));
        [Gramext.Stoken ("IDENT", "Add"); Gramext.Stoken ("IDENT", "ML");
         Gramext.Stoken ("IDENT", "Path");
         Gramext.Snterm
           (Gram.Entry.obj (ne_string : 'ne_string Gram.Entry.e))],
        Gramext.action
          (fun (dir : 'ne_string) _ _ _ (loc : Ploc.t) ->
             (VernacAddMLPath (false, dir) : 'command));
        [Gramext.Stoken ("IDENT", "Inspect");
         Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e))],
        Gramext.action
          (fun (n : 'natural) _ (loc : Ploc.t) ->
             (VernacPrint (PrintInspect n) : 'command));
        [Gramext.Stoken ("IDENT", "Print");
         Gramext.Stoken ("IDENT", "Namespace");
         Gramext.Snterm (Gram.Entry.obj (dirpath : 'dirpath Gram.Entry.e))],
        Gramext.action
          (fun (ns : 'dirpath) _ _ (loc : Ploc.t) ->
             (VernacPrint (PrintNamespace ns) : 'command));
        [Gramext.Stoken ("IDENT", "Print");
         Gramext.Stoken ("IDENT", "Module");
         Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e))],
        Gramext.action
          (fun (qid : 'global) _ _ (loc : Ploc.t) ->
             (VernacPrint (PrintModule qid) : 'command));
        [Gramext.Stoken ("IDENT", "Print");
         Gramext.Stoken ("IDENT", "Module"); Gramext.Stoken ("", "Type");
         Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e))],
        Gramext.action
          (fun (qid : 'global) _ _ _ (loc : Ploc.t) ->
             (VernacPrint (PrintModuleType qid) : 'command));
        [Gramext.Stoken ("IDENT", "Print");
         Gramext.Snterm
           (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e));
         Gramext.Sopt
           (Gramext.Snterm
              (Gram.Entry.obj
                 (univ_name_list : 'univ_name_list Gram.Entry.e)))],
        Gramext.action
          (fun (l : 'univ_name_list option) (qid : 'smart_global) _
               (loc : Ploc.t) ->
             (VernacPrint (PrintName (qid, l)) : 'command));
        [Gramext.Stoken ("IDENT", "Print");
         Gramext.Snterm
           (Gram.Entry.obj (printable : 'printable Gram.Entry.e))],
        Gramext.action
          (fun (p : 'printable) _ (loc : Ploc.t) ->
             (VernacPrint p : 'command));
        [Gramext.Stoken ("", "Type");
         Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e))],
        Gramext.action
          (fun (c : 'lconstr) _ (loc : Ploc.t) ->
             (VernacGlobalCheck c : 'command));
        [Gramext.Stoken ("IDENT", "DelPath");
         Gramext.Snterm
           (Gram.Entry.obj (ne_string : 'ne_string Gram.Entry.e))],
        Gramext.action
          (fun (dir : 'ne_string) _ (loc : Ploc.t) ->
             (VernacRemoveLoadPath dir : 'command));
        [Gramext.Stoken ("IDENT", "AddRecPath");
         Gramext.Snterm
           (Gram.Entry.obj (ne_string : 'ne_string Gram.Entry.e));
         Gramext.Stoken ("", "as");
         Gramext.Snterm
           (Gram.Entry.obj (as_dirpath : 'as_dirpath Gram.Entry.e))],
        Gramext.action
          (fun (alias : 'as_dirpath) _ (dir : 'ne_string) _ (loc : Ploc.t) ->
             (VernacAddLoadPath (true, dir, alias) : 'command));
        [Gramext.Stoken ("IDENT", "AddPath");
         Gramext.Snterm
           (Gram.Entry.obj (ne_string : 'ne_string Gram.Entry.e));
         Gramext.Stoken ("", "as");
         Gramext.Snterm
           (Gram.Entry.obj (as_dirpath : 'as_dirpath Gram.Entry.e))],
        Gramext.action
          (fun (alias : 'as_dirpath) _ (dir : 'ne_string) _ (loc : Ploc.t) ->
             (VernacAddLoadPath (false, dir, alias) : 'command));
        [Gramext.Stoken ("IDENT", "Remove");
         Gramext.Stoken ("IDENT", "LoadPath");
         Gramext.Snterm
           (Gram.Entry.obj (ne_string : 'ne_string Gram.Entry.e))],
        Gramext.action
          (fun (dir : 'ne_string) _ _ (loc : Ploc.t) ->
             (VernacRemoveLoadPath dir : 'command));
        [Gramext.Stoken ("IDENT", "Add"); Gramext.Stoken ("IDENT", "Rec");
         Gramext.Stoken ("IDENT", "LoadPath");
         Gramext.Snterm
           (Gram.Entry.obj (ne_string : 'ne_string Gram.Entry.e));
         Gramext.Snterm
           (Gram.Entry.obj (as_dirpath : 'as_dirpath Gram.Entry.e))],
        Gramext.action
          (fun (alias : 'as_dirpath) (dir : 'ne_string) _ _ _
               (loc : Ploc.t) ->
             (VernacAddLoadPath (true, dir, alias) : 'command));
        [Gramext.Stoken ("IDENT", "Add");
         Gramext.Stoken ("IDENT", "LoadPath");
         Gramext.Snterm
           (Gram.Entry.obj (ne_string : 'ne_string Gram.Entry.e));
         Gramext.Snterm
           (Gram.Entry.obj (as_dirpath : 'as_dirpath Gram.Entry.e))],
        Gramext.action
          (fun (alias : 'as_dirpath) (dir : 'ne_string) _ _ (loc : Ploc.t) ->
             (VernacAddLoadPath (false, dir, alias) : 'command));
        [Gramext.Stoken ("IDENT", "Locate");
         Gramext.Snterm
           (Gram.Entry.obj (locatable : 'locatable Gram.Entry.e))],
        Gramext.action
          (fun (l : 'locatable) _ (loc : Ploc.t) ->
             (VernacLocate l : 'command));
        [Gramext.Stoken ("IDENT", "Declare"); Gramext.Stoken ("IDENT", "ML");
         Gramext.Stoken ("IDENT", "Module");
         Gramext.Slist1
           (Gramext.Snterm
              (Gram.Entry.obj (ne_string : 'ne_string Gram.Entry.e)))],
        Gramext.action
          (fun (l : 'ne_string list) _ _ _ (loc : Ploc.t) ->
             (VernacDeclareMLModule l : 'command));
        [Gramext.Stoken ("IDENT", "Load");
         Gramext.srules
           [[], Gramext.action (fun (loc : Ploc.t) -> (false : 'e__25));
            [Gramext.Stoken ("IDENT", "Verbose")],
            Gramext.action (fun _ (loc : Ploc.t) -> (true : 'e__25))];
         Gramext.srules
           [[Gramext.Stoken ("IDENT", "")],
            Gramext.action (fun (s : string) (loc : Ploc.t) -> (s : 'e__26));
            [Gramext.Snterm
               (Gram.Entry.obj (ne_string : 'ne_string Gram.Entry.e))],
            Gramext.action
              (fun (s : 'ne_string) (loc : Ploc.t) -> (s : 'e__26))]],
        Gramext.action
          (fun (s : 'e__26) (verbosely : 'e__25) _ (loc : Ploc.t) ->
             (VernacLoad (verbosely, s) : 'command));
        [Gramext.Stoken ("IDENT", "Quit")],
        Gramext.action
          (fun _ (loc : Ploc.t) -> (VernacToplevelControl Quit : 'command));
        [Gramext.Stoken ("IDENT", "Drop")],
        Gramext.action
          (fun _ (loc : Ploc.t) -> (VernacToplevelControl Drop : 'command));
        [Gramext.Stoken ("IDENT", "Cd");
         Gramext.Snterm
           (Gram.Entry.obj (ne_string : 'ne_string Gram.Entry.e))],
        Gramext.action
          (fun (dir : 'ne_string) _ (loc : Ploc.t) ->
             (VernacChdir (Some dir) : 'command));
        [Gramext.Stoken ("IDENT", "Cd")],
        Gramext.action
          (fun _ (loc : Ploc.t) -> (VernacChdir None : 'command));
        [Gramext.Stoken ("IDENT", "Pwd")],
        Gramext.action
          (fun _ (loc : Ploc.t) -> (VernacChdir None : 'command));
        [Gramext.Stoken ("IDENT", "Declare");
         Gramext.Stoken ("IDENT", "Instance");
         Gramext.Snterm
           (Gram.Entry.obj (instance_name : 'instance_name Gram.Entry.e));
         Gramext.Stoken ("", ":");
         Gramext.srules
           [[],
            Gramext.action
              (fun (loc : Ploc.t) -> (Decl_kinds.Explicit : 'e__24));
            [Gramext.Stoken ("", "!")],
            Gramext.action
              (fun _ (loc : Ploc.t) -> (Decl_kinds.Implicit : 'e__24))];
         Gramext.Snterml
           (Gram.Entry.obj (operconstr : 'operconstr Gram.Entry.e), "200");
         Gramext.Snterm
           (Gram.Entry.obj (hint_info : 'hint_info Gram.Entry.e))],
        Gramext.action
          (fun (info : 'hint_info) (t : 'operconstr) (expl : 'e__24) _
               (namesup : 'instance_name) _ _ (loc : Ploc.t) ->
             (VernacInstance
                (true, snd namesup, (fst namesup, expl, t), None, info) :
              'command));
        [Gramext.Stoken ("IDENT", "Comments");
         Gramext.Slist0
           (Gramext.Snterm
              (Gram.Entry.obj (comment : 'comment Gram.Entry.e)))],
        Gramext.action
          (fun (l : 'comment list) _ (loc : Ploc.t) ->
             (VernacComments l : 'command))]];
    Gram.extend (query_command : 'query_command Gram.Entry.e) None
      [None, None,
       [[Gramext.Stoken ("IDENT", "SearchAbout"); Gramext.Stoken ("", "[");
         Gramext.Slist1
           (Gramext.Snterm
              (Gram.Entry.obj
                 (searchabout_query : 'searchabout_query Gram.Entry.e)));
         Gramext.Stoken ("", "]");
         Gramext.Snterm
           (Gram.Entry.obj
              (in_or_out_modules : 'in_or_out_modules Gram.Entry.e));
         Gramext.Stoken ("", ".")],
        Gramext.action
          (fun _ (l : 'in_or_out_modules) _ (sl : 'searchabout_query list) _ _
               (loc : Ploc.t) ->
             (fun g -> VernacSearch (SearchAbout sl, g, l) : 'query_command));
        [Gramext.Stoken ("IDENT", "SearchAbout");
         Gramext.Snterm
           (Gram.Entry.obj
              (searchabout_query : 'searchabout_query Gram.Entry.e));
         Gramext.Snterm
           (Gram.Entry.obj
              (searchabout_queries : 'searchabout_queries Gram.Entry.e));
         Gramext.Stoken ("", ".")],
        Gramext.action
          (fun _ (l : 'searchabout_queries) (s : 'searchabout_query) _
               (loc : Ploc.t) ->
             (fun g ->
                let (sl, m) = l in
                VernacSearch (SearchAbout (s :: sl), g, m) :
              'query_command));
        [Gramext.Stoken ("IDENT", "Search");
         Gramext.Snterm
           (Gram.Entry.obj
              (searchabout_query : 'searchabout_query Gram.Entry.e));
         Gramext.Snterm
           (Gram.Entry.obj
              (searchabout_queries : 'searchabout_queries Gram.Entry.e));
         Gramext.Stoken ("", ".")],
        Gramext.action
          (fun _ (l : 'searchabout_queries) (s : 'searchabout_query) _
               (loc : Ploc.t) ->
             (let (sl, m) = l in
              fun g -> VernacSearch (SearchAbout (s :: sl), g, m) :
              'query_command));
        [Gramext.Stoken ("IDENT", "SearchRewrite");
         Gramext.Snterm
           (Gram.Entry.obj (constr_pattern : 'constr_pattern Gram.Entry.e));
         Gramext.Snterm
           (Gram.Entry.obj
              (in_or_out_modules : 'in_or_out_modules Gram.Entry.e));
         Gramext.Stoken ("", ".")],
        Gramext.action
          (fun _ (l : 'in_or_out_modules) (c : 'constr_pattern) _
               (loc : Ploc.t) ->
             (fun g -> VernacSearch (SearchRewrite c, g, l) :
              'query_command));
        [Gramext.Stoken ("IDENT", "SearchPattern");
         Gramext.Snterm
           (Gram.Entry.obj (constr_pattern : 'constr_pattern Gram.Entry.e));
         Gramext.Snterm
           (Gram.Entry.obj
              (in_or_out_modules : 'in_or_out_modules Gram.Entry.e));
         Gramext.Stoken ("", ".")],
        Gramext.action
          (fun _ (l : 'in_or_out_modules) (c : 'constr_pattern) _
               (loc : Ploc.t) ->
             (fun g -> VernacSearch (SearchPattern c, g, l) :
              'query_command));
        [Gramext.Stoken ("IDENT", "SearchHead");
         Gramext.Snterm
           (Gram.Entry.obj (constr_pattern : 'constr_pattern Gram.Entry.e));
         Gramext.Snterm
           (Gram.Entry.obj
              (in_or_out_modules : 'in_or_out_modules Gram.Entry.e));
         Gramext.Stoken ("", ".")],
        Gramext.action
          (fun _ (l : 'in_or_out_modules) (c : 'constr_pattern) _
               (loc : Ploc.t) ->
             (fun g -> VernacSearch (SearchHead c, g, l) : 'query_command));
        [Gramext.Stoken ("IDENT", "About");
         Gramext.Snterm
           (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e));
         Gramext.Sopt
           (Gramext.Snterm
              (Gram.Entry.obj
                 (univ_name_list : 'univ_name_list Gram.Entry.e)));
         Gramext.Stoken ("", ".")],
        Gramext.action
          (fun _ (l : 'univ_name_list option) (qid : 'smart_global) _
               (loc : Ploc.t) ->
             (fun g -> VernacPrint (PrintAbout (qid, l, g)) :
              'query_command));
        [Gramext.Stoken ("IDENT", "Check");
         Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
         Gramext.Stoken ("", ".")],
        Gramext.action
          (fun _ (c : 'lconstr) _ (loc : Ploc.t) ->
             (fun g -> VernacCheckMayEval (None, g, c) : 'query_command));
        [Gramext.Stoken ("IDENT", "Compute");
         Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
         Gramext.Stoken ("", ".")],
        Gramext.action
          (fun _ (c : 'lconstr) _ (loc : Ploc.t) ->
             (fun g ->
                VernacCheckMayEval (Some (Genredexpr.CbvVm None), g, c) :
              'query_command));
        [Gramext.Stoken ("IDENT", "Eval");
         Gramext.Snterm (Gram.Entry.obj (red_expr : 'red_expr Gram.Entry.e));
         Gramext.Stoken ("", "in");
         Gramext.Snterm (Gram.Entry.obj (lconstr : 'lconstr Gram.Entry.e));
         Gramext.Stoken ("", ".")],
        Gramext.action
          (fun _ (c : 'lconstr) _ (r : 'red_expr) _ (loc : Ploc.t) ->
             (fun g -> VernacCheckMayEval (Some r, g, c) : 'query_command))]];
    Gram.extend (printable : 'printable Gram.Entry.e) None
      [None, None,
       [[Gramext.Stoken ("IDENT", "Strategies")],
        Gramext.action
          (fun _ (loc : Ploc.t) -> (PrintStrategy None : 'printable));
        [Gramext.Stoken ("IDENT", "Strategy");
         Gramext.Snterm
           (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e))],
        Gramext.action
          (fun (qid : 'smart_global) _ (loc : Ploc.t) ->
             (PrintStrategy (Some qid) : 'printable));
        [Gramext.Stoken ("IDENT", "All");
         Gramext.Stoken ("IDENT", "Dependencies");
         Gramext.Snterm
           (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e))],
        Gramext.action
          (fun (qid : 'smart_global) _ _ (loc : Ploc.t) ->
             (PrintAssumptions (true, true, qid) : 'printable));
        [Gramext.Stoken ("IDENT", "Transparent");
         Gramext.Stoken ("IDENT", "Dependencies");
         Gramext.Snterm
           (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e))],
        Gramext.action
          (fun (qid : 'smart_global) _ _ (loc : Ploc.t) ->
             (PrintAssumptions (false, true, qid) : 'printable));
        [Gramext.Stoken ("IDENT", "Opaque");
         Gramext.Stoken ("IDENT", "Dependencies");
         Gramext.Snterm
           (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e))],
        Gramext.action
          (fun (qid : 'smart_global) _ _ (loc : Ploc.t) ->
             (PrintAssumptions (true, false, qid) : 'printable));
        [Gramext.Stoken ("IDENT", "Assumptions");
         Gramext.Snterm
           (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e))],
        Gramext.action
          (fun (qid : 'smart_global) _ (loc : Ploc.t) ->
             (PrintAssumptions (false, false, qid) : 'printable));
        [Gramext.Stoken ("IDENT", "Sorted");
         Gramext.Stoken ("IDENT", "Universes");
         Gramext.Sopt
           (Gramext.Snterm
              (Gram.Entry.obj (ne_string : 'ne_string Gram.Entry.e)))],
        Gramext.action
          (fun (fopt : 'ne_string option) _ _ (loc : Ploc.t) ->
             (PrintUniverses (true, fopt) : 'printable));
        [Gramext.Stoken ("IDENT", "Universes");
         Gramext.Sopt
           (Gramext.Snterm
              (Gram.Entry.obj (ne_string : 'ne_string Gram.Entry.e)))],
        Gramext.action
          (fun (fopt : 'ne_string option) _ (loc : Ploc.t) ->
             (PrintUniverses (false, fopt) : 'printable));
        [Gramext.Stoken ("IDENT", "Implicit");
         Gramext.Snterm
           (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e))],
        Gramext.action
          (fun (qid : 'smart_global) _ (loc : Ploc.t) ->
             (PrintImplicit qid : 'printable));
        [Gramext.Stoken ("IDENT", "Visibility");
         Gramext.Sopt
           (Gramext.srules
              [[Gramext.Stoken ("IDENT", "")],
               Gramext.action
                 (fun (x : string) (loc : Ploc.t) -> (x : 'e__27))])],
        Gramext.action
          (fun (s : 'e__27 option) _ (loc : Ploc.t) ->
             (PrintVisibility s : 'printable));
        [Gramext.Stoken ("IDENT", "Scope"); Gramext.Stoken ("IDENT", "")],
        Gramext.action
          (fun (s : string) _ (loc : Ploc.t) -> (PrintScope s : 'printable));
        [Gramext.Stoken ("IDENT", "Scopes")],
        Gramext.action (fun _ (loc : Ploc.t) -> (PrintScopes : 'printable));
        [Gramext.Stoken ("IDENT", "HintDb"); Gramext.Stoken ("IDENT", "")],
        Gramext.action
          (fun (s : string) _ (loc : Ploc.t) ->
             (PrintHintDbName s : 'printable));
        [Gramext.Stoken ("IDENT", "Hint"); Gramext.Stoken ("", "*")],
        Gramext.action (fun _ _ (loc : Ploc.t) -> (PrintHintDb : 'printable));
        [Gramext.Stoken ("IDENT", "Hint");
         Gramext.Snterm
           (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e))],
        Gramext.action
          (fun (qid : 'smart_global) _ (loc : Ploc.t) ->
             (PrintHint qid : 'printable));
        [Gramext.Stoken ("IDENT", "Hint")],
        Gramext.action (fun _ (loc : Ploc.t) -> (PrintHintGoal : 'printable));
        [Gramext.Stoken ("IDENT", "Options")],
        Gramext.action (fun _ (loc : Ploc.t) -> (PrintTables : 'printable));
        [Gramext.Stoken ("IDENT", "Tables")],
        Gramext.action (fun _ (loc : Ploc.t) -> (PrintTables : 'printable));
        [Gramext.Stoken ("IDENT", "Canonical");
         Gramext.Stoken ("IDENT", "Projections")],
        Gramext.action
          (fun _ _ (loc : Ploc.t) ->
             (PrintCanonicalConversions : 'printable));
        [Gramext.Stoken ("IDENT", "Coercion");
         Gramext.Stoken ("IDENT", "Paths");
         Gramext.Snterm
           (Gram.Entry.obj (class_rawexpr : 'class_rawexpr Gram.Entry.e));
         Gramext.Snterm
           (Gram.Entry.obj (class_rawexpr : 'class_rawexpr Gram.Entry.e))],
        Gramext.action
          (fun (t : 'class_rawexpr) (s : 'class_rawexpr) _ _ (loc : Ploc.t) ->
             (PrintCoercionPaths (s, t) : 'printable));
        [Gramext.Stoken ("IDENT", "Coercions")],
        Gramext.action
          (fun _ (loc : Ploc.t) -> (PrintCoercions : 'printable));
        [Gramext.Stoken ("IDENT", "Instances");
         Gramext.Snterm
           (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e))],
        Gramext.action
          (fun (qid : 'smart_global) _ (loc : Ploc.t) ->
             (PrintInstances qid : 'printable));
        [Gramext.Stoken ("IDENT", "TypeClasses")],
        Gramext.action
          (fun _ (loc : Ploc.t) -> (PrintTypeClasses : 'printable));
        [Gramext.Stoken ("IDENT", "Classes")],
        Gramext.action (fun _ (loc : Ploc.t) -> (PrintClasses : 'printable));
        [Gramext.Stoken ("IDENT", "Graph")],
        Gramext.action (fun _ (loc : Ploc.t) -> (PrintGraph : 'printable));
        [Gramext.Stoken ("IDENT", "Debug"); Gramext.Stoken ("IDENT", "GC")],
        Gramext.action
          (fun _ _ (loc : Ploc.t) -> (PrintDebugGC : 'printable));
        [Gramext.Stoken ("IDENT", "ML"); Gramext.Stoken ("IDENT", "Modules")],
        Gramext.action
          (fun _ _ (loc : Ploc.t) -> (PrintMLModules : 'printable));
        [Gramext.Stoken ("IDENT", "ML"); Gramext.Stoken ("IDENT", "Path")],
        Gramext.action
          (fun _ _ (loc : Ploc.t) -> (PrintMLLoadPath : 'printable));
        [Gramext.Stoken ("IDENT", "Libraries")],
        Gramext.action (fun _ (loc : Ploc.t) -> (PrintModules : 'printable));
        [Gramext.Stoken ("IDENT", "Modules")],
        Gramext.action
          (fun _ (loc : Ploc.t) ->
             (user_err
                Pp
                .(str
                  "Print Modules is obsolete; use Print Libraries instead") :
              'printable));
        [Gramext.Stoken ("IDENT", "LoadPath");
         Gramext.Sopt
           (Gramext.Snterm
              (Gram.Entry.obj (dirpath : 'dirpath Gram.Entry.e)))],
        Gramext.action
          (fun (dir : 'dirpath option) _ (loc : Ploc.t) ->
             (PrintLoadPath dir : 'printable));
        [Gramext.Stoken ("IDENT", "Grammar"); Gramext.Stoken ("IDENT", "")],
        Gramext.action
          (fun (ent : string) _ (loc : Ploc.t) ->
             (PrintGrammar ent : 'printable));
        [Gramext.Stoken ("IDENT", "Section");
         Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e))],
        Gramext.action
          (fun (s : 'global) _ (loc : Ploc.t) ->
             (PrintSectionContext s : 'printable));
        [Gramext.Stoken ("IDENT", "All")],
        Gramext.action
          (fun _ (loc : Ploc.t) -> (PrintFullContext : 'printable));
        [Gramext.Stoken ("IDENT", "Term");
         Gramext.Snterm
           (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e));
         Gramext.Sopt
           (Gramext.Snterm
              (Gram.Entry.obj
                 (univ_name_list : 'univ_name_list Gram.Entry.e)))],
        Gramext.action
          (fun (l : 'univ_name_list option) (qid : 'smart_global) _
               (loc : Ploc.t) ->
             (PrintName (qid, l) : 'printable))]];
    Gram.extend (class_rawexpr : 'class_rawexpr Gram.Entry.e) None
      [None, None,
       [[Gramext.Snterm
           (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e))],
        Gramext.action
          (fun (qid : 'smart_global) (loc : Ploc.t) ->
             (RefClass qid : 'class_rawexpr));
        [Gramext.Stoken ("IDENT", "Sortclass")],
        Gramext.action (fun _ (loc : Ploc.t) -> (SortClass : 'class_rawexpr));
        [Gramext.Stoken ("IDENT", "Funclass")],
        Gramext.action
          (fun _ (loc : Ploc.t) -> (FunClass : 'class_rawexpr))]];
    Gram.extend (locatable : 'locatable Gram.Entry.e) None
      [None, None,
       [[Gramext.Stoken ("IDENT", "Module");
         Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e))],
        Gramext.action
          (fun (qid : 'global) _ (loc : Ploc.t) ->
             (LocateModule qid : 'locatable));
        [Gramext.Stoken ("IDENT", "Library");
         Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e))],
        Gramext.action
          (fun (qid : 'global) _ (loc : Ploc.t) ->
             (LocateLibrary qid : 'locatable));
        [Gramext.Stoken ("IDENT", "File");
         Gramext.Snterm
           (Gram.Entry.obj (ne_string : 'ne_string Gram.Entry.e))],
        Gramext.action
          (fun (f : 'ne_string) _ (loc : Ploc.t) ->
             (LocateFile f : 'locatable));
        [Gramext.Stoken ("IDENT", "Term");
         Gramext.Snterm
           (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e))],
        Gramext.action
          (fun (qid : 'smart_global) _ (loc : Ploc.t) ->
             (LocateTerm qid : 'locatable));
        [Gramext.Snterm
           (Gram.Entry.obj (smart_global : 'smart_global Gram.Entry.e))],
        Gramext.action
          (fun (qid : 'smart_global) (loc : Ploc.t) ->
             (LocateAny qid : 'locatable))]];
    Gram.extend (option_value : 'option_value Gram.Entry.e) None
      [None, None,
       [[Gramext.Stoken ("STRING", "")],
        Gramext.action
          (fun (s : string) (loc : Ploc.t) ->
             (StringValue s : 'option_value));
        [Gramext.Snterm (Gram.Entry.obj (integer : 'integer Gram.Entry.e))],
        Gramext.action
          (fun (n : 'integer) (loc : Ploc.t) ->
             (IntValue (Some n) : 'option_value));
        [],
        Gramext.action
          (fun (loc : Ploc.t) -> (BoolValue true : 'option_value))]];
    Gram.extend (option_ref_value : 'option_ref_value Gram.Entry.e) None
      [None, None,
       [[Gramext.Stoken ("STRING", "")],
        Gramext.action
          (fun (s : string) (loc : Ploc.t) ->
             (StringRefValue s : 'option_ref_value));
        [Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e))],
        Gramext.action
          (fun (id : 'global) (loc : Ploc.t) ->
             (QualidRefValue id : 'option_ref_value))]];
    Gram.extend (option_table : 'option_table Gram.Entry.e) None
      [None, None,
       [[Gramext.Slist1
           (Gramext.srules
              [[Gramext.Stoken ("IDENT", "")],
               Gramext.action
                 (fun (x : string) (loc : Ploc.t) -> (x : 'e__28))])],
        Gramext.action
          (fun (fl : 'e__28 list) (loc : Ploc.t) -> (fl : 'option_table))]];
    Gram.extend (as_dirpath : 'as_dirpath Gram.Entry.e) None
      [None, None,
       [[Gramext.Sopt
           (Gramext.srules
              [[Gramext.Stoken ("", "as");
                Gramext.Snterm
                  (Gram.Entry.obj (dirpath : 'dirpath Gram.Entry.e))],
               Gramext.action
                 (fun (d : 'dirpath) _ (loc : Ploc.t) -> (d : 'e__29))])],
        Gramext.action
          (fun (d : 'e__29 option) (loc : Ploc.t) -> (d : 'as_dirpath))]];
    Gram.extend (ne_in_or_out_modules : 'ne_in_or_out_modules Gram.Entry.e)
      None
      [None, None,
       [[Gramext.Stoken ("IDENT", "outside");
         Gramext.Slist1
           (Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e)))],
        Gramext.action
          (fun (l : 'global list) _ (loc : Ploc.t) ->
             (SearchOutside l : 'ne_in_or_out_modules));
        [Gramext.Stoken ("IDENT", "inside");
         Gramext.Slist1
           (Gramext.Snterm (Gram.Entry.obj (global : 'global Gram.Entry.e)))],
        Gramext.action
          (fun (l : 'global list) _ (loc : Ploc.t) ->
             (SearchInside l : 'ne_in_or_out_modules))]];
    Gram.extend (in_or_out_modules : 'in_or_out_modules Gram.Entry.e) None
      [None, None,
       [[],
        Gramext.action
          (fun (loc : Ploc.t) -> (SearchOutside [] : 'in_or_out_modules));
        [Gramext.Snterm
           (Gram.Entry.obj
              (ne_in_or_out_modules : 'ne_in_or_out_modules Gram.Entry.e))],
        Gramext.action
          (fun (m : 'ne_in_or_out_modules) (loc : Ploc.t) ->
             (m : 'in_or_out_modules))]];
    Gram.extend (comment : 'comment Gram.Entry.e) None
      [None, None,
       [[Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e))],
        Gramext.action
          (fun (n : 'natural) (loc : Ploc.t) -> (CommentInt n : 'comment));
        [Gramext.Stoken ("STRING", "")],
        Gramext.action
          (fun (s : string) (loc : Ploc.t) -> (CommentString s : 'comment));
        [Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e))],
        Gramext.action
          (fun (c : 'constr) (loc : Ploc.t) ->
             (CommentConstr c : 'comment))]];
    Gram.extend (positive_search_mark : 'positive_search_mark Gram.Entry.e)
      None
      [None, None,
       [[],
        Gramext.action (fun (loc : Ploc.t) -> (true : 'positive_search_mark));
        [Gramext.Stoken ("", "-")],
        Gramext.action
          (fun _ (loc : Ploc.t) -> (false : 'positive_search_mark))]];
    Gram.extend (scope : 'scope Gram.Entry.e) None
      [None, None,
       [[Gramext.Stoken ("", "%"); Gramext.Stoken ("IDENT", "")],
        Gramext.action
          (fun (key : string) _ (loc : Ploc.t) -> (key : 'scope))]];
    Gram.extend (searchabout_query : 'searchabout_query Gram.Entry.e) None
      [None, None,
       [[Gramext.Snterm
           (Gram.Entry.obj
              (positive_search_mark : 'positive_search_mark Gram.Entry.e));
         Gramext.Snterm
           (Gram.Entry.obj (constr_pattern : 'constr_pattern Gram.Entry.e))],
        Gramext.action
          (fun (p : 'constr_pattern) (b : 'positive_search_mark)
               (loc : Ploc.t) ->
             (b, SearchSubPattern p : 'searchabout_query));
        [Gramext.Snterm
           (Gram.Entry.obj
              (positive_search_mark : 'positive_search_mark Gram.Entry.e));
         Gramext.Snterm
           (Gram.Entry.obj (ne_string : 'ne_string Gram.Entry.e));
         Gramext.Sopt
           (Gramext.Snterm (Gram.Entry.obj (scope : 'scope Gram.Entry.e)))],
        Gramext.action
          (fun (sc : 'scope option) (s : 'ne_string)
               (b : 'positive_search_mark) (loc : Ploc.t) ->
             (b, SearchString (s, sc) : 'searchabout_query))]];
    Gram.extend (searchabout_queries : 'searchabout_queries Gram.Entry.e) None
      [None, None,
       [[],
        Gramext.action
          (fun (loc : Ploc.t) ->
             ([], SearchOutside [] : 'searchabout_queries));
        [Gramext.Snterm
           (Gram.Entry.obj
              (searchabout_query : 'searchabout_query Gram.Entry.e));
         Gramext.Sself],
        Gramext.action
          (fun (l : 'searchabout_queries) (s : 'searchabout_query)
               (loc : Ploc.t) ->
             (let (sl, m) = l in s :: sl, m : 'searchabout_queries));
        [Gramext.Snterm
           (Gram.Entry.obj
              (ne_in_or_out_modules : 'ne_in_or_out_modules Gram.Entry.e))],
        Gramext.action
          (fun (m : 'ne_in_or_out_modules) (loc : Ploc.t) ->
             ([], m : 'searchabout_queries))]];
    Gram.extend (univ_name_list : 'univ_name_list Gram.Entry.e) None
      [None, None,
       [[Gramext.Stoken ("", "@{");
         Gramext.Slist0
           (Gramext.Snterm (Gram.Entry.obj (name : 'name Gram.Entry.e)));
         Gramext.Stoken ("", "}")],
        Gramext.action
          (fun _ (l : 'name list) _ (loc : Ploc.t) -> (l : 'univ_name_list))]]
  end;
  Gram.extend (command : 'command Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "Declare");
       Gramext.Stoken ("IDENT", "Reduction"); Gramext.Stoken ("IDENT", "");
       Gramext.Stoken ("", ":=");
       Gramext.Snterm (Gram.Entry.obj (red_expr : 'red_expr Gram.Entry.e))],
      Gramext.action
        (fun (r : 'red_expr) _ (s : string) _ _ (loc : Ploc.t) ->
           (VernacDeclareReduction (s, r) : 'command));
      [Gramext.Stoken ("IDENT", "Debug"); Gramext.Stoken ("IDENT", "Off")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) ->
           (VernacSetOption (false, ["Ltac"; "Debug"], BoolValue false) :
            'command));
      [Gramext.Stoken ("IDENT", "Debug"); Gramext.Stoken ("IDENT", "On")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) ->
           (VernacSetOption (false, ["Ltac"; "Debug"], BoolValue true) :
            'command));
      [Gramext.Stoken ("IDENT", "Backtrack");
       Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e))],
      Gramext.action
        (fun (p : 'natural) (m : 'natural) (n : 'natural) _ (loc : Ploc.t) ->
           (VernacBacktrack (n, m, p) : 'command));
      [Gramext.Stoken ("IDENT", "BackTo");
       Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e))],
      Gramext.action
        (fun (n : 'natural) _ (loc : Ploc.t) -> (VernacBackTo n : 'command));
      [Gramext.Stoken ("IDENT", "Back");
       Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e))],
      Gramext.action
        (fun (n : 'natural) _ (loc : Ploc.t) -> (VernacBack n : 'command));
      [Gramext.Stoken ("IDENT", "Back")],
      Gramext.action (fun _ (loc : Ploc.t) -> (VernacBack 1 : 'command));
      [Gramext.Stoken ("IDENT", "Reset");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e))],
      Gramext.action
        (fun (id : 'identref) _ (loc : Ploc.t) ->
           (VernacResetName id : 'command));
      [Gramext.Stoken ("IDENT", "Reset");
       Gramext.Stoken ("IDENT", "Initial")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) -> (VernacResetInitial : 'command));
      [Gramext.Stoken ("IDENT", "Restore"); Gramext.Stoken ("IDENT", "State");
       Gramext.Snterm (Gram.Entry.obj (ne_string : 'ne_string Gram.Entry.e))],
      Gramext.action
        (fun (s : 'ne_string) _ _ (loc : Ploc.t) ->
           (VernacRestoreState s : 'command));
      [Gramext.Stoken ("IDENT", "Restore"); Gramext.Stoken ("IDENT", "State");
       Gramext.Stoken ("IDENT", "")],
      Gramext.action
        (fun (s : string) _ _ (loc : Ploc.t) ->
           (VernacRestoreState s : 'command));
      [Gramext.Stoken ("IDENT", "Write"); Gramext.Stoken ("IDENT", "State");
       Gramext.Snterm (Gram.Entry.obj (ne_string : 'ne_string Gram.Entry.e))],
      Gramext.action
        (fun (s : 'ne_string) _ _ (loc : Ploc.t) ->
           (VernacWriteState s : 'command));
      [(* State management *)
       Gramext.
       Stoken
         ("IDENT", "Write");
       Gramext.Stoken ("IDENT", "State"); Gramext.Stoken ("IDENT", "")],
      Gramext.action
        (fun (s : string) _ _ (loc : Ploc.t) ->
           (VernacWriteState s : 'command))]]

(* Grammar extensions *)

let _ =
  let _ = (syntax : 'syntax Gram.Entry.e) in
  let grammar_entry_create = Gram.Entry.create in
  let only_parsing : 'only_parsing Gram.Entry.e =
    grammar_entry_create "only_parsing"
  and level : 'level Gram.Entry.e = grammar_entry_create "level"
  and syntax_modifier : 'syntax_modifier Gram.Entry.e =
    grammar_entry_create "syntax_modifier"
  and syntax_extension_type : 'syntax_extension_type Gram.Entry.e =
    grammar_entry_create "syntax_extension_type"
  and at_level : 'at_level Gram.Entry.e = grammar_entry_create "at_level"
  and constr_as_binder_kind : 'constr_as_binder_kind Gram.Entry.e =
    grammar_entry_create "constr_as_binder_kind"
  in
  Gram.extend (syntax : 'syntax Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "Reserved");
       Gramext.Stoken ("IDENT", "Notation");
       Gramext.Snterm
         (Gram.Entry.obj (ne_lstring : 'ne_lstring Gram.Entry.e));
       Gramext.srules
         [[], Gramext.action (fun (loc : Ploc.t) -> ([] : 'e__35));
          [Gramext.Stoken ("", "(");
           Gramext.Slist1sep
             (Gramext.Snterm
                (Gram.Entry.obj
                   (syntax_modifier : 'syntax_modifier Gram.Entry.e)),
              Gramext.Stoken ("", ","), false);
           Gramext.Stoken ("", ")")],
          Gramext.action
            (fun _ (l : 'syntax_modifier list) _ (loc : Ploc.t) ->
               (l : 'e__35))]],
      Gramext.action
        (fun (l : 'e__35) (s : 'ne_lstring) _ _ (loc : Ploc.t) ->
           (VernacSyntaxExtension (false, (s, l)) : 'syntax));
      [Gramext.Stoken ("IDENT", "Reserved");
       Gramext.Stoken ("IDENT", "Infix");
       Gramext.Snterm
         (Gram.Entry.obj (ne_lstring : 'ne_lstring Gram.Entry.e));
       Gramext.srules
         [[], Gramext.action (fun (loc : Ploc.t) -> ([] : 'e__34));
          [Gramext.Stoken ("", "(");
           Gramext.Slist1sep
             (Gramext.Snterm
                (Gram.Entry.obj
                   (syntax_modifier : 'syntax_modifier Gram.Entry.e)),
              Gramext.Stoken ("", ","), false);
           Gramext.Stoken ("", ")")],
          Gramext.action
            (fun _ (l : 'syntax_modifier list) _ (loc : Ploc.t) ->
               (l : 'e__34))]],
      Gramext.action
        (fun (l : 'e__34) (s : 'ne_lstring) _ _ (loc : Ploc.t) ->
           (let s = CAst.map (fun s -> "x '" ^ s ^ "' y") s in
            VernacSyntaxExtension (true, (s, l)) :
            'syntax));
      [Gramext.Stoken ("IDENT", "Format");
       Gramext.Stoken ("IDENT", "Notation"); Gramext.Stoken ("STRING", "");
       Gramext.Stoken ("STRING", ""); Gramext.Stoken ("STRING", "")],
      Gramext.action
        (fun (fmt : string) (s : string) (n : string) _ _ (loc : Ploc.t) ->
           (VernacNotationAddFormat (n, s, fmt) : 'syntax));
      [Gramext.Stoken ("IDENT", "Notation");
       Gramext.Snterm (Gram.Entry.obj (lstring : 'lstring Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.srules
         [[], Gramext.action (fun (loc : Ploc.t) -> ([] : 'e__32));
          [Gramext.Stoken ("", "(");
           Gramext.Slist1sep
             (Gramext.Snterm
                (Gram.Entry.obj
                   (syntax_modifier : 'syntax_modifier Gram.Entry.e)),
              Gramext.Stoken ("", ","), false);
           Gramext.Stoken ("", ")")],
          Gramext.action
            (fun _ (l : 'syntax_modifier list) _ (loc : Ploc.t) ->
               (l : 'e__32))];
       Gramext.Sopt
         (Gramext.srules
            [[Gramext.Stoken ("", ":"); Gramext.Stoken ("IDENT", "")],
             Gramext.action
               (fun (sc : string) _ (loc : Ploc.t) -> (sc : 'e__33))])],
      Gramext.action
        (fun (sc : 'e__33 option) (modl : 'e__32) (c : 'constr) _
             (s : 'lstring) _ (loc : Ploc.t) ->
           (VernacNotation (c, (s, modl), sc) : 'syntax));
      [Gramext.Stoken ("IDENT", "Notation");
       Gramext.Snterm (Gram.Entry.obj (identref : 'identref Gram.Entry.e));
       Gramext.Slist0
         (Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e)));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj (only_parsing : 'only_parsing Gram.Entry.e))],
      Gramext.action
        (fun (b : 'only_parsing) (c : 'constr) _ (idl : 'ident list)
             (id : 'identref) _ (loc : Ploc.t) ->
           (VernacSyntacticDefinition (id, (idl, c), b) : 'syntax));
      [Gramext.Stoken ("IDENT", "Infix");
       Gramext.Snterm
         (Gram.Entry.obj (ne_lstring : 'ne_lstring Gram.Entry.e));
       Gramext.Stoken ("", ":=");
       Gramext.Snterm (Gram.Entry.obj (constr : 'constr Gram.Entry.e));
       Gramext.srules
         [[], Gramext.action (fun (loc : Ploc.t) -> ([] : 'e__30));
          [Gramext.Stoken ("", "(");
           Gramext.Slist1sep
             (Gramext.Snterm
                (Gram.Entry.obj
                   (syntax_modifier : 'syntax_modifier Gram.Entry.e)),
              Gramext.Stoken ("", ","), false);
           Gramext.Stoken ("", ")")],
          Gramext.action
            (fun _ (l : 'syntax_modifier list) _ (loc : Ploc.t) ->
               (l : 'e__30))];
       Gramext.Sopt
         (Gramext.srules
            [[Gramext.Stoken ("", ":"); Gramext.Stoken ("IDENT", "")],
             Gramext.action
               (fun (sc : string) _ (loc : Ploc.t) -> (sc : 'e__31))])],
      Gramext.action
        (fun (sc : 'e__31 option) (modl : 'e__30) (p : 'constr) _
             (op : 'ne_lstring) _ (loc : Ploc.t) ->
           (VernacInfix ((op, modl), p, sc) : 'syntax));
      [Gramext.Stoken ("IDENT", "Bind"); Gramext.Stoken ("IDENT", "Scope");
       Gramext.Stoken ("IDENT", ""); Gramext.Stoken ("", "with");
       Gramext.Slist1
         (Gramext.Snterm
            (Gram.Entry.obj (class_rawexpr : 'class_rawexpr Gram.Entry.e)))],
      Gramext.action
        (fun (refl : 'class_rawexpr list) _ (sc : string) _ _
             (loc : Ploc.t) ->
           (VernacBindScope (sc, refl) : 'syntax));
      [Gramext.Stoken ("IDENT", "Undelimit");
       Gramext.Stoken ("IDENT", "Scope"); Gramext.Stoken ("IDENT", "")],
      Gramext.action
        (fun (sc : string) _ _ (loc : Ploc.t) ->
           (VernacDelimiters (sc, None) : 'syntax));
      [Gramext.Stoken ("IDENT", "Delimit"); Gramext.Stoken ("IDENT", "Scope");
       Gramext.Stoken ("IDENT", ""); Gramext.Stoken ("", "with");
       Gramext.Stoken ("IDENT", "")],
      Gramext.action
        (fun (key : string) _ (sc : string) _ _ (loc : Ploc.t) ->
           (VernacDelimiters (sc, Some key) : 'syntax));
      [Gramext.Stoken ("IDENT", "Close"); Gramext.Stoken ("IDENT", "Scope");
       Gramext.Stoken ("IDENT", "")],
      Gramext.action
        (fun (sc : string) _ _ (loc : Ploc.t) ->
           (VernacOpenCloseScope (false, sc) : 'syntax));
      [Gramext.Stoken ("IDENT", "Open"); Gramext.Stoken ("IDENT", "Scope");
       Gramext.Stoken ("IDENT", "")],
      Gramext.action
        (fun (sc : string) _ _ (loc : Ploc.t) ->
           (VernacOpenCloseScope (true, sc) : 'syntax))]];
  Gram.extend (only_parsing : 'only_parsing Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> (None : 'only_parsing));
      [Gramext.Stoken ("", "("); Gramext.Stoken ("IDENT", "compat");
       Gramext.Stoken ("STRING", ""); Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (s : string) _ _ (loc : Ploc.t) ->
           (Some (parse_compat_version s) : 'only_parsing));
      [Gramext.Stoken ("", "("); Gramext.Stoken ("IDENT", "only");
       Gramext.Stoken ("IDENT", "parsing"); Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ _ _ _ (loc : Ploc.t) ->
           (Some Flags.Current : 'only_parsing))]];
  Gram.extend (level : 'level Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "next"); Gramext.Stoken ("IDENT", "level")],
      Gramext.action (fun _ _ (loc : Ploc.t) -> (NextLevel : 'level));
      [Gramext.Stoken ("IDENT", "level");
       Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e))],
      Gramext.action
        (fun (n : 'natural) _ (loc : Ploc.t) -> (NumLevel n : 'level))]];
  Gram.extend (syntax_modifier : 'syntax_modifier Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "");
       Gramext.Snterm
         (Gram.Entry.obj
            (syntax_extension_type : 'syntax_extension_type Gram.Entry.e))],
      Gramext.action
        (fun (typ : 'syntax_extension_type) (x : string) (loc : Ploc.t) ->
           (SetEntryType (x, typ) : 'syntax_modifier));
      [Gramext.Stoken ("IDENT", "");
       Gramext.Snterm
         (Gram.Entry.obj
            (constr_as_binder_kind : 'constr_as_binder_kind Gram.Entry.e))],
      Gramext.action
        (fun (b : 'constr_as_binder_kind) (x : string) (loc : Ploc.t) ->
           (SetItemLevelAsBinder ([x], b, None) : 'syntax_modifier));
      [Gramext.Stoken ("IDENT", ""); Gramext.Stoken ("", "at");
       Gramext.Snterm (Gram.Entry.obj (level : 'level Gram.Entry.e));
       Gramext.Snterm
         (Gram.Entry.obj
            (constr_as_binder_kind : 'constr_as_binder_kind Gram.Entry.e))],
      Gramext.action
        (fun (b : 'constr_as_binder_kind) (lev : 'level) _ (x : string)
             (loc : Ploc.t) ->
           (SetItemLevelAsBinder ([x], b, Some lev) : 'syntax_modifier));
      [Gramext.Stoken ("IDENT", ""); Gramext.Stoken ("", "at");
       Gramext.Snterm (Gram.Entry.obj (level : 'level Gram.Entry.e))],
      Gramext.action
        (fun (lev : 'level) _ (x : string) (loc : Ploc.t) ->
           (SetItemLevel ([x], lev) : 'syntax_modifier));
      [Gramext.Stoken ("IDENT", ""); Gramext.Stoken ("", ",");
       Gramext.Slist1sep
         (Gramext.srules
            [[Gramext.Stoken ("IDENT", "")],
             Gramext.action
               (fun (id : string) (loc : Ploc.t) -> (id : 'e__38))],
          Gramext.Stoken ("", ","), false);
       Gramext.Stoken ("", "at");
       Gramext.Snterm (Gram.Entry.obj (level : 'level Gram.Entry.e))],
      Gramext.action
        (fun (lev : 'level) _ (l : 'e__38 list) _ (x : string)
             (loc : Ploc.t) ->
           (SetItemLevel (x :: l, lev) : 'syntax_modifier));
      [Gramext.Stoken ("IDENT", "format");
       Gramext.srules
         [[Gramext.Stoken ("STRING", "")],
          Gramext.action
            (fun (s : string) (loc : Ploc.t) ->
               (CAst.make ~loc:((!@) loc) s : 'e__36))];
       Gramext.Sopt
         (Gramext.srules
            [[Gramext.Stoken ("STRING", "")],
             Gramext.action
               (fun (s : string) (loc : Ploc.t) ->
                  (CAst.make ~loc:((!@) loc) s : 'e__37))])],
      Gramext.action
        (fun (s2 : 'e__37 option) (s1 : 'e__36) _ (loc : Ploc.t) ->
           (match s1, s2 with
              {CAst.v = k}, Some s -> SetFormat (k, s)
            | s, None -> SetFormat ("text", s) :
            'syntax_modifier));
      [Gramext.Stoken ("IDENT", "compat"); Gramext.Stoken ("STRING", "")],
      Gramext.action
        (fun (s : string) _ (loc : Ploc.t) ->
           (SetCompatVersion (parse_compat_version s) : 'syntax_modifier));
      [Gramext.Stoken ("IDENT", "only"); Gramext.Stoken ("IDENT", "parsing")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) -> (SetOnlyParsing : 'syntax_modifier));
      [Gramext.Stoken ("IDENT", "only");
       Gramext.Stoken ("IDENT", "printing")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) -> (SetOnlyPrinting : 'syntax_modifier));
      [Gramext.Stoken ("IDENT", "no");
       Gramext.Stoken ("IDENT", "associativity")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) -> (SetAssoc NonA : 'syntax_modifier));
      [Gramext.Stoken ("IDENT", "right");
       Gramext.Stoken ("IDENT", "associativity")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) -> (SetAssoc RightA : 'syntax_modifier));
      [Gramext.Stoken ("IDENT", "left");
       Gramext.Stoken ("IDENT", "associativity")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) -> (SetAssoc LeftA : 'syntax_modifier));
      [Gramext.Stoken ("", "at"); Gramext.Stoken ("IDENT", "level");
       Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e))],
      Gramext.action
        (fun (n : 'natural) _ _ (loc : Ploc.t) ->
           (SetLevel n : 'syntax_modifier))]];
  Gram.extend (syntax_extension_type : 'syntax_extension_type Gram.Entry.e)
    None
    [None, None,
     [[Gramext.Stoken ("IDENT", "closed");
       Gramext.Stoken ("IDENT", "binder")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) -> (ETBinder false : 'syntax_extension_type));
      [Gramext.Stoken ("IDENT", "strict");
       Gramext.Stoken ("IDENT", "pattern"); Gramext.Stoken ("", "at");
       Gramext.Stoken ("IDENT", "level");
       Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e))],
      Gramext.action
        (fun (n : 'natural) _ _ _ _ (loc : Ploc.t) ->
           (ETPattern (true, Some n) : 'syntax_extension_type));
      [Gramext.Stoken ("IDENT", "strict");
       Gramext.Stoken ("IDENT", "pattern")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) ->
           (ETPattern (true, None) : 'syntax_extension_type));
      [Gramext.Stoken ("IDENT", "pattern"); Gramext.Stoken ("", "at");
       Gramext.Stoken ("IDENT", "level");
       Gramext.Snterm (Gram.Entry.obj (natural : 'natural Gram.Entry.e))],
      Gramext.action
        (fun (n : 'natural) _ _ _ (loc : Ploc.t) ->
           (ETPattern (false, Some n) : 'syntax_extension_type));
      [Gramext.Stoken ("IDENT", "pattern")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           (ETPattern (false, None) : 'syntax_extension_type));
      [Gramext.Stoken ("IDENT", "constr");
       Gramext.Sopt
         (Gramext.Snterm
            (Gram.Entry.obj (at_level : 'at_level Gram.Entry.e)));
       Gramext.Snterm
         (Gram.Entry.obj
            (constr_as_binder_kind : 'constr_as_binder_kind Gram.Entry.e))],
      Gramext.action
        (fun (b : 'constr_as_binder_kind) (n : 'at_level option) _
             (loc : Ploc.t) ->
           (ETConstrAsBinder (b, n) : 'syntax_extension_type));
      [Gramext.Stoken ("IDENT", "binder")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (ETBinder true : 'syntax_extension_type));
      [Gramext.Stoken ("IDENT", "bigint")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (ETBigint : 'syntax_extension_type));
      [Gramext.Stoken ("IDENT", "global")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (ETReference : 'syntax_extension_type));
      [Gramext.Stoken ("IDENT", "ident")],
      Gramext.action
        (fun _ (loc : Ploc.t) -> (ETName : 'syntax_extension_type))]];
  Gram.extend (at_level : 'at_level Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "at");
       Gramext.Snterm (Gram.Entry.obj (level : 'level Gram.Entry.e))],
      Gramext.action (fun (n : 'level) _ (loc : Ploc.t) -> (n : 'at_level))]];
  Gram.extend (constr_as_binder_kind : 'constr_as_binder_kind Gram.Entry.e)
    None
    [None, None,
     [[Gramext.Stoken ("", "as"); Gramext.Stoken ("IDENT", "strict");
       Gramext.Stoken ("IDENT", "pattern")],
      Gramext.action
        (fun _ _ _ (loc : Ploc.t) ->
           (AsStrictPattern : 'constr_as_binder_kind));
      [Gramext.Stoken ("", "as"); Gramext.Stoken ("IDENT", "pattern")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) ->
           (AsIdentOrPattern : 'constr_as_binder_kind));
      [Gramext.Stoken ("", "as"); Gramext.Stoken ("IDENT", "ident")],
      Gramext.action
        (fun _ _ (loc : Ploc.t) -> (AsIdent : 'constr_as_binder_kind))]]
