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

open Pcoq
open Pcoq.Prim

let prim_kw = ["{"; "}"; "["; "]"; "("; ")"; "'"]
let _ = List.iter CLexer.add_keyword prim_kw


let local_make_qualid l id = make_qualid (DirPath.make l) id

let my_int_of_string loc s =
  try
    let n = int_of_string s in
    (* To avoid Array.make errors (that e.g. Undo uses), we set a *)
    (* more restricted limit than int_of_string does *)
    if n > 1024 * 2048 then raise Exit;
    n
  with Failure _ | Exit ->
    CErrors.user_err ~loc (Pp.str "Cannot support a so large number.")

let _ =
  let _ = (bigint : 'bigint Gram.Entry.e)
  and _ = (natural : 'natural Gram.Entry.e)
  and _ = (integer : 'integer Gram.Entry.e)
  and _ = (identref : 'identref Gram.Entry.e)
  and _ = (name : 'name Gram.Entry.e)
  and _ = (ident : 'ident Gram.Entry.e)
  and _ = (var : 'var Gram.Entry.e)
  and _ = (preident : 'preident Gram.Entry.e)
  and _ = (fullyqualid : 'fullyqualid Gram.Entry.e)
  and _ = (qualid : 'qualid Gram.Entry.e)
  and _ = (reference : 'reference Gram.Entry.e)
  and _ = (dirpath : 'dirpath Gram.Entry.e)
  and _ = (ne_lstring : 'ne_lstring Gram.Entry.e)
  and _ = (ne_string : 'ne_string Gram.Entry.e)
  and _ = (string : 'string Gram.Entry.e)
  and _ = (lstring : 'lstring Gram.Entry.e)
  and _ = (pattern_ident : 'pattern_ident Gram.Entry.e)
  and _ = (pattern_identref : 'pattern_identref Gram.Entry.e)
  and _ = (by_notation : 'by_notation Gram.Entry.e)
  and _ = (smart_global : 'smart_global Gram.Entry.e) in
  let grammar_entry_create = Gram.Entry.create in
  let field : 'field Gram.Entry.e = grammar_entry_create "field"
  and fields : 'fields Gram.Entry.e = grammar_entry_create "fields"
  and basequalid : 'basequalid Gram.Entry.e =
    grammar_entry_create "basequalid"
  in
  Gram.extend (preident : 'preident Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "")],
      Gramext.action (fun (s : string) (loc : Ploc.t) -> (s : 'preident))]];
  Gram.extend (ident : 'ident Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("IDENT", "")],
      Gramext.action
        (fun (s : string) (loc : Ploc.t) -> (Id.of_string s : 'ident))]];
  Gram.extend (pattern_ident : 'pattern_ident Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("LEFTQMARK", "");
       Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e))],
      Gramext.action
        (fun (id : 'ident) _ (loc : Ploc.t) -> (id : 'pattern_ident))]];
  Gram.extend (pattern_identref : 'pattern_identref Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (pattern_ident : 'pattern_ident Gram.Entry.e))],
      Gramext.action
        (fun (id : 'pattern_ident) (loc : Ploc.t) ->
           (CAst.make ~loc:((!@) loc) id : 'pattern_identref))]];
  Gram.extend (var : 'var Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e))],
      Gramext.action
        (fun (id : 'ident) (loc : Ploc.t) ->
           (CAst.make ~loc:((!@) loc) id : 'var))]];
  Gram.extend (identref : 'identref Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e))],
      Gramext.action
        (fun (id : 'ident) (loc : Ploc.t) ->
           (CAst.make ~loc:((!@) loc) id : 'identref))]];
  Gram.extend (field : 'field Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("FIELD", "")],
      Gramext.action
        (fun (s : string) (loc : Ploc.t) -> (Id.of_string s : 'field))]];
  Gram.extend (fields : 'fields Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (field : 'field Gram.Entry.e))],
      Gramext.action (fun (id : 'field) (loc : Ploc.t) -> ([], id : 'fields));
      [Gramext.Snterm (Gram.Entry.obj (field : 'field Gram.Entry.e));
       Gramext.Sself],
      Gramext.action
        (fun (l, id' : 'fields) (id : 'field) (loc : Ploc.t) ->
           (l @ [id], id' : 'fields))]];
  Gram.extend (fullyqualid : 'fullyqualid Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e))],
      Gramext.action
        (fun (id : 'ident) (loc : Ploc.t) ->
           (CAst.make ~loc:((!@) loc) [id] : 'fullyqualid));
      [Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (fields : 'fields Gram.Entry.e))],
      Gramext.action
        (fun (l, id' : 'fields) (id : 'ident) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (id :: List.rev (id' :: l)) :
            'fullyqualid))]];
  Gram.extend (basequalid : 'basequalid Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e))],
      Gramext.action
        (fun (id : 'ident) (loc : Ploc.t) ->
           (qualid_of_ident id : 'basequalid));
      [Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (fields : 'fields Gram.Entry.e))],
      Gramext.action
        (fun (l, id' : 'fields) (id : 'ident) (loc : Ploc.t) ->
           (local_make_qualid (l @ [id]) id' : 'basequalid))]];
  Gram.extend (name : 'name Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e))],
      Gramext.action
        (fun (id : 'ident) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (Name id) : 'name));
      [Gramext.Stoken ("IDENT", "_")],
      Gramext.action
        (fun _ (loc : Ploc.t) ->
           (CAst.make ~loc:((!@) loc) Anonymous : 'name))]];
  Gram.extend (reference : 'reference Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e))],
      Gramext.action
        (fun (id : 'ident) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (Ident id) : 'reference));
      [Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e));
       Gramext.Snterm (Gram.Entry.obj (fields : 'fields Gram.Entry.e))],
      Gramext.action
        (fun (l, id' : 'fields) (id : 'ident) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc))
              (Qualid (local_make_qualid (l @ [id]) id')) :
            'reference))]];
  Gram.extend (by_notation : 'by_notation Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (ne_string : 'ne_string Gram.Entry.e));
       Gramext.Sopt
         (Gramext.srules
            [[Gramext.Stoken ("", "%"); Gramext.Stoken ("IDENT", "")],
             Gramext.action
               (fun (key : string) _ (loc : Ploc.t) -> (key : 'e__1))])],
      Gramext.action
        (fun (sc : 'e__1 option) (s : 'ne_string) (loc : Ploc.t) ->
           (s, sc : 'by_notation))]];
  Gram.extend (smart_global : 'smart_global Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (by_notation : 'by_notation Gram.Entry.e))],
      Gramext.action
        (fun (ntn : 'by_notation) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (Misctypes.ByNotation ntn) :
            'smart_global));
      [Gramext.Snterm (Gram.Entry.obj (reference : 'reference Gram.Entry.e))],
      Gramext.action
        (fun (c : 'reference) (loc : Ploc.t) ->
           ((@@) (CAst.make ~loc:((!@) loc)) (Misctypes.AN c) :
            'smart_global))]];
  Gram.extend (qualid : 'qualid Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm
         (Gram.Entry.obj (basequalid : 'basequalid Gram.Entry.e))],
      Gramext.action
        (fun (qid : 'basequalid) (loc : Ploc.t) ->
           (CAst.make ~loc:((!@) loc) qid : 'qualid))]];
  Gram.extend (ne_string : 'ne_string Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("STRING", "")],
      Gramext.action
        (fun (s : string) (loc : Ploc.t) ->
           (if s = "" then
              CErrors.user_err ~loc:((!@) loc) (Pp.str "Empty string.");
            s :
            'ne_string))]];
  Gram.extend (ne_lstring : 'ne_lstring Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (ne_string : 'ne_string Gram.Entry.e))],
      Gramext.action
        (fun (s : 'ne_string) (loc : Ploc.t) ->
           (CAst.make ~loc:((!@) loc) s : 'ne_lstring))]];
  Gram.extend (dirpath : 'dirpath Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (ident : 'ident Gram.Entry.e));
       Gramext.Slist0
         (Gramext.Snterm (Gram.Entry.obj (field : 'field Gram.Entry.e)))],
      Gramext.action
        (fun (l : 'field list) (id : 'ident) (loc : Ploc.t) ->
           (DirPath.make (List.rev (id :: l)) : 'dirpath))]];
  Gram.extend (string : 'string Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("STRING", "")],
      Gramext.action (fun (s : string) (loc : Ploc.t) -> (s : 'string))]];
  Gram.extend (lstring : 'lstring Gram.Entry.e) None
    [None, None,
     [[Gramext.Snterm (Gram.Entry.obj (string : 'string Gram.Entry.e))],
      Gramext.action
        (fun (s : 'string) (loc : Ploc.t) ->
           (CAst.make ~loc:((!@) loc) s : 'lstring))]];
  Gram.extend (integer : 'integer Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("", "-"); Gramext.Stoken ("INT", "")],
      Gramext.action
        (fun (i : string) _ (loc : Ploc.t) ->
           (-my_int_of_string ((!@) loc) i : 'integer));
      [Gramext.Stoken ("INT", "")],
      Gramext.action
        (fun (i : string) (loc : Ploc.t) ->
           (my_int_of_string ((!@) loc) i : 'integer))]];
  Gram.extend (natural : 'natural Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("INT", "")],
      Gramext.action
        (fun (i : string) (loc : Ploc.t) ->
           (my_int_of_string ((!@) loc) i : 'natural))]];
  Gram.extend (bigint : 'bigint Gram.Entry.e) None
    [None, None,
     [[Gramext.Stoken ("INT", "")],
      Gramext.action (fun (i : string) (loc : Ploc.t) -> (i : 'bigint))]]
