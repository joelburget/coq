(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*
  Syntax for the subtac terms and types.
  Elaborated from correctness/psyntax.ml4 by Jean-Christophe Filliâtre *)

open Libnames
open Constrexpr
open Constrexpr_ops
open Stdarg
open Tacarg
open Extraargs

let (set_default_tactic, get_default_tactic, print_default_tactic) =
  Tactic_option.declare_tactic_option "Program tactic"

let () =
  (** Delay to recover the tactic imperatively *)
  let tac =
    Proofview.tclBIND (Proofview.tclUNIT ())
      (fun () -> snd (get_default_tactic ()))
  in
  Obligations.default_tactic := tac

let with_tac f tac =
  let env = Genintern.empty_glob_sign (Global.env ()) in
  let tac =
    match tac with
      None -> None
    | Some tac ->
        let tac = Genarg.in_gen (Genarg.rawwit wit_ltac) tac in
        let (_, tac) = Genintern.generic_intern env tac in Some tac
  in
  f tac

(* We define new entries for programs, with the use of this module
 * Subtac. These entries are named Subtac.<foo>
 *)

module Gram = Pcoq.Gram
module Tactic = Pltac

open Pcoq

let sigref =
  mkRefC
    ((@@) CAst.make
       (Qualid (Libnames.qualid_of_string "Coq.Init.Specif.sig")))

type 'a withtac_argtype =
  (Tacexpr.raw_tactic_expr option, 'a) Genarg.abstract_argument_type

let wit_withtac : Tacexpr.raw_tactic_expr option Genarg.uniform_genarg_type =
  Genarg.create_arg "withtac"

let withtac =
  Pcoq.create_generic_entry Pcoq.utactic "withtac" (Genarg.rawwit wit_withtac)

let _ =
  let _ = (withtac : 'withtac Gram.Entry.e) in
  Gram.extend (withtac : 'withtac Gram.Entry.e) None
    [None, None,
     [[], Gramext.action (fun (loc : Ploc.t) -> (None : 'withtac));
      [Gramext.Stoken ("", "with");
       Gramext.Snterm
         (Gram.Entry.obj (Tactic.tactic : 'Tactic__tactic Gram.Entry.e))],
      Gramext.action
        (fun (t : 'Tactic__tactic) _ (loc : Ploc.t) -> (Some t : 'withtac))]];
  Gram.extend (Constr.closed_binder : 'Constr__closed_binder Gram.Entry.e)
    None
    [None, None,
     [[Gramext.Stoken ("", "(");
       Gramext.Snterm (Gram.Entry.obj (Prim.name : 'Prim__name Gram.Entry.e));
       Gramext.Stoken ("", ":");
       Gramext.Snterm
         (Gram.Entry.obj (Constr.lconstr : 'Constr__lconstr Gram.Entry.e));
       Gramext.Stoken ("", "|");
       Gramext.Snterm
         (Gram.Entry.obj (Constr.lconstr : 'Constr__lconstr Gram.Entry.e));
       Gramext.Stoken ("", ")")],
      Gramext.action
        (fun _ (c : 'Constr__lconstr) _ (t : 'Constr__lconstr) _
             (id : 'Prim__name) _ (loc : Ploc.t) ->
           (let typ =
              mkAppC (sigref, [mkLambdaC ([id], default_binder_kind, t, c)])
            in
            [CLocalAssum ([id], default_binder_kind, typ)] :
            'Constr__closed_binder))]]

open Obligations

let obligation obl tac = with_tac (fun t -> Obligations.obligation obl t) tac
let next_obligation obl tac =
  with_tac (fun t -> Obligations.next_obligation obl t) tac

let classify_obbl _ =
  Vernacexpr.(VtStartProof ("Classic", Doesn'tGuaranteeOpacity, []), VtLater)

let _ =
  CList.iteri
    (fun i (depr, f) -> Vernacinterp.vinterp_add depr ("Obligations", i) f)
    [false,
     (function
        [num; name; t; tac] ->
          let num = Genarg.out_gen (Genarg.rawwit wit_integer) num in
          let name = Genarg.out_gen (Genarg.rawwit wit_ident) name in
          let t = Genarg.out_gen (Genarg.rawwit wit_lglob) t in
          let tac = Genarg.out_gen (Genarg.rawwit wit_withtac) tac in
          (fun ~atts ~st ->
             let () = obligation (num, Some name, Some t) tac in st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [num; name; tac] ->
          let num = Genarg.out_gen (Genarg.rawwit wit_integer) num in
          let name = Genarg.out_gen (Genarg.rawwit wit_ident) name in
          let tac = Genarg.out_gen (Genarg.rawwit wit_withtac) tac in
          (fun ~atts ~st ->
             let () = obligation (num, Some name, None) tac in st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [num; t; tac] ->
          let num = Genarg.out_gen (Genarg.rawwit wit_integer) num in
          let t = Genarg.out_gen (Genarg.rawwit wit_lglob) t in
          let tac = Genarg.out_gen (Genarg.rawwit wit_withtac) tac in
          (fun ~atts ~st -> let () = obligation (num, None, Some t) tac in st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [num; tac] ->
          let num = Genarg.out_gen (Genarg.rawwit wit_integer) num in
          let tac = Genarg.out_gen (Genarg.rawwit wit_withtac) tac in
          (fun ~atts ~st -> let () = obligation (num, None, None) tac in st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [name; tac] ->
          let name = Genarg.out_gen (Genarg.rawwit wit_ident) name in
          let tac = Genarg.out_gen (Genarg.rawwit wit_withtac) tac in
          (fun ~atts ~st -> let () = next_obligation (Some name) tac in st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [tac] ->
          let tac = Genarg.out_gen (Genarg.rawwit wit_withtac) tac in
          (fun ~atts ~st -> let () = next_obligation None tac in st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("Obligations", i) f)
    [(function
        [num; name; t; tac] -> (fun loc -> classify_obbl "Obligations")
      | _ -> failwith "Extension: cannot occur");
     (function
        [num; name; tac] -> (fun loc -> classify_obbl "Obligations")
      | _ -> failwith "Extension: cannot occur");
     (function
        [num; t; tac] -> (fun loc -> classify_obbl "Obligations")
      | _ -> failwith "Extension: cannot occur");
     (function
        [num; tac] -> (fun loc -> classify_obbl "Obligations")
      | _ -> failwith "Extension: cannot occur");
     (function
        [name; tac] -> (fun loc -> classify_obbl "Obligations")
      | _ -> failwith "Extension: cannot occur");
     (function
        [tac] -> (fun loc -> classify_obbl "Obligations")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("Obligations", i) None r)
    [[Egramml.GramTerminal "Obligation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_integer),
            Extend.Aentry (Pcoq.genarg_grammar wit_integer)));
      Egramml.GramTerminal "of";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)));
      Egramml.GramTerminal ":";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_lglob),
            Extend.Aentry (Pcoq.genarg_grammar wit_lglob)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_withtac),
            Extend.Aentry (Pcoq.genarg_grammar wit_withtac)))];
     [Egramml.GramTerminal "Obligation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_integer),
            Extend.Aentry (Pcoq.genarg_grammar wit_integer)));
      Egramml.GramTerminal "of";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_withtac),
            Extend.Aentry (Pcoq.genarg_grammar wit_withtac)))];
     [Egramml.GramTerminal "Obligation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_integer),
            Extend.Aentry (Pcoq.genarg_grammar wit_integer)));
      Egramml.GramTerminal ":";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_lglob),
            Extend.Aentry (Pcoq.genarg_grammar wit_lglob)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_withtac),
            Extend.Aentry (Pcoq.genarg_grammar wit_withtac)))];
     [Egramml.GramTerminal "Obligation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_integer),
            Extend.Aentry (Pcoq.genarg_grammar wit_integer)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_withtac),
            Extend.Aentry (Pcoq.genarg_grammar wit_withtac)))];
     [Egramml.GramTerminal "Next"; Egramml.GramTerminal "Obligation";
      Egramml.GramTerminal "of";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)));
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_withtac),
            Extend.Aentry (Pcoq.genarg_grammar wit_withtac)))];
     [Egramml.GramTerminal "Next"; Egramml.GramTerminal "Obligation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_withtac),
            Extend.Aentry (Pcoq.genarg_grammar wit_withtac)))]]

let _ =
  CList.iteri
    (fun i (depr, f) ->
       Vernacinterp.vinterp_add depr ("Solve_Obligation", i) f)
    [false,
     (function
        [num; name; t] ->
          let num = Genarg.out_gen (Genarg.rawwit wit_integer) num in
          let name = Genarg.out_gen (Genarg.rawwit wit_ident) name in
          let t = Genarg.out_gen (Genarg.rawwit wit_tactic) t in
          (fun ~atts ~st ->
             let () =
               try_solve_obligation num (Some name)
                 (Some (Tacinterp.interp t))
             in
             st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [num; t] ->
          let num = Genarg.out_gen (Genarg.rawwit wit_integer) num in
          let t = Genarg.out_gen (Genarg.rawwit wit_tactic) t in
          (fun ~atts ~st ->
             let () =
               try_solve_obligation num None (Some (Tacinterp.interp t))
             in
             st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("Solve_Obligation", i) f)
    [(function
        [num; name; t] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "Solve_Obligation")
      | _ -> failwith "Extension: cannot occur");
     (function
        [num; t] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "Solve_Obligation")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("Solve_Obligation", i) None r)
    [[Egramml.GramTerminal "Solve"; Egramml.GramTerminal "Obligation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_integer),
            Extend.Aentry (Pcoq.genarg_grammar wit_integer)));
      Egramml.GramTerminal "of";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)));
      Egramml.GramTerminal "with";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_tactic),
            Extend.Aentry (Pcoq.genarg_grammar wit_tactic)))];
     [Egramml.GramTerminal "Solve"; Egramml.GramTerminal "Obligation";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_integer),
            Extend.Aentry (Pcoq.genarg_grammar wit_integer)));
      Egramml.GramTerminal "with";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_tactic),
            Extend.Aentry (Pcoq.genarg_grammar wit_tactic)))]]

let _ =
  CList.iteri
    (fun i (depr, f) ->
       Vernacinterp.vinterp_add depr ("Solve_Obligations", i) f)
    [false,
     (function
        [name; t] ->
          let name = Genarg.out_gen (Genarg.rawwit wit_ident) name in
          let t = Genarg.out_gen (Genarg.rawwit wit_tactic) t in
          (fun ~atts ~st ->
             let () =
               try_solve_obligations (Some name) (Some (Tacinterp.interp t))
             in
             st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [t] ->
          let t = Genarg.out_gen (Genarg.rawwit wit_tactic) t in
          (fun ~atts ~st ->
             let () =
               try_solve_obligations None (Some (Tacinterp.interp t))
             in
             st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [] ->
          (fun ~atts ~st -> let () = try_solve_obligations None None in st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("Solve_Obligations", i) f)
    [(function
        [name; t] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "Solve_Obligations")
      | _ -> failwith "Extension: cannot occur");
     (function
        [t] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "Solve_Obligations")
      | _ -> failwith "Extension: cannot occur");
     (function
        [] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "Solve_Obligations")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("Solve_Obligations", i) None r)
    [[Egramml.GramTerminal "Solve"; Egramml.GramTerminal "Obligations";
      Egramml.GramTerminal "of";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)));
      Egramml.GramTerminal "with";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_tactic),
            Extend.Aentry (Pcoq.genarg_grammar wit_tactic)))];
     [Egramml.GramTerminal "Solve"; Egramml.GramTerminal "Obligations";
      Egramml.GramTerminal "with";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_tactic),
            Extend.Aentry (Pcoq.genarg_grammar wit_tactic)))];
     [Egramml.GramTerminal "Solve"; Egramml.GramTerminal "Obligations"]]

let _ =
  CList.iteri
    (fun i (depr, f) ->
       Vernacinterp.vinterp_add depr ("Solve_All_Obligations", i) f)
    [false,
     (function
        [t] ->
          let t = Genarg.out_gen (Genarg.rawwit wit_tactic) t in
          (fun ~atts ~st ->
             let () = solve_all_obligations (Some (Tacinterp.interp t)) in st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [] -> (fun ~atts ~st -> let () = solve_all_obligations None in st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier
         ("Solve_All_Obligations", i) f)
    [(function
        [t] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "Solve_All_Obligations")
      | _ -> failwith "Extension: cannot occur");
     (function
        [] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "Solve_All_Obligations")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("Solve_All_Obligations", i) None
         r)
    [[Egramml.GramTerminal "Solve"; Egramml.GramTerminal "All";
      Egramml.GramTerminal "Obligations"; Egramml.GramTerminal "with";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_tactic),
            Extend.Aentry (Pcoq.genarg_grammar wit_tactic)))];
     [Egramml.GramTerminal "Solve"; Egramml.GramTerminal "All";
      Egramml.GramTerminal "Obligations"]]

let _ =
  CList.iteri
    (fun i (depr, f) ->
       Vernacinterp.vinterp_add depr ("Admit_Obligations", i) f)
    [false,
     (function
        [name] ->
          let name = Genarg.out_gen (Genarg.rawwit wit_ident) name in
          (fun ~atts ~st -> let () = admit_obligations (Some name) in st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [] -> (fun ~atts ~st -> let () = admit_obligations None in st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("Admit_Obligations", i) f)
    [(function
        [name] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "Admit_Obligations")
      | _ -> failwith "Extension: cannot occur");
     (function
        [] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff)
               "Admit_Obligations")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("Admit_Obligations", i) None r)
    [[Egramml.GramTerminal "Admit"; Egramml.GramTerminal "Obligations";
      Egramml.GramTerminal "of";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))];
     [Egramml.GramTerminal "Admit"; Egramml.GramTerminal "Obligations"]]

let _ =
  CList.iteri
    (fun i (depr, f) -> Vernacinterp.vinterp_add depr ("Set_Solver", i) f)
    [false,
     (function
        [t] ->
          let t = Genarg.out_gen (Genarg.rawwit wit_tactic) t in
          (fun ~atts ~st ->
             let open Vernacinterp in
             begin
               set_default_tactic
                 (Locality.make_section_locality atts.locality)
                 (Tacintern.glob_tactic t);
               st
             end)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("Set_Solver", i) f)
    [(function
        [t] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_sideeff) "Set_Solver")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("Set_Solver", i) None r)
    [[Egramml.GramTerminal "Obligation"; Egramml.GramTerminal "Tactic";
      Egramml.GramTerminal ":=";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_tactic),
            Extend.Aentry (Pcoq.genarg_grammar wit_tactic)))]]

open Pp

let _ =
  CList.iteri
    (fun i (depr, f) -> Vernacinterp.vinterp_add depr ("Show_Solver", i) f)
    [false,
     (function
        [] ->
          (fun ~atts ~st ->
             let () =
               Feedback.msg_info
                 ((++) (str "Program obligation tactic is ")
                    (print_default_tactic ()))
             in
             st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("Show_Solver", i) f)
    [(function
        [] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_query) "Show_Solver")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("Show_Solver", i) None r)
    [[Egramml.GramTerminal "Show"; Egramml.GramTerminal "Obligation";
      Egramml.GramTerminal "Tactic"]]

let _ =
  CList.iteri
    (fun i (depr, f) ->
       Vernacinterp.vinterp_add depr ("Show_Obligations", i) f)
    [false,
     (function
        [name] ->
          let name = Genarg.out_gen (Genarg.rawwit wit_ident) name in
          (fun ~atts ~st -> let () = show_obligations (Some name) in st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [] -> (fun ~atts ~st -> let () = show_obligations None in st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("Show_Obligations", i) f)
    [(function
        [name] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_query)
               "Show_Obligations")
      | _ -> failwith "Extension: cannot occur");
     (function
        [] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_query)
               "Show_Obligations")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("Show_Obligations", i) None r)
    [[Egramml.GramTerminal "Obligations"; Egramml.GramTerminal "of";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))];
     [Egramml.GramTerminal "Obligations"]]

let _ =
  CList.iteri
    (fun i (depr, f) -> Vernacinterp.vinterp_add depr ("Show_Preterm", i) f)
    [false,
     (function
        [name] ->
          let name = Genarg.out_gen (Genarg.rawwit wit_ident) name in
          (fun ~atts ~st ->
             let () = Feedback.msg_info (show_term (Some name)) in st)
      | _ -> failwith "Extension: cannot occur");
     false,
     (function
        [] ->
          (fun ~atts ~st -> let () = Feedback.msg_info (show_term None) in st)
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i f ->
       Vernac_classifier.declare_vernac_classifier ("Show_Preterm", i) f)
    [(function
        [name] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_query) "Show_Preterm")
      | _ -> failwith "Extension: cannot occur");
     (function
        [] ->
          (fun loc ->
             (fun _ -> Vernac_classifier.classify_as_query) "Show_Preterm")
      | _ -> failwith "Extension: cannot occur")];
  CList.iteri
    (fun i r ->
       Egramml.extend_vernac_command_grammar ("Show_Preterm", i) None r)
    [[Egramml.GramTerminal "Preterm"; Egramml.GramTerminal "of";
      Egramml.GramNonTerminal
        (Loc.tag
           (Some (Genarg.rawwit wit_ident),
            Extend.Aentry (Pcoq.genarg_grammar wit_ident)))];
     [Egramml.GramTerminal "Preterm"]]

open Pp

(* Declare a printer for the content of Program tactics *)
let () =
  let printer _ _ _ =
    function
      None -> mt ()
    | Some tac ->
        (++) ((++) (str "with") (spc ())) (Pptactic.pr_raw_tactic tac)
  in
  Pptactic.declare_extra_vernac_genarg_pprule wit_withtac printer
