(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See COPYING for licensing details.
 *)

open Format

open Extensions

open Abella_types
open Term
open Metaterm

let ship_sign ff =
  let open Prover in
  let (types, consts) = !sign in
  List.iter begin fun ty ->
    if not (List.mem ty ["prop" ; "o" ; "olist"]) then
      fprintf ff "Kind %s type.@." ty
  end (List.rev types) ;
  List.iter begin fun (k, Typing.Poly (_, ty)) ->
    if not (List.mem k ["member" ; "=>" ; "pi" ; "::" ; "nil"]
            || Hashtbl.mem defs_table k) then
      fprintf ff "Type %s @[%a@].@." k format_ty ty
  end (List.rev consts)

let all_standard_heads defs =
  List.for_all begin fun (head, _) ->
    match head with
    | Pred _ -> true
    | _ -> false
  end defs

let get_vars tyargs =
  List.mapi begin fun n ty ->
    var Constant ("ZZZ" ^ string_of_int (n + 1)) 0 ty
  end tyargs

let get_case name vars (head, body) =
  match head with
  | Pred (head, _) ->
      let vs = find_vars Constant [head]
               |> List.filter (fun v -> is_capital_name v.name)
               |> List.rev
      in
      let actual_args =
        match observe (hnorm head) with
        | App (_, args) -> args
        | _ -> assert false
      in
      let eqs = List.map2 (fun v arg -> Eq (v, arg)) vars actual_args in
      let body = if body = True then [] else [body] in
      let body = conjoin (eqs @ body) in
      if vs <> [] then
        Binding (Exists, List.map (fun v -> (v.name, v.ty)) vs, body)
      else body
  | _ -> assert false

let ship_defs ff =
  let open Prover in
  let (_, consts) = !sign in
  List.iter begin fun (k, Typing.Poly (_, (Ty (tyargs, tyhead) as ty))) ->
    if k <> "member" && Hashtbl.mem defs_table k then begin
      match Hashtbl.find defs_table k with
      | (defty, [kk], defs) when k = kk && all_standard_heads defs ->
          fprintf ff "%s %s : @[%a@] by@."
            (match defty with
             | Inductive -> "Define Inductive"
             | _ -> "Define CoInductive")
            k format_ty ty ;
          let vars = get_vars tyargs in
          let head_pred = Pred (app (const k ty) vars, Irrelevant) in
          fprintf ff "@[%a@] := @." format_metaterm head_pred ;
          let disjs = List.map (get_case k vars) defs in
          let body = disjoin disjs in
          fprintf ff "  @[%a@].@." format_metaterm body ;
      | _ ->
          fprintf ff "/* %S suppressed */" k
    end
  end (List.rev consts)

let ship_lemmas ff =
  let open Prover in
  List.iter begin fun (name, bod) ->
    fprintf ff "Lemma %s : @[%a@].@." name format_metaterm bod
  end (List.rev !lemmas)

let ship_goal name ff =
  let open Prover in
  fprintf ff "Theorem %s : @[%a@].@." name format_metaterm sequent.goal

let ship ~file ~thm =
  let open Prover in
  let fpcin = match file with
    | [fn] -> Filename.chop_extension fn ^ "_" ^ thm ^ ".fpcin"
    | _ -> thm ^ ".fpcin"
  in
  if List.length !subgoals <> 0 then
    failwithf "ship: too many subgoals (%d)" (List.length !subgoals) ;
  if sequent.vars <> [] then
    failwithf "ship: too many variables" ;
  if sequent.hyps <> [] then
    failwithf "ship: too many hypotheses" ;
  let oc = open_out_bin fpcin in
  let ff = formatter_of_out_channel oc in
  ship_sign ff ;
  ship_defs ff ;
  ship_lemmas ff ;
  ship_goal thm ff ;
  pp_print_flush ff () ;
  close_out oc ;
  Printf.printf "FPC proof obligation shipped to %S.\n%!" fpcin ;
  Prover.skip ()
