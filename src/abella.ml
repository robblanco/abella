(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
(*                                                                          *)
(* This file is part of Abella.                                             *)
(*                                                                          *)
(* Abella is free software: you can redistribute it and/or modify           *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation, either version 3 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* Abella is distributed in the hope that it will be useful,                *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License        *)
(* along with Abella.  If not, see <http://www.gnu.org/licenses/>.          *)
(****************************************************************************)

(* BEGIN global Abella configuration *)

let stratification_warnings_are_errors = false
  (** Any stratification violation warnings are treated as errors *)

(* END global Abella configuration *)

open Term
open Metaterm
open Prover
open Abella_types
open Typing
open Extensions
open Printf
open Accumulate

let can_read_specification = ref true

let interactive = ref true
let out = ref stdout
let compile_out = ref None

let switch_to_interactive = ref false
let lexbuf = ref (Lexing.from_channel stdin)

let annotate = ref false
let count = ref 0

let witnesses = ref false

exception AbortProof

(* Input *)

let perform_switch_to_interactive () =
  assert !switch_to_interactive ;
  switch_to_interactive := false ;
  lexbuf := Lexing.from_channel stdin ;
  interactive := true ;
  out := stdout ;
  fprintf !out "Switching to interactive mode.\n%!"

let interactive_or_exit () =
  if not !interactive then
    if !switch_to_interactive then
      perform_switch_to_interactive ()
    else
      exit 1


let position_range (p1, p2) =
  let file = p1.Lexing.pos_fname in
  let line = p1.Lexing.pos_lnum in
  let char1 = p1.Lexing.pos_cnum - p1.Lexing.pos_bol in
  let char2 = p2.Lexing.pos_cnum - p1.Lexing.pos_bol in
    if file = "" then
      ""
    else
      sprintf ": file %s, line %d, characters %d-%d" file line char1 char2

let type_inference_error (pos, ct) exp act =
  eprintf "Typing error%s.\n%!" (position_range pos) ;
  match ct with
    | CArg ->
        eprintf "Expression has type %s but is used here with type %s\n%!"
          (ty_to_string act) (ty_to_string exp)
    | CFun ->
        eprintf "Expression is applied to too many arguments\n%!"

let teyjus_only_keywords =
  ["closed"; "exportdef"; "import"; "infix"; "infixl"; "infixr"; "local";
   "localkind"; "postfix"; "posfixl"; "prefix"; "prefixr"; "typeabbrev";
   "use_sig"; "useonly"; "sigma"]

let warn_on_teyjus_only_keywords (ktable, ctable) =
  let tokens = List.unique (ktable @ List.map fst ctable) in
  let used_keywords = List.intersect tokens teyjus_only_keywords in
    if used_keywords <> [] then
      fprintf !out
        "Warning: The following tokens are keywords in Teyjus: %s\n%!"
        (String.concat ", " used_keywords)

let update_subordination_sign sr sign =
  List.fold_left Subordination.update sr (sign_to_tys sign)

let read_specification name =
  clear_specification_cache () ;
  fprintf !out "Reading specification %S%s\n%!" name
    (if !load_path <> "." then
       sprintf " (from %S)" !load_path
     else "") ;
  let read_sign = get_sign name in
  let () = warn_on_teyjus_only_keywords read_sign in
  let sign' = merge_signs [!sign; read_sign] in
  let sr' = update_subordination_sign !sr read_sign in
  let clauses' = get_clauses ~sr:sr' name in
    (* Any exceptions must have been thrown by now - do actual assignments *)
    sr := sr' ;
    sign := sign' ;
    add_clauses clauses'

(* Checks *)

let ensure_no_restrictions term =
  if get_max_restriction term > 0 then
    failwithf "Invalid formula: %s\n\
             \ Cannot use size restrictions (*, @, #, or +)"
      (metaterm_to_string term)

let untyped_ensure_no_restrictions term =
  ensure_no_restrictions (umetaterm_to_metaterm [] term)

let rec contains_prop ty =
  match ty with
  | Ty (argtys, targty) ->
      targty = "prop" || List.exists contains_prop argtys

type nonstrat_reason =
  | Negative_head of string
  | Negative_ho_arg of string
exception Nonstrat of nonstrat_reason

let add_sgn preds p posity =
  let old_posity =
    try String.Map.find p preds with Not_found -> posity in
  let posity =
    if old_posity = posity then posity
    else NONPOS
  in
  String.Map.add p posity preds

let get_pred_occurrences mt =
  let preds = ref String.Set.empty in
  let rec aux_term t =
    match observe (hnorm t) with
    | Var v when contains_prop v.ty ->
        preds := String.Set.add v.Term.name !preds
    | App (t, ts) ->
        aux_term t ; List.iter aux_term ts
    | Lam (_, t) ->
        aux_term t
    | Var _ | DB _ -> ()
    | _ -> assert false
  in
  iter_preds begin fun ~parity ~posity t ->
    if posity = NONPOS then aux_term t
  end mt ;
  !preds

let warn_stratify names head term =
  let nonposities = get_pred_occurrences term in
  let is_ho_var arg =
    match observe (hnorm arg) with
    | Var { Term.ty = ty; Term.name = v; _ } when contains_prop ty -> Some v
    | _ -> None
  in
  let ho_names =
    def_head_args head |>
    List.filter_map is_ho_var in
  let doit () =
    String.Set.iter begin fun pname ->
      if List.mem pname names then
        raise (Nonstrat (Negative_head pname)) ;
      if List.mem pname ho_names then
        raise (Nonstrat (Negative_ho_arg pname)) ;
    end nonposities
  in
  try doit () with
  | Nonstrat reason ->
      let msg = match reason with
        | Negative_head name ->
            Printf.sprintf
              "Definition might not be stratified\n  (%S occurs to the left of ->)"
              name
        | Negative_ho_arg name ->
            Printf.sprintf
              "Definition can be used to defeat stratification\n  (higher-order argument %S occurs to the left of ->)"
              name
      in
      if stratification_warnings_are_errors
      then failwith msg
      else Printf.fprintf !out "Warning: %s\n%!" msg

let check_theorem thm =
  ensure_no_restrictions thm

let ensure_not_capital name =
  if is_capital_name name then
    failwithf "Invalid defined predicate name %S.\n\
             \ Defined predicates may not begin with a capital letter."
      name

let ensure_name_contained id ids =
  if not (List.mem id ids) then
    failwithf "Found stray clause for %s" id

let ensure_wellformed_head t =
  match t with
    | Pred _ -> ()
    | Binding(Nabla, _, Pred _) -> ()
    | _ ->
        failwithf "Invalid head in definition: %s"
          (metaterm_to_string t)

let check_defs names defs =
  List.iter ensure_not_capital names ;
  List.iter
    (fun (head, body) ->
       ensure_wellformed_head head ;
       ensure_name_contained (def_head_name head) names ;
       ensure_no_restrictions head ;
       ensure_no_restrictions body ;
       warn_stratify names head body)
    defs

let check_noredef ids =
  let (_, ctable) = !sign in
    List.iter (
      fun id -> if List.mem id (List.map fst ctable) then
        failwithf "Predicate or constant %s already exists" id
    ) ids

(******************************************************************************)
(*RB*)(*A translation module should be hack-added here*)

(* TODO
   - Substitute predicate names for logic variables and add their identification
     with the corresponding generated fixed points.
   - Unary predicates (bad argument sequence) and variables as atoms. To tell
     these two apart, I need symbol tables again. *)

let fpc_ids ids =
  String.concat ", " ids

let rec fpc_ty = function Ty(tys, id) ->
  let tys_str_l = List.map fpc_ty tys in
  let tys_str = String.concat " -> " tys_str_l in
  match tys with
  | []          ->                             id (* Simple type *)
  | [_]         -> "( " ^ tys_str ^ " ) -> " ^ id (* Left-associative *)
  | _ :: _ :: _ ->        tys_str ^   " -> " ^ id (* Right-associative *)

(*************************
 * Interface with Abella *
 *************************)
let fpc_theorem name thm =
  fprintf stdout "FPC theorem"

let rec fpc_uterm = function
  | UCon(pos, id, ty) -> "{Con/" ^ id ^ ", " ^ fpc_ty ty ^ "}"
  | ULam(pos, id, ty, uterm) -> "{Lam/" ^ id ^ ", " ^ fpc_ty ty ^ ", " ^ fpc_uterm uterm ^ "}"
  | UApp(pos, uterm_x, uterm_y) -> "{App/" ^ fpc_uterm uterm_x ^ ", " ^ fpc_uterm uterm_y ^ "}"

(*let rec fpc_upred *)
let fpc_restriction = ""
(*
  function
  | Smaller(n)
  | Equal(n)
  | CoSmaller(n)
  | CoEqual(n)
  | Irrelevant
*)

(*TODO Compiled support missing *)
(* 1. List.map2_exn *)

(** Translation: head of a clause, recursive elaboration.
    For clarity and in consideration of the limited complexity of what we
    expect to be "reasonable" predicates, all considerations of efficiency have
    been dropped where needed.
    Note that the number of arguments at each stage determines the current depth
    if needed, so no explicit parameter is needed.
    @param uterm Term representing the head of a clause or one of its curried
                 subterms.
    @return Tuple consisting of head constituents in string format for the
     current subtree: {ol
     {- the name of the predicate;}
     {- the list of variables involved; and}
     {- the ordered list of arguments on those variables.}}
    @raise Matching errors on invalid structures.
    @author Rob Blanco
    @todo This is outside the "parent function" because I suspect that it will
          be reused, and will possibly need to be renamed, etc. The expectation
          is that because atoms "are" predicates/fixed points in the current
          context, this will work well with little extra attention. Consider,
          however, the case of variables. *)
let rec fpc_udef_head_rec =
  (** Translation: argument of a predicate call.
      @param uterm Term representing an argument in a predicate call.
      @return String representation of the argument of a predicate call.
      @raise Matching errors on invalid structures.
      @author Rob Blanco
      @todo I had some notes here that I think have been taken proper care of.
            Consult if something goes wrong or greater generality is still
            needed. *)
  let fpc_udef_head_arg uterm =
    (** Translation: argument of a predicate call, recursive elaboration.
        Arguments to predicate calls are either monotype variables or, more
        generally, expressions involving monotype variables and monotype
        constructors. These constructors can take parameters and be nested.
        @param level Current parse depth.
        @param uterm (Sub)term representing an argument in a predicate call.
        @return String representation of the argument of a predicate call.
        @raise Matching errors on invalid structures.
        @author Rob Blanco *)
    let rec fpc_udef_head_arg_rec level = function
      (* An identifier at the top is a variable, at the bottom of a degenerate
         left chain it is a constructor that opens the string representation of
         the term. *)
      | UCon(_, id, _) ->
        (** Check if an identifier is already declared in Abella.
            Here we make use of the global state (i.e. the signature), which has
            led me to reposition the source code a bit, at least for now.
            @param id An identifier (type constructor or definition).
            @return A boolean indicating its presence in the current session.
            @author Rob Blanco *)
        let fpc_declared_id id =
          try check_noredef [id] ; false
          with _ -> true
        in
        (* fpc_udef_head_arg_rec *)
        if level = 0
        then if fpc_declared_id id
          then ([], id)
          else ([id], id)
        else ([], "(" ^ id)
      (* An application always consists of two parts: a left traversal of the
         degenerate tree with its previous arguments, if any, yielding an open
         (incomplete) term representation. This is the recursive part proper. On
         the right, the corresponding argument is parsed and added to the string
         representation. At the top of the chain, this closes the term. *)
      | UApp(_, uterm_l, uterm_r) ->
        let (vars_l, arg_l) = fpc_udef_head_arg_rec (level + 1) uterm_l in
        let (vars_r, arg_r) = fpc_udef_head_arg_rec 0 uterm_r in
        let terminator = if level = 0 then ")" else "" in
        (vars_l @ vars_r, arg_l ^ " " ^ arg_r ^ terminator)
      (* Error *)
      | ULam(_, _, _, _) -> failwith "uterm not supported"
    (* fpc_udef_head_arg uterm *)
    in
    fpc_udef_head_arg_rec 0 uterm
  (* fpc_udef_head_rec *)
  in function
  (* Base case: predicate name at the bottom on the left *)
  | UCon(_, id, _) -> (id, [], [])
  (* Recursive case: process each argument *)
  | UApp(_, uterm_l, uterm_r) ->
      let (name, vars_l, args_l) = fpc_udef_head_rec uterm_l in
      let (vars_r, arg_r) = fpc_udef_head_arg uterm_r in
      let vars_uniq = List.sort_uniq String.compare (vars_l @ vars_r) in
      (name, vars_uniq, args_l @ [arg_r])
  (* Errors *)
  | ULam(_, _, _, _) -> failwith "uterm not supported"

(** Translation: decomposition of clause head for parameter mapping.
    This function is meant to be used on the head of a clause into the name of
    the predicate being encoded, and the lists of arguments and variables
    involved in these. These data initiate the encoding of the body of the
    clause by providing the means through which the Args parameter will be
    decoded into the actual parameters of the clause.
    @param umetaterm Left-degenerate binary tree consisting of a sequence of
                     UApp uterms. The deepest UApp is terminated on the right by
                     a UCon containing the name of the predicate. All are
                     terminated on the left with a subtree representing an
                     argument. For a tree of left UApp depth n, the right child
                     of the UApp node at level k represents the (n-k+1)-th
                     argument. Arguments are expected to be subtrees of UApp and
                     UCon uterms.
    @return Tuple consisting of head constituents, all in string format: {ol
     {- the name of the predicate;}
     {- the list of variables involved; and}
     {- the ordered list of arguments on those variables.}}
    @raise Matching errors on invalid structures.
    @author Rob Blanco
    @todo Detect and treat unary constructors, predicate names, and variables.
          To do this, we need to resort to a symbol table, so we either build it
          (functionally or imperatively) or use Abella's. At any rate, the
          translation is embedded in an imperative framework, so it makes sense
          to be stateful, as we are running in exactly such an environment.
          Moreover, reusing Abella's tables will keep our code as unpolluted as
          possible. In particular, remove the following from the list of
          variables: {ol
          {- previously declared term constructors, esp. unaries; and}
          {- previously declared predicate names.}}
          NOTE: I hope that this has been taken care of at the one and right
          place to deal with this. Cf. fpc_declared_id.
    @todo Consider if/how the function can be reused for predicates within the
          body of a clause. Refactor accordingly. *)
let fpc_udef_head = function
  (* Errors *)
  | UTrue|UFalse|UEq (_, _)|UAsyncObj (_, _, _)|USyncObj (_, _, _, _)|
    UArrow (_, _)|UBinding (_, _, _)|UOr (_, _)|UAnd (_, _) ->
    failwith "umetaterm not supported"
  (* Treatment for predicates *)
  | UPred(uterm, _) -> fpc_udef_head_rec uterm

(** Translation: quantify a set of variables.
    @param binder Type of quantification to apply to 'vars'.
    @param vars Nonempty list of strings representing variable names in a term.
    @return String representing the variables of 'vars' quantified over
            'binder'.
    @raise On nabla quantifiers, currently unsupported.
    @author Rob Blanco *)
let fpc_var_quantification binder =
  let binder_str = (function
    | Forall -> "all"
    | Exists -> "some"
    | Nabla  -> failwith "binder not supported") binder
  in function
  | [] -> assert false
  | (hd :: tl) as vars ->
    List.fold_left (fun acc var -> acc ^ binder_str ^ " " ^ var ^ "\\ ") "" vars
    |> String.trim

(** Translation: arguments of a fixed point expression.
    Predicates are encoded through fixed points in the checker. All fixed points
    have a single argument that can be used to encode arbitrary lists of
    parameters through the list constructors 'argv' and '(++)'.
    @param args List of strings representing arguments passed to a predicate.
    @return String representing the single argument for the fixed point that
            translates the original predicate.
    @author Rob Blanco *)
let fpc_fixed_point_args = function
  | [] -> "argv"
  | (hd :: tl) as args -> "(" ^ String.concat " ++ " args ^ " ++ argv)"

(** Translation: body of a clause.
    @param name Name of the predicate being translated.
    @param umetaterm (Sub-)term representing a clause or part thereof.
    @return String representation of the term 'umetaterm' where according to
            encoding conventions recursive references to the predicate being
            considered ('name') are given the canonical self-reference 'Pred'.
    @raise On unsupported terms.
    @author Rob Blanco
    @todo Return list of references to other predicates for external linking.
          Can I do it generically? In Abella the syntactic detour is not needed.
    @todo In the predicate case, maybe need to refactor, rename, re-something,
          fpc_udef_head, as well as the functions that conflate the parts.
    @todo The function name is unfortunate, so appears to be fpc_udef_head_rec,
          which is apparently never called recursively outside itself.
    @todo Can we consider a generic print_metaterm as a better alternative?
    @todo Minor simplifications: if the body is trivially true, drop the clause
          (at least in a disjunctive context). Recall that this is recursive, so
          it could be a bit more delicate than just doing it here. *)
let rec fpc_udef_body name =
  (** Translation: predicate calls within the encoding of another predicate.
      Self-references are made to 'Pred' as dictated by the encoding convention
      (cf. fpc_define). References to other predicates are capitalized to
      signify a logic variable that must be pre-loaded with the corresponding
      fixed point of the predicate, which will be given the same name. As
      identifiers cannot start with uppercase, these will be reserved for the
      logic variables of same-named predicates. (Be careful with name clashes!)
      @param name Name of the predicate being encoded.
      @param pred Name of the predicate being called.
      @param args Arguments to the predicate being called.
      @return String representing the call to 'pred' with 'args' within the
              encoding of 'name'.
      @author Rob Blanco
      @todo To clarify where needed: variables may not be named after predicates
            for this simple encoding to work.
      @todo Also note that I am using this code for raw variables, too. Explain,
            rename, adjust where appropriate. In particular, reuse in equality
            makes me think that arguments may never apply (equality works on
            terms, and though in Abella predicates are defined through similar
            grammars, for me the context is different). *)
  let fpc_upred name pred args =
    let pred_str = if pred = name then "Pred" else String.capitalize pred in
    "(" ^ pred_str ^ " " ^ fpc_fixed_point_args args ^ ")"
  (* fpc_udef_body *)
  in function
  | UTrue -> "tt"
  | UFalse -> "ff"
  | UEq(t1, t2) -> (* This case may work, but it doesn't look clean at all *)
    let (pred1, _, args1) = fpc_udef_head_rec t1 in
    let (pred2, _, args2) = fpc_udef_head_rec t2 in
    let t1_str = fpc_upred name pred1 args1 in
    let t2_str = fpc_upred name pred2 args2 in
    "(eq " ^ t1_str ^ " " ^ t2_str ^ ")"
  | UArrow(umt1, umt2) ->
    "(imp " ^ fpc_udef_body name umt1 ^ " " ^ fpc_udef_body name umt2 ^ ")"
  | UBinding(b, idtys, umt) ->
    let ids = List.map (fun (id, _) -> id) idtys in (* Used elsewhere? *)
    let ids_str = fpc_var_quantification b ids in
    "(" ^ ids_str ^ " " ^ fpc_udef_body name umt ^ ")"
  | UOr(umt1, umt2) ->
    "(or "  ^ fpc_udef_body name umt1 ^ " " ^ fpc_udef_body name umt2 ^ ")"
  | UAnd(umt1, umt2) ->
    "(and " ^ fpc_udef_body name umt1 ^ " " ^ fpc_udef_body name umt2 ^ ")"
  | UPred(_, _) as p ->
    let (pred, _, args) = fpc_udef_head p in
    fpc_upred name pred args
  | UAsyncObj(_, _, _)|USyncObj(_, _, _, _) ->
    failwith "umetaterm not supported"

(******************************************************************************)
let rec preds = function
  | UTrue|UFalse|UEq(_, _)                        -> []
  | UArrow(mt1, mt2)|UOr(mt1, mt2)|UAnd(mt1, mt2) -> preds mt1 @ preds mt2
  | UBinding(_, _, mt)                            -> preds mt
  | UPred(_, _) as p                              -> [p]
  | UAsyncObj(_, _, _)|USyncObj(_, _, _, _) -> failwith "metaterm not supported"

(*name polymorphism?
  also very important: when changing to FUNCTION, make sure to clean up the argument!*)
let pred_name =
  let rec pred_name_rec = function
    | UApp(_, term_l, _) -> pred_name_rec term_l
    | UCon(_, id, _) -> id
    | _ -> failwith "term not supported"
  in function
  | UPred(term, _) -> pred_name_rec term
  | _ -> failwith "not a predicate"

let pred_fp name =
  name ^ " " ^ String.capitalize name

let sandwich left right str =
  if String.length str = 0 then "" else left ^ str ^ right (*is_empty: Core*)

let test_fun name body =
  preds body |> 
  List.map pred_name |>
  List.filter (fun x -> String.compare x name <> 0) |>
  List.map pred_fp |>
  List.sort_uniq String.compare (*|>
  String.concat " /\ " |>
  sandwich ":= " "."*)
(******************************************************************************)

(** Translation: single clause in a predicate definition to (disjunctive) clause
    in the fixed point encoding.
    @param def Clause tuple consisting of two components: {ol
     {- the head of the clause; and}
     {- the body of the clause.}}
    @return String representation of the encoding of the clause.
    @raise On invalid structures including unsupported features.
    @author Rob Blanco *)
(*A flexible idea: a category of functions "visit_predicates"... that take other functions instructing what to do with the selected nodes, so we may reuse and clarify things*)
let fpc_udef (head, body) =
  let (name, vars, args) = fpc_udef_head head in
  let vars_str = fpc_var_quantification Exists vars in
  let args_str = fpc_fixed_point_args args in
  let body_str = fpc_udef_body name body in
  "(" ^ vars_str ^ " (and (eq Args " ^ args_str ^ ")\n" ^
  body_str ^
  "\n))"

(** Translation: multi-clause predicate definition to disjunctive fixed point
    encoding, sans fixed point header.
    The function produces a left-associative chain of disjunctions, each leaf
    encoding one of the clauses of the predicate. It is interesting to note that
    each clause is entirely self contained, i.e. the encoding deviates from my
    manual, early examples in that it lacks a top-level argument parsing, used
    to give common names to the arguments, shared by all clauses. Here instead,
    each clause parses the arguments according to its head, which is more
    verbose, but also allows more compact bodies, as parameters can be made to
    match more complex expressions; critically, the procedure is entirely local
    as opposed to my manual encoding. (It was while dealing with context
    subsumption examples that the realization came to me.)
    @param defs Nonempty list of clauses conforming the definition of a
                (co)inductive predicate.
    @return String representation of the encoding of the clauses.
    @raise On invalid structures and unsupported features.
    @author Rob Blanco
    @todo Could we add support for undefined clauses, and is this the right
          place? *)
let rec fpc_udefs(*_exn*) = function
  | [] -> assert false
  | [hd] -> fpc_udef hd
  | hd :: (hd' :: tl' as tl) -> "(or " ^ fpc_udef hd ^ "\n" ^ fpc_udefs tl ^ ")"

(*maybe I'm repeating part of the processing that I did in test_fun... but does it make sense there?*)
(*concat_map not defined outside Core*)
let fpc_udefs_ext name udefs =
  let wrap str =
    if String.length str = 0
    then ""
    else "\n:=\n" ^ str
  in
  List.map (fun (_, body) -> test_fun name body) udefs |>
  List.concat |>
  List.sort_uniq String.compare |>
  String.concat " /\ " |>
  wrap

(** Translation: inductive predicate to least fixed point.
    The function produces a left-associative chain of disjunctions, each leaf
    encoding one of the clauses of the predicate.
    @param udefs List of predicate definitions in ordered, one-to-one
                 correspondence with the elements of 'idtys'.
    @param idtys List of tuples containing the names and types of the
                 predicates involved in the definition.
    @return String encoding a least fixed point that represents the predicate of
            the definition.
    @raise Mutually recursive definitions and definitions involving
           unsupported features. Possibly invalid structures, but without any
           guarantees (an error-free Abella parse tree is assumed).
    @author Rob Blanco
    @todo Add support for mutual recursion.
    @todo Here and throughout, fix naming conventions to ignore 'u' prefixes,
          i.e. defs vs. udefs, etc. *)
let fpc_define(*_exn*) udefs = function
  | [] -> assert false
  | _ :: _ :: _ -> failwith "mutual recursion not supported"
  | (name, _) :: [] ->
    "Define " ^ name ^ " : (i -> bool) -> prop by\n" ^
    name ^ " (mu Pred\\Args\\\n" ^
    fpc_udefs udefs ^
    "\n)" ^
    fpc_udefs_ext name udefs ^
    "."
(*
  let (name, _) = List.hd idtys in
  "Define " ^ name ^ " : (i -> bool) -> prop by\n" ^
  name ^ " (mu Pred\\Args\\\n" ^
  fpc_udefs udefs ^
  "\n)."
*)

let fpc_codefine idtys udefs =
  fprintf stdout "FPC codefine"

(* No need for kind declarations: everything will be 'i' *)
let fpc_kind ids = ""

let fpc_type ids ty =
  let ids_str = fpc_ids ids in
  let ty_str = fpc_ty ty in
  "Type\t" ^ ids_str ^ "\t" ^ ty_str ^ ".\n"
(******************************************************************************)    

(* Compilation and importing *)

let comp_spec_sign = ref ([], [])
let comp_spec_clauses = ref []
let comp_content = ref []

let marshal citem =
  match !compile_out with
    | Some cout -> Marshal.to_channel cout citem []
    | None -> ()

let ensure_finalized_specification () =
  if !can_read_specification then begin
    can_read_specification := false ;
    comp_spec_sign := !sign ;
    comp_spec_clauses := !clauses
  end

let compile citem =
  ensure_finalized_specification () ;
  comp_content := citem :: !comp_content

let predicates (ktable, ctable) =
  List.map fst (List.find_all (fun (_, Poly(_, Ty(_, ty))) -> ty = "o") ctable)

let write_compilation () =
  marshal !comp_spec_sign ;
  marshal !comp_spec_clauses ;
  marshal (predicates !sign) ;
  marshal (List.rev !comp_content)

let clause_eq c1 c2 = eq c1 c2

let clauses_to_predicates clauses =
  let clause_heads =
    List.map (fun c -> let (_,h,_) = clausify c in h) clauses in
  List.unique (List.map term_head_name clause_heads)

let ensure_valid_import imp_spec_sign imp_spec_clauses imp_predicates =
  let (ktable, ctable) = !sign in
  let (imp_ktable, imp_ctable) = imp_spec_sign in

  (* 1. Imported ktable must be a subset of ktable *)
  let missing_types = List.minus imp_ktable ktable in
  let () = if missing_types <> [] then
    failwithf "Imported file makes reference to unknown types: %s"
      (String.concat ", " missing_types)
  in

  (* 2. Imported ctable must be a subset of ctable *)
  let missing_consts = List.minus imp_ctable ctable in
  let () = if missing_consts <> [] then
    failwithf "Imported file makes reference to unknown constants: %s"
      (String.concat ", " (List.map fst missing_consts))
  in

  (* 3. Imported clauses must be a subset of clauses *)
  let missing_clauses =
    List.minus ~cmp:clause_eq imp_spec_clauses !clauses
  in
  let () = if missing_clauses <> [] then
    failwithf "Imported file makes reference to unknown clauses for: %s"
      (String.concat ", " (clauses_to_predicates missing_clauses))
  in

  (* 4. Clauses for imported predicates must be subset of imported clauses *)
  let extended_clauses =
    List.minus ~cmp:clause_eq
      (List.find_all
         (fun clause ->
           let (_,clause_head,_) = clausify clause in
           List.mem (term_head_name clause_head) imp_predicates)
         !clauses)
      imp_spec_clauses
  in
  let () = if extended_clauses <> [] then
    failwithf "Cannot import file since clauses have been extended for: %s"
      (String.concat ", " (clauses_to_predicates extended_clauses))
  in
  ()


let imported = ref []

let import filename =
  let rec aux filename =
    if not (List.mem filename !imported) then begin
      imported := filename :: !imported ;
      let file = open_in_bin (filename ^ ".thc") in
      let imp_spec_sign = (Marshal.from_channel file : sign) in
      let imp_spec_clauses = (Marshal.from_channel file : clauses) in
      let imp_predicates = (Marshal.from_channel file : string list) in
      let imp_content = (Marshal.from_channel file : compiled list) in
        ensure_valid_import imp_spec_sign imp_spec_clauses imp_predicates ;
        List.iter
          (function
             | CTheorem(name, thm) ->
                 fpc_theorem name thm ; (*RB*)
                 add_lemma name thm ;
             | CDefine(idtys, defs) ->
                 (*fpc_define defs idtys ;*) (*RB*)
                 let ids = List.map fst idtys in
                   check_noredef ids;
                   check_defs ids defs ;
                   add_global_consts idtys ;
                   add_defs ids Inductive defs ;
             | CCoDefine(idtys, defs) ->
                 fpc_codefine idtys defs ; (*RB*)
                 let ids = List.map fst idtys in
                   check_noredef ids;
                   check_defs ids defs ;
                   add_global_consts idtys ;
                   add_defs ids CoInductive defs
             | CImport(filename) ->
                 aux filename
             | CKind(ids) ->
                 fprintf stderr "%s" (fpc_kind ids) ; (*RB*)
                 check_noredef ids;
                 add_global_types ids
             | CType(ids, ty) ->
                 fprintf stderr "%s" (fpc_type ids ty) ; (*RB*)
                 check_noredef ids;
                 add_global_consts (List.map (fun id -> (id, ty)) ids)
             | CClose(ty_subords) ->
                 List.iter
                   (fun (ty, prev) ->
                      let curr = Subordination.subordinates !sr ty in
                        match List.minus curr prev with
                          | [] -> ()
                          | xs ->
                              failwithf
                                "Cannot close %s since it is now subordinate to %s"
                                ty (String.concat ", " xs))
                   ty_subords ;
                 close_types (List.map fst ty_subords))
          imp_content
    end
  in
    if List.mem filename !imported then
      fprintf !out "Ignoring import: %s has already been imported.\n%!" filename
    else begin
      fprintf !out "Importing from %s\n%!" filename ;
      aux filename
    end


(* Proof processing *)

let query q =
  let fv = ids_to_fresh_tyctx (umetaterm_extract_if is_capital_name q) in
  let ctx = fresh_alist ~tag:Logic ~used:[] fv in
  match type_umetaterm ~sr:!sr ~sign:!sign ~ctx (UBinding(Metaterm.Exists, fv, q)) with
    | Binding(Metaterm.Exists, fv, q) ->
        let ctx = List.map begin fun (x, ty) ->
            (x, Term.fresh ~tag:Logic 0 ty)
          end fv in
        let q = replace_metaterm_vars ctx q in
        let _ = Tactics.search
          ~depth:max_int
          ~hyps:[]
          ~clauses:!clauses
          ~alldefs:(defs_table_to_list ())
          ~sc:(fun w ->
                 fprintf !out "Found solution:\n" ;
                 List.iter
                   (fun (n, v) ->
                      fprintf !out "%s = %s\n" n (term_to_string v))
                   ctx ;
                 fprintf !out "\n%!")
          q
        in
          fprintf !out "No more solutions.\n%!"
    | _ -> assert false

let set_fail ~key ~expected v =
  failwithf "Unknown value '%s' for key %S; expected %s"
    (set_value_to_string v) key expected

let set k v =
  match k, v with
  | "subgoals", Int d when d >= 0 -> subgoal_depth := d
  | "subgoals", Str "on" -> subgoal_depth := 1000
  | "subgoals", Str "off" -> subgoal_depth := 0
  | "subgoals", _ -> set_fail v
                       ~key:"subgoals"
                       ~expected:"'on', 'off', or non-negative integer"

  | "instantiations", Str "on" -> Prover.show_instantiations := true
  | "instantiations", Str "off" -> Prover.show_instantiations := false
  | "instantiations", _ -> set_fail v
                             ~key:"instantiations"
                             ~expected:"'on' or 'off'"

  | "types", Str "on" -> Prover.show_types := true
  | "types", Str "off" -> Prover.show_types := false
  | "types", _ -> set_fail v
                    ~key:"types"
                    ~expected:"'on' or 'off'"

  | "search_depth", Int d when d >= 0 -> search_depth := d
  | "search_depth", _ -> set_fail v
                           ~key:"search_depth"
                           ~expected:"non-negative integer"

  | "witnesses", Str "on" -> witnesses := true
  | "witnesses", Str "off" -> witnesses := false
  | "witnesses", _ -> set_fail v
                        ~key:"witnesses"
                        ~expected:"'on' or 'off'"

  | "load_path", QStr s -> load_path := s

  | _, _ -> failwithf "Unknown key '%s'" k

let print_theorem name thm =
  fprintf !out "\nTheorem %s : \n%s.\n%!"
    name (metaterm_to_formatted_string thm)

let show name =
  print_theorem name (get_lemma name)

let witness w =
  if !witnesses then
    fprintf !out "Witness: %s\n%!" (Tactics.witness_to_string w)

let term_witness (t, w) =
  if !witnesses then
    fprintf !out "Witness: %s : %s\n%!"
      (Tactics.witness_to_string w)
      (metaterm_to_string t)

let rec process_proof name =
  let suppress_display = ref false in
  let finished = ref false in
    try while not !finished do try
      if !annotate then begin
        fprintf !out "</pre>\n%!" ;
        incr count ;
        fprintf !out "<a name=\"%d\"></a>\n%!" !count ;
        fprintf !out "<pre>\n%!"
      end ;
      if not !suppress_display then
        display !out
      else
        suppress_display := false ;
      fprintf !out "%s < %!" name ;
      let input = Parser.command Lexer.token !lexbuf in
        if not !interactive then begin
          let pre, post = if !annotate then "<b>", "</b>" else "", "" in
            fprintf !out "%s%s.%s\n%!" pre (command_to_string input) post
        end ;
        save_undo_state () ;
        begin match input with
          | Induction(args, hn) -> induction ?name:hn args
          | CoInduction hn -> coinduction ?name:hn ()
          | Apply(h, args, ws, hn) -> apply ?name:hn h args ws ~term_witness
          | Backchain(h, ws) -> backchain h ws ~term_witness
          | Cut(h, arg, hn) -> cut ?name:hn h arg
          | CutFrom(h, arg, t, hn) -> cut_from ?name:hn h arg t
          | SearchCut(h, hn) -> search_cut ?name:hn h
          | Inst(h, ws, hn) -> inst ?name:hn h ws
          | Case(str, hn) -> case ?name:hn str
          | Assert(t, hn) ->
              untyped_ensure_no_restrictions t ;
              assert_hyp ?name:hn t
          | Exists(_, t) -> exists t
          | Monotone(h, t) -> monotone h t
          | Clear(hs) -> clear hs
          | Abbrev(h, s) -> abbrev h s
          | Unabbrev(hs) -> unabbrev hs
          | Rename(hfr, hto) -> rename hfr hto
          | Search(limit) ->
              search ~limit ~interactive:!interactive ~witness ()
          | Permute(ids, h) -> permute_nominals ids h
          | Split -> split false
          | SplitStar -> split true
          | Left -> left ()
          | Right -> right ()
          | Unfold (cs, ss) -> unfold cs ss
          | Intros hs -> intros hs
          | Skip -> skip ()
          | Abort -> raise AbortProof
          | Undo -> undo () ; undo () (* undo recent save, and previous save *)
          | Common(Set(k, v)) -> set k v
          | Common(Show(n)) ->
              undo () ; (* Do not save an undo point here *)
              show n ;
              fprintf !out "\n%!" ;
              suppress_display := true
          | Common(Quit) -> raise End_of_file
        end ;
        if !interactive then flush stdout ;
    with
      | Failure "lexing: empty token" ->
          exit (if !interactive then 0 else 1)
      | Prover.Proof_completed ->
          fprintf !out "Proof completed.\n%!" ;
          reset_prover () ;
          finished := true
      | Failure s ->
          eprintf "Error: %s\n%!" s ;
          interactive_or_exit ()
      | End_of_file ->
          if !switch_to_interactive then
            perform_switch_to_interactive ()
          else begin
            fprintf !out "Proof NOT completed.\n%!" ;
            exit 1
          end
      | AbortProof ->
          fprintf !out "Proof aborted.\n%!" ;
          reset_prover () ;
          raise AbortProof
      | Abella_types.Reported_parse_error ->
          Lexing.flush_input !lexbuf ;
          interactive_or_exit ()
      | Parsing.Parse_error ->
          eprintf "Syntax error%s.\n%!" (position !lexbuf) ;
          Lexing.flush_input !lexbuf ;
          interactive_or_exit () ;
      | TypeInferenceFailure(ci, exp, act) ->
          type_inference_error ci exp act ;
          interactive_or_exit ()
      | e ->
          eprintf "Error: %s\n%s%!" (Printexc.to_string e) (Printexc.get_backtrace ()) ;
          interactive_or_exit ()
    done with
      | Failure "eof" -> ()

let rec process () =
  try while true do try
    if !annotate then begin
      incr count ;
      fprintf !out "<a name=\"%d\"></a>\n%!" !count ;
      fprintf !out "<pre class=\"code\">\n%!"
    end ;
    fprintf !out "Abella < %!" ;
    let input = Parser.top_command Lexer.token !lexbuf in
      if not !interactive then begin
          let pre, post = if !annotate then "<b>", "</b>" else "", "" in
            fprintf !out "%s%s.%s\n%!" pre (top_command_to_string input) post
      end ;
      begin match input with
        | Theorem(name, thm) ->
            fpc_theorem name thm ; (*RB*)
            let thm = type_umetaterm ~sr:!sr ~sign:!sign thm in
              check_theorem thm ;
              theorem thm ;
              begin try
                process_proof name ;
                compile (CTheorem(name, thm)) ;
                add_lemma name thm ;
              with AbortProof -> () end
        | SSplit(name, names) ->
            let thms = create_split_theorems name names in
              List.iter
                (fun (n, t) ->
                   print_theorem n t ;
                   add_lemma n t ;
                   compile (CTheorem(n, t)))
                thms ;
        | Define(idtys, udefs) ->
            fprintf stderr "%s" (fpc_define udefs idtys) ; (*RB*)
            let ids = List.map fst idtys in
              check_noredef ids;
              let (local_sr, local_sign) = locally_add_global_consts idtys in
              let defs = type_udefs ~sr:local_sr ~sign:local_sign udefs in
                check_defs ids defs ;
                commit_global_consts local_sr local_sign ;
                compile (CDefine(idtys, defs)) ;
                add_defs ids Inductive defs
        | CoDefine(idtys, udefs) ->
            fpc_codefine idtys udefs ; (*RB*)
            let ids = List.map fst idtys in
              check_noredef ids;
              let (local_sr, local_sign) = locally_add_global_consts idtys in
              let defs = type_udefs ~sr:local_sr ~sign:local_sign udefs in
                check_defs ids defs ;
                commit_global_consts local_sr local_sign ;
                compile (CCoDefine(idtys, defs)) ;
                add_defs ids CoInductive defs
        | TopCommon(Set(k, v)) ->
            set k v
        | TopCommon(Show(n)) ->
            show n
        | TopCommon(Quit) ->
            raise End_of_file
        | Import(filename) ->
            compile (CImport filename) ;
            import filename ;
        | Specification(filename) ->
            if !can_read_specification then begin
              read_specification filename ;
              ensure_finalized_specification ()
            end else
              failwith "Specification can only be read \
                      \ at the begining of a development."
        | Query(q) -> query q
        | Kind(ids) ->
            fprintf stderr "%s" (fpc_kind ids) ; (*RB*)
            check_noredef ids;
            add_global_types ids ;
            compile (CKind ids)
        | Type(ids, ty) ->
            fprintf stderr "%s" (fpc_type ids ty) ; (*RB*)
            check_noredef ids;
            add_global_consts (List.map (fun id -> (id, ty)) ids) ;
            compile (CType(ids, ty))
        | Close(ids) ->
            close_types ids ;
            compile
              (CClose(List.map
                        (fun id -> (id, Subordination.subordinates !sr id))
                        ids)) ;
      end ;
      if !interactive then flush stdout ;
      if !annotate then fprintf !out "</pre>%!" ;
      fprintf !out "\n%!" ;
  with
    | Failure "lexing: empty token" ->
        eprintf "Unknown symbol" ;
        exit (if !interactive then 0 else 1)
    | Failure s ->
        eprintf "Error: %s\n%!" s ;
        interactive_or_exit ()
    | End_of_file ->
        if !switch_to_interactive then
          perform_switch_to_interactive ()
        else begin
          fprintf !out "Goodbye.\n%!" ;
          ensure_finalized_specification () ;
          write_compilation () ;
          if !annotate then fprintf !out "</pre>\n%!" ;
          exit 0
        end
    | Abella_types.Reported_parse_error ->
        Lexing.flush_input !lexbuf ;
        interactive_or_exit ()
    | Parsing.Parse_error ->
        eprintf "Syntax error%s.\n%!" (position !lexbuf) ;
        Lexing.flush_input !lexbuf ;
        interactive_or_exit ()
    | TypeInferenceFailure(ci, exp, act) ->
        type_inference_error ci exp act ;
        interactive_or_exit ()
    | e ->
        eprintf "Unknown error: %s\n%!" (Printexc.to_string e) ;
        interactive_or_exit ()
  done with
  | Failure "eof" -> ()


(* Command line and startup *)

let welcome_msg = sprintf "Welcome to Abella %s\n" Version.version

let usage_message = "abella [options] <theorem-file>"

let set_output filename =
  out := open_out filename

let set_compile_out filename =
  compile_out := Some (open_out_bin filename)

let makefile = ref false

let options =
  Arg.align
    [
      ("-i", Arg.Set switch_to_interactive,
       " Switch to interactive mode after reading inputs") ;
      ("-o", Arg.String set_output,
       "<file-name> Output to file") ;
      ("-c", Arg.String set_compile_out,
       "<file-name> Compile definitions and theorems in an importable format") ;
      ("-a", Arg.Set annotate, " Annotate mode") ;
      ("-M", Arg.Set makefile, " Output dependencies in Makefile format")
    ]

let input_files = ref []

let set_input () =
  match !input_files with
    | [] -> ()
    | [filename] ->
        interactive := false ;
        lexbuf := lexbuf_from_file filename
    | fs ->
        eprintf "Error: Multiple files specified as input: %s\n%!"
          (String.concat ", " fs) ;
        exit 1

let add_input filename =
  input_files := !input_files @ [filename]

let _ =
  Sys.set_signal Sys.sigint
    (Sys.Signal_handle (fun _ -> failwith "Interrupted (use ctrl-D to quit)")) ;

  Arg.parse options add_input usage_message ;

  if not !Sys.interactive then
    if !makefile then begin
      List.iter Depend.print_deps !input_files ;
    end else begin
      set_input () ;
      fprintf !out "%s%!" welcome_msg ;
      process ()
    end
;;
