(** Export Abella sessions for external verification.
    @todo Use Core.Std? is_empty, concat_map... *)

open Metaterm
open Prover
open Term
open Typing

(*******************************************************************************
 * State *
 *********)

(* Full file translation can be performed piecewise for the most part, on a
   rolling basis, and this is the adopted choice for now: minimum integration in
   the Abella parser leaving the core undisturbed. Locally, we need to resort to
   symbol tables, and these are needed to provide a full translation of an
   Abella session or file. Abella keeps track of its own state in an imperative
   framework, so it makes sense to be stateful and reuse the state if possible.
   This is brittle and we can't make many assumptions, but will work for now. *)

(*let translation = ref ""*)

(*******************************************************************************
 * Helpers *
 ***********)

type sign_type =
  | Type
  | Predicate
  | Variable

let check_id id =
  let (_, ctable) = !sign in
  try
    let (_, Poly(_, Ty(_, ty))) = List.find (fun (name, _) -> name = id) ctable
    in if ty = "prop"
    then Predicate
    else Type
  with
    Not_found -> Variable

(** Translation: quantify a set of variables.
    @param binder Type of quantification to apply to 'vars'.
    @param vars Nonempty list of strings representing variable names in a term.
    @return String representing the variables of 'vars' quantified over
            'binder'.
    @raise On nabla quantifiers, currently unsupported.
    @author Rob Blanco *)
let quantify binder =
  let binder_str = (function
    | Forall -> "all"
    | Exists -> "some"
    | Nabla  -> failwith "binder not supported") binder
  in function
  | [] -> assert false
  | (hd :: tl) as vars ->
    List.fold_left (fun acc var -> acc ^ binder_str ^ " " ^ var ^ "\\ ") "" vars
    |> String.trim

(** Meta-level conjunction of terms. *)
let and_descriptions strs = String.concat " /\\ " strs

(*******************************************************************************
 * Kinds *
 *********)

let describe_kind ids = "" (* Everything will be transparently 'i'-typed *)

(*******************************************************************************
 * Types *
 *********)

let describe_ids ids =
  String.concat ", " ids

let rec describe_ty = function Ty(tys, id) ->
  let tys_str = List.map describe_ty tys |> String.concat " -> " in
  match tys with
  | []          ->                        "i" (* Simple type *)
  | [_]         -> "( " ^ tys_str ^ " ) -> i" (* Left-associative *)
  | _ :: _ :: _ ->        tys_str ^   " -> i" (* Right-associative *)

let describe_type ids ty =
  let ids_str = describe_ids ids in
  let ty_str = describe_ty ty in
  "Type " ^ ids_str ^ " " ^ ty_str ^ ".\n"

(*******************************************************************************
 * Terms *
 *********)

let rec get_term_variables = function
  | Var(id) ->
    if check_id id.name = Variable
    then [id.name]
    else []
  | App(_, args) -> (* The name cannot be a variable *)
    List.map get_term_variables args |>
    List.concat |>
    List.sort_uniq String.compare
  | Ptr(_) as ptr ->
    let var = observe ptr in
    get_term_variables var
  | DB(_) | Lam(_, _) | Susp(_, _, _, _) -> failwith "term not supported"

let rec describe_term = function
  | Var(id) -> id.name
  | App(name, args) ->
    let name_str = describe_term name in
    let args_str = List.map describe_term args |> String.concat " " in
    "(" ^ name_str ^ " " ^ args_str ^ ")"
  | Ptr(_) as ptr ->
    let var = observe ptr in
    describe_term var
  | DB(_) | Lam(_, _) | Susp(_, _, _, _) -> failwith "term not supported"

(*******************************************************************************
 * Predicate calls *
 *******************)

let get_predicate_name = function
  | Pred(App((Ptr(_) as ptr), _), _) ->
    let var = observe ptr in
    ( match var with
    | Var id ->
      if check_id id.name = Predicate
      then id.name
      else failwith "not a predicate"
    | _ -> failwith "bad observation" )
  | _ -> failwith "bad predicate"

let get_predicate_arguments = function
  | Pred(App(_, args) ,_) ->
    List.map describe_term args
  | _ -> failwith "not a predicate or bad format"

(** Translation: arguments of a fixed point expression.
    Predicates are encoded through fixed points in the checker. All fixed points
    have a single argument that can be used to encode arbitrary lists of
    parameters through the list constructors 'argv' and '(++)'.
    @param args List of strings representing arguments passed to a predicate.
    @return String representing the single argument for the fixed point that
            translates the original predicate.
    @author Rob Blanco *)
let describe_arguments = function
  | [] -> "argv"
  | (hd :: tl) as args -> "(" ^ String.concat " ++ " args ^ " ++ argv)"

(** Translation: predicate calls within the encoding of another predicate.
      Self-references are made to 'Pred' as dictated by the encoding convention
      (cf. define_descr). References to other predicates are capitalized to
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
            grammars, for me the context is different).
      @todo Compare with describe_definition. *)
let describe_predicate global_name = function
  | Pred(_, _) as pred ->
    let name = get_predicate_name pred in
    let args = get_predicate_arguments pred in
    let name_str = if name = global_name then "Pred" else String.capitalize name in
    let args_str = describe_arguments args in
    "(" ^ name_str ^ " " ^ args_str  ^ ")"
  | _ -> failwith "not a predicate"

(*******************************************************************************
 * Predicate dependencies *
 **************************)

(** List of predicate metaterms within a metaterm.
    A predicate may appear more than once in the list. If used to extract
    identities of used predicates, unicity is not assured. *)
let rec get_predicates = function
  | True|False|Eq(_, _) -> []
  | Arrow(mt1, mt2)
  | Or(mt1, mt2)
  | And(mt1, mt2)       -> get_predicates mt1 @ get_predicates mt2
  | Binding(_, _, mt)   -> get_predicates mt
  | Pred(_, _) as p     -> [p]
  | Obj(_, _)           -> failwith "metaterm not supported"

(** Translation: load a predicate into a logic variable. *)
let describe_dependency id = id ^ " " ^ String.capitalize id

(** List external dependencies.
    @param name Name of the current scope (definition or theorem).
    @param defs List of definitions, assumed to describe 'name'.
    @return List of predicates other than 'name' present in 'defs', without
            duplicates.
    @raise On unsupported terms.
    @author Rob Blanco *)
let get_dependencies name defs =
  defs |>
  List.map get_predicates |>
  List.concat |>
  List.map get_predicate_name |>
  List.filter (fun x -> String.compare x name <> 0) |>
  List.sort_uniq String.compare

(** Translation: context-sensitive dependencies.
    @param name Name of the current scope (definition or theorem).
    @param defs List of definitions, assumed to describe 'name'.
    @decorate Context-dependent function to generate string output.
    @return List of predicates other than 'name' present in 'defs' loaded in
            uppercase same-named logic variables.
    @raise On unsupported terms.
    @author Rob Blanco
    @todo There is some duplication of steps and partial application across
          definitions and theorems. Refactor and clean. *)
let describe_dependencies name defs decorate =
  defs |>
  List.map (fun (_, body) -> body) |>
  get_dependencies name |>
  List.map describe_dependency |>
  and_descriptions |>
  decorate

(*******************************************************************************
 * Metaterms *
 *************)

(** Variables of a metaterm.
    Obviously inefficient implementation.
    @param metaterm The metaterm.
    @return List of variables in string format, without repeats.
    @raise On unsupported terms.
    @author Rob Blanco
    @todo Ensure that bound variables are never returned. *)
let rec get_metaterm_variables = function
  | True -> []
  | False -> []
  | Eq(t1, t2) ->
    List.sort_uniq String.compare (get_term_variables t1 @ get_term_variables t2)
  | Arrow(mt1, mt2)
  | Or(mt1, mt2)
  | And(mt1, mt2) ->
    List.sort_uniq String.compare (get_metaterm_variables mt1 @ get_metaterm_variables mt2)
  | Binding(_, _, mt) ->
    List.sort compare (get_metaterm_variables mt)
  | Pred(t, _) ->
    List.sort compare (get_term_variables t)
  | Obj(_, _) -> failwith "metaterm not supported"

(** Translation: body of a clause.
    Meta-object refactoring is probably not needed at this point.
    @param name Name of the predicate being translated.
    @param metaterm (Sub-)term representing a clause or part thereof.
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
let rec describe_metaterm name = function
  (* describe_metaterm *)
  | True -> "tt"
  | False -> "ff"
  | Eq(t1, t2) ->
    "(eq " ^ describe_term t1 ^ " " ^ describe_term t2 ^ ")"
  | Arrow(mt1, mt2) ->
    "(imp " ^ describe_metaterm name mt1 ^ " " ^ describe_metaterm name mt2 ^ ")"
  | Binding(b, idtys, mt) ->
    let ids = List.map (fun (id, _) -> id) idtys in (*TODO fst*)
    let ids_str = quantify b ids in
    "(" ^ ids_str ^ " " ^ describe_metaterm name mt ^ ")"
  | Or(mt1, mt2) ->
    "(or "  ^ describe_metaterm name mt1 ^ " " ^ describe_metaterm name mt2 ^ ")"
  | And(mt1, mt2) ->
    "(and " ^ describe_metaterm name mt1 ^ " " ^ describe_metaterm name mt2 ^ ")"
  | Pred(_, _) as p ->
    describe_predicate name p
  | Obj(_, _) ->
    failwith "metaterm not supported"

(*******************************************************************************
 * (Co)inductive definitions *
 *****************************)

(** Translation: single clause in a predicate definition to (disjunctive) clause
    in the fixed point encoding.
    @param def Clause tuple consisting of two components: {ol
     {- the head of the clause; and}
     {- the body of the clause.}}
    @return String representation of the encoding of the clause.
    @raise On invalid structures including unsupported features.
    @author Rob Blanco
    @todo Unify coding style where appropriate: hierarchical parsing vs. getters
          and manipulators. *)
let describe_definition (head, body) =
  let name = get_predicate_name head in
  let vars = get_metaterm_variables head in
  let args = get_predicate_arguments head in
  let vars_str = quantify Exists vars in
  let args_str = describe_arguments args in
  let body_str = describe_metaterm name body in
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
let rec describe_definitions = function
  | [] -> assert false
  | [hd] -> describe_definition hd
  | hd :: (hd' :: tl' as tl) ->
    "(or " ^ describe_definition hd ^ "\n" ^ describe_definitions tl ^ ")"

(** Translation: inductive predicate to least fixed point.
    The function produces a left-associative chain of disjunctions, each leaf
    encoding one of the clauses of the predicate.
    @param op String representation of fixed point type to be translated.
    @param defs List of predicate definitions in ordered, one-to-one
                 correspondence with the elements of 'idtys'.
    @param idtys List of tuples containing the names and types of the
                 predicates involved in the definition.
    @return String encoding of fixed point representing the predicate given by
            the definitions.
    @raise Mutually recursive definitions and definitions involving
           unsupported features. Possibly invalid structures, but without any
           guarantees (an error-free Abella parse tree is assumed).
    @author Rob Blanco
    @todo Add support for mutual recursion. *)
let describe_fixed_point op defs = function
  | [] -> assert false
  | _ :: _ :: _ -> failwith "mutual recursion not supported"
  | (name, _) :: [] ->
    let decorate str =
      if String.length str = 0
      then ""
      else "\n:=\n" ^ str
    in
    "Define " ^ name ^ " : (i -> bool) -> prop by\n" ^
    name ^ " (" ^ op ^ " Pred\\Args\\\n" ^
    describe_definitions defs ^
    "\n)" ^
    describe_dependencies name defs decorate ^
    ".\n"

let describe_define   defs idtys = describe_fixed_point "mu" defs idtys
let describe_codefine defs idtys = describe_fixed_point "nu" defs idtys

(*******************************************************************************
 * Theorems *
 ************)

(** Translation: theorem to predicate representing it as a formula.
    @param name Name of the predicate.
    @param thm Metaterm representation.
    @param String encoding of an inductive definition that returns the theorem
           formula.
    @raise On unsupported and invalid metaterms.
    @author Rob Blanco
    @todo Add support for mutual recursion.
    @todo Regarding dependencies: Recursion is irrelevant. Make name optional
          throughout and adapt interface. Refactoring to get dependencies to
          work on metaterms; then extend that to def pairs. *)
let describe_theorem name thm =
  let decorate str =
    if String.length str = 0
    then ""
    else  str ^ " /\\ " in
  let thm_str = describe_metaterm "" thm in (*HACK*)
  let deps_str = describe_dependencies "" [(True, thm)] decorate in (*HACK*)
  "Define " ^ name ^ " : bool -> prop by\n" ^
  name ^ " F :=\n" ^
  deps_str ^  "F =\n" ^
  thm_str ^
  ".\n"

(*******************************************************************************
 * Theorem proofs *
 ******************)

(*
let test_theorems =
  (*List.map fst !lemmas |> String.concat " "*)
  Printf.sprintf "%d" (List.length !lemmas)
*)

(*I assume everything is of my shape*)
let get_theorems =
  List.map fst !lemmas |>
  List.map (Str.replace_first (Str.regexp "__proof__$") "")

let get_proof_name pred_name =
  pred_name ^ "__proof__"

(*NAMING CONVENTION, HERE!!
  by default, make all previous lemmas available; otherwise we rely on a
  concrete proof, which currently we don't have, though it would be best
  TODO use proof script if at all possible and come back!
  TODO refactor with describe_dependency*)
let describe_proof_stub pred_name =
  let proof_name = pred_name ^ "__proof__" in
  let pred_var = String.capitalize pred_name in
  let describe_lemmas lemmas =
      List.fold_right (fun lemma acc ->
        Printf.sprintf "(lemma (name \"%s\") %s) :: %s"
                        pred_name
                        (String.capitalize pred_name)
                        acc)
        lemmas "nil"
  in
  Printf.sprintf "Define %s : cert -> prop by\n\
                  %s Cert :=\n\
                  %s %s /\\\n\
                  %s\
                  prove_with_lemmas Cert %s\n\
                  %s\n\
                  .\n"
                  proof_name
                  proof_name
                  pred_name pred_var
                  (List.map describe_dependency get_theorems |> and_descriptions) (*refactor, cf. describe_dependencies & friends; also consider newlines!*)
                  pred_var
                  (describe_lemmas get_theorems)

let describe_proof_check pred_name =
  Printf.sprintf "#assert %s\n\
                  **your certificate here**\n\
                  .\n"
                  (get_proof_name pred_name)

(*
#include "logic.thm".
#include "cert-sig.thm".
#include "admin-fpc.thm".
#include "plus-examples-sig.thm".
#include "kernel.thm".
#include "plus-examples.thm".
*)

(*******************************************************************************
 * Output file manipulation *
 ****************************)

let append text file =
  let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 file in
  output_string oc text ;
  close_out oc

let describe_copy_i =
  let (_, ctable) = !sign in
  List.map fst ctable |> String.concat " "
  

(*******************************************************************************
 * Module interface *
 ********************)

let ckind ids =
  append (describe_kind ids) "fpc-decl.mod"

let ctype ids ty =
  append (describe_type ids ty) "fpc-decl.mod" ;
  append (describe_copy_i) "fpc-decl.mod"

let cdefine defs idtys =
  append (describe_define defs idtys) "fpc-decl.mod"

let ccodefine defs idtys =
  append (describe_codefine defs idtys) "fpc-decl.mod"

let ctheorem id mterm =
  append (describe_theorem id mterm) "fpc-decl.mod" ;
  append (describe_proof_stub id) "fpc-decl.mod" ;
  append (describe_proof_check id) "fpc-test.mod"
