(** Export Abella sessions for external verification.
    @todo Use Core.Std? is_empty, concat_map... *)
(* what would happen during e.g. redefinitions?*)
(*Unify coding style where appropriate: hierarchical parsing vs. getters and manipulators. - this, now to general comments
 Good unit test framework
 Also note, it's really difficult to know where failwiths are propagaged! Only locally... same with exceptions? *)

open Printf

open Abella_types
open Metaterm
open Prover
open Term
open Typing

(*******************************************************************************
 * State *
 *********)

(* Full file translation can be performed piecewise for the most part, on a
 * rolling basis. Locally, we need to resort to symbol tables, e.g. as
 * maintained by Abella itself. The prover is written in an imperative fashion
 * and we must therefore adopt its conventions at least to some extent.
 *   For now the Abella state is used when needed, even though this is brittle
 * and offers few guarantees. However, full translation within Abella requires
 * additional bookkeeping, i.e., order is relevant, and signatures can only be
 * provided at session's end. In this sense, too, and for the sake of
 * uniformity, all commands are cached, and then processed in batch. *)

(** List of commands emitted from Abella, stored in reverse chronological
  * order. *)
let commands : compiled list ref = ref []

(*******************************************************************************
 * Helpers *
 ***********)

type signature_type =
| Type
| Predicate
| Variable

(** Signature type of a string identifier. If an identifier is not present in
  * the symbol table it is assumed to be a variable on fallback.
  * @param id String identifier. Fictional values must be avoided.
  * @return Signature type of 'id'. *)
let id_type id =
  let ctable = snd !sign in
  try
    let (_, Poly(_, Ty(_, ty))) = List.find (fun x -> fst x = id) ctable in
    if ty = "prop" then Predicate else Type
  with
  | Not_found -> Variable

(** Quantify a set of variables.
  * @param binder Type of quantification to apply to 'vars'.
  * @param vars List of strings representing variable names. Will be settified.
  *   May be empty.
  * @return String with the variables of 'vars' quantified over 'binder'. If
  *   nonempty, quantifiers are trailed by single spaces (relevant for
  *   formatting).
  * @raise Nabla quantification. *)
let quantify binder vars =
  let binder_str = (function
  | Forall -> "all"
  | Exists -> "some"
  | Nabla ->  failwith "binder not supported") binder in
  let varset = List.sort_uniq String.compare vars in
  let append_quantifier acc var = sprintf "%s%s %s\\ " acc binder_str var in
  List.fold_left append_quantifier "" varset

(** Meta-level conjunction of terms.
  * @param strs List of strings representing meta-level terms.
  * @return Meta-level conjunction. *)
let and_descriptions strs = String.concat " /\\ " strs

(*******************************************************************************
 * Kinds *
 *********)

(* Everything is be transparently 'i'-typed; kinds are thus not relevant. *)

(*******************************************************************************
 * Types *
 *********)

(** Output list of identifiers as string.
  * @param ids List of identifiers (strings).
  * @return Comma-separated list in string format. *)
let describe_ids ids =
  String.concat ", " ids

(** Output type description as string.
  * @param ty Type description.
  * @return Type description in string format. *)
let rec describe_ty = function Ty(tys, _) ->
  let tys_str = tys |> List.map describe_ty |> String.concat " -> " in
  match tys with
  | [] ->                                 "i" (* Simple type. *)
  | [_] ->         "( " ^ tys_str ^ " ) -> i" (* Left-associative. *)
  | _ :: _ :: _ ->        tys_str ^   " -> i" (* Right-associative. *)

(** Output type constructor declaration as string.
  * @param ids List of constructor ids being declared.
  * @param ty Type descriptor.
  * @return Type constructor representation in string format. *)
let describe_type ids ty =
  let ids_str = describe_ids ids in
  let ty_str = describe_ty ty in
  sprintf "Type %s %s.\n" ids_str ty_str

(*******************************************************************************
 * Terms *
 *********)

(** Get list of variables in a term.
  * @param term The term.
  * @return List (set) of variables in string format.
  * @raise Unsupported terms. *)
let rec term_variables = function
| Var(id) ->
  if id_type id.name = Variable then [id.name] else []
| App(_, args) -> (* The name cannot be a variable. *)
  args |>
  List.map term_variables |>
  List.concat |>
  List.sort_uniq String.compare
| Ptr(_) as ptr ->
  let var = observe ptr in
  term_variables var
| DB(_) | Lam(_, _) | Susp(_, _, _, _) -> failwith "term not supported"

(** Output term as string.
  * @param term The term.
  * @return String representation of the term.
  * @raise Unsupported terms. *)
let rec describe_term = function
| Var(id) -> id.name
| App(name, args) ->
  let name_str = describe_term name in
  let args_str = args |> List.map describe_term |> String.concat " " in
  sprintf "(%s %s)" name_str args_str
| Ptr(_) as ptr ->
  let var = observe ptr in
  describe_term var
| DB(_) | Lam(_, _) | Susp(_, _, _, _) -> failwith "term not supported"

(*******************************************************************************
 * Predicate calls *
 *******************)

(** Name of a predicate metaterm.
  * @param mterm Metaterm.
  * @return Name of the predicate metaterm.
  * @raise Failure to adhere to the standard encoding: a predicate metaterm
  *   with an application term inside with a pointer as its head that points to
  *   a variable representing the name of the predicate.
  * @todo Possible refactoring with similar functions. General-purpose vs.
  *   special-purpose decomposers returning the components. *)
let predicate_name =

  let variable_name = function
  | Var(id) ->
    if id_type id.name = Predicate then id.name
    else failwith "not a predicate"
  | DB(_) | Lam(_, _) | Susp(_, _, _, _) | App(_, _) | Ptr(_) ->
    failwith "not a variable" in

  let pointer_name = function
  | Ptr(_) as ptr ->
    let var = observe ptr in
    variable_name var
  | Var(_) | DB(_) | Lam(_, _) | Susp(_, _, _, _) | App(_, _) ->
    failwith "not a pointer" in

  let application_name = function
  | App(term, _) -> pointer_name term
  | Var(_) | DB(_) | Lam(_, _) | Susp(_, _, _, _) | Ptr(_) ->
    failwith "not an application" in

function
| Pred(term, _) -> application_name term
| True | False | Eq(_, _) | Obj(_, _) | Arrow(_, _)| Binding(_, _, _) |
  Or(_, _) | And(_, _) -> failwith "not a predicate"

(*
let get_predicate_name = function
  | Pred(App((Ptr(_) as ptr), _), _) ->
    let var = observe ptr in
    ( match var with
    | Var id ->
      if id_type id.name = Predicate
      then id.name
      else failwith "not a predicate"
    | _ -> failwith "bad observation" )
  | _ -> failwith "bad predicate"
*)

(** Arguments of a predicate metaterm in string format.
  * @param mterm Metaterm.
  * @return List of arguments passed to a predicate, each represented as string.
  * @raise Failure to adhere to the standard encoding: a predicate metaterm
  *   with an application term inside containing its list of arguments. *)
let predicate_arguments =

  let application_arguments = function
  | App(_, args) -> List.map describe_term args
  | Var(_) | DB(_) | Lam(_, _) | Susp(_, _, _, _) | Ptr(_) ->
    failwith "not an application" in

function
| Pred(term, _) -> application_arguments term
| True | False | Eq(_, _) | Obj(_, _) | Arrow(_, _)| Binding(_, _, _) |
  Or(_, _) | And(_, _) -> failwith "not a predicate"

(** Arguments of a fixed point expression in string format.
  *   Predicates are encoded through fixed points in the checker. All fixed
  * points use a single argument to encode arbitrary lists of arguments.
  * @param args List of strings representing arguments passed to a predicate.
  * @return String representing the single argument for the fixed point that
  *         translates the original predicate. *)
let describe_arguments = function
| [] -> "argv"
| _ :: _ as args ->
  let args_str = String.concat " ++ " args in
  sprintf "(%s ++ argv)" args_str

(** Predicate call within the encoding of another predicate in strong format.
  *   Encode a predicate call within the definition of a predicate. Self-
  * references are transformed by convention into the fixed point parameter
  * 'Pred', external references refer to the fixed point definitions of those
  * predicates pre-loaded into a same-named (capitalized) logic variable.
  * Identifiers cannot start with uppercase, so this encoding is safe barring
  * name clashes, which must be avoided.
  * @param main Name of the predicate being encoded.
  * @param mterm Predicate metaterm.
  * @return Predicate call in string format.
  * @todo To clarify where needed: variables may not be named after predicates
  *   for this simple encoding to work.
  * @todo Previously this code was re-used for raw variables. Explanations,
  *   renamings and adjustments might still be in order. Reuse in equality was
  *   especially questionable (as equality works on terms and the predicate
  *   context is different).
  * @todo Compare with describe_definition. *)
let describe_predicate main = function
| Pred(_, _) as pred ->
  let name = predicate_name pred
  and args = predicate_arguments pred in
  let name_str = if name = main then "Pred" else String.capitalize name
  and args_str = describe_arguments args in
  sprintf "(%s %s)" name_str args_str
| True | False | Eq(_, _) | Obj(_, _) | Arrow(_, _)| Binding(_, _, _) |
  Or(_, _) | And(_, _) -> failwith "not a predicate"

(*******************************************************************************
 * Predicate dependencies *
 **************************)

(** List of predicate metaterms within a metaterm.
  * @param mterm Metaterm.
  * @return List of predicate metaterms contained within 'mterm'.
  * @raise Unsupported metaterms.
  * @todo A predicate may appear more than once in the list. If used to extract
  *   identities of used predicates, unicity is not assured. (Should it?) *)
let rec get_predicates = function
| True
| False
| Eq(_, _) ->
  []
| Arrow(mt1, mt2)
| Or(mt1, mt2)
| And(mt1, mt2) ->
  get_predicates mt1 @ get_predicates mt2
| Binding(_, _, mt) ->
  get_predicates mt
| Pred(_, _) as p ->
  [p]
| Obj(_, _) -> failwith "metaterm not supported"

(** Pre-load dependency on a predicate.
  * @param id Name of a predicate that presents a dependency in the block
  *   being translated.
  * @return String representing the dependency in the meta-language, using the
  *   meta-level (lowercase) predicate to load its associated object-level fixed
  *   point representation in an uppercase same-named variable.
  * @todo The function name is not too illustrative. *)
let describe_dependency id = id ^ " " ^ String.capitalize id

(** List external dependencies.
  * @param name Name of the current scope (definition or theorem).
  * @param defs List of definitions, assumed to describe 'name'.
  * @return Set of predicates other than 'name' present in 'defs', no repeats.
  * @raise Unsupported definitions. *)
let get_dependencies name defs =
  let is_not_name str = String.compare str name <> 0 in
  defs |>
  List.map get_predicates |>
  List.concat |>
  List.map predicate_name |>
  List.filter is_not_name |>
  List.sort_uniq String.compare

(** Meta-level dependencies in string format.
    @param name Name of current scope (definition or theorem).
    @param defs List of definitions, assumed to describe 'name'.
    @param decorate Context-dependent function to generate string output.
    @return String loading the set of predicates other than 'name' present in
      'defs' in meta-level logic variables.
    @raise Unsupported definitions.
    @todo There is some duplication of steps and partial application across
      definitions and theorems to be refactored. *)
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
  * @param mterm Metaterm.
  * @return Set of variables in string format, without repeats.
  * @raise Unsupported metaterms.
  * @todo Ensure that bound variables are never returned.
  * @todo Rather inefficient implementation (again, a common grace). *)
let metaterm_variables mterm =

  let rec metaterm_variables_rec = function
  | True -> []
  | False -> []
  | Eq(t1, t2) -> term_variables t1 @ term_variables t2
  | Arrow(mt1, mt2)
  | Or(mt1, mt2)
  | And(mt1, mt2) -> metaterm_variables_rec mt1 @ metaterm_variables_rec mt2
  | Binding(_, _, mt) -> metaterm_variables_rec mt
  | Pred(t, _) -> term_variables t
  | Obj(_, _) -> failwith "metaterm not supported" in

  let vars = metaterm_variables_rec mterm in
  List.sort_uniq String.compare vars

(** Translation: body of a clause.
  * Meta-object refactoring is probably not needed at this point.
  * @param name Name of the context (predicate, theorem) being translated.
  * @param mterm (Sub-)term representing a clause or part thereof.
  * @return Metaterm in string format according to the encoding conventions in
  *  the meta-language, including self-references.
  * @raise Unsupported metaterms.
  * @todo Predicate-theorem unification is an ugly hack at the moment. Redesign
  *   maybe necessary to some moderate extent.
  * @todo Would a generic print_metaterm be a better alternative?
  * @todo Minor simplifications: if the body is trivially true, drop the clause
  *   in disjunctive contexts. Being recursive, it is a bit more delicate than
  *   "just do it". *)
let rec describe_metaterm name =

  let describe_connective = function
  | True -> "tt"
  | False -> "ff"
  | Eq(_, _) -> "eq"
  | Arrow(_, _) -> "imp"
  | Or(_, _) -> "or"
  | And(_, _) -> "and"
  | Binding(_, _, _) | Pred(_, _) | Obj(_, _) -> failwith "not a connective" in

function
| True | False as mt ->
  describe_connective mt
| Eq(t1, t2) as mt ->
  let operator = describe_connective mt
  and operand1 = describe_term t1
  and operand2 = describe_term t2 in
  sprintf "(%s %s %s)" operator operand1 operand2
| Arrow(mt1, mt2) | Or(mt1, mt2) | And(mt1, mt2) as mt ->
  let operator = describe_connective mt
  and operand1 = describe_metaterm name mt1
  and operand2 = describe_metaterm name mt2 in
  sprintf "(%s %s %s)" operator operand1 operand2
| Binding(b, idtys, mt) ->
  let eigenvars = List.map fst idtys in
  let quantifiers = quantify b eigenvars in
  let operand = describe_metaterm name mt in
  sprintf "(%s%s)" quantifiers operand
| Pred(_, _) as p ->
  describe_predicate name p
| Obj(_, _) -> failwith "metaterm not supported"

(*
function
| True -> "tt"
| False -> "ff"
| Eq(t1, t2) ->
  "(eq " ^ describe_term t1 ^ " " ^ describe_term t2 ^ ")"
| Arrow(mt1, mt2) ->
  "(imp " ^ describe_metaterm name mt1 ^ " " ^ describe_metaterm name mt2 ^ ")"
| Binding(b, idtys, mt) ->
  let ids = List.map (fun (id, _) -> id) idtys in (*TODO fst*)
  let ids_str = quantify b ids in
  "(" ^ ids_str ^ describe_metaterm name mt ^ ")"
| Or(mt1, mt2) ->
  "(or "  ^ describe_metaterm name mt1 ^ " " ^ describe_metaterm name mt2 ^ ")"
| And(mt1, mt2) ->
  "(and " ^ describe_metaterm name mt1 ^ " " ^ describe_metaterm name mt2 ^ ")"
| Pred(_, _) as p ->
  describe_predicate name p
| Obj(_, _) -> failwith "metaterm not supported"
*)

(*******************************************************************************
 * (Co)inductive definitions *
 *****************************)

(** Single clause of predicate definition to (disjunctive) fixed point clause.
  * @param def Clause tuple consisting of head and body of the clause.
  * @return Fixed point encoding of the clause in string format.
  * @raise Unsupported definitions. *)
let describe_definition (head, body) =
  let name = predicate_name head
  and vars = metaterm_variables head
  and args = predicate_arguments head in
  let vars_str = quantify Exists vars
  and args_str = describe_arguments args
  and body_str = describe_metaterm name body in
  sprintf "(%s(and (eq Args %s)\n%s\n))" vars_str args_str body_str
(*
  "(" ^ vars_str ^ "(and (eq Args " ^ args_str ^ ")\n" ^
  body_str ^
  "\n))"
*)

(** Multi-clause predicate definition to disjunctive fixed point, sans header.
  *   Produces a left-associative chain of disjunctions, each leaf encoding one
  * clause of the predicate. Interestingly, each clause is entirely self
  * contained, i.e. the encoding deviates from my manual, early examples in that
  * it lacks a top-level argument parsing, used to give common names to the
  * arguments, shared by all clauses. Here instead, each clause parses the
  * arguments according to its head, which is more verbose, but also allows more
  * compact bodies, as parameters can be made to match more complex expressions;
  * critically, the procedure is entirely local. (I first ran into this variant
  * dealing with context subsumption.)
  * @param defs Nonempty list of clauses defining a (co)inductive predicate.
  * @return String representation of the fixed point encoding.
  * @raise Invalid definitions.
  * @todo Add support for undefined clauses, and is this the right place? *)
let rec describe_definitions = function
| [] -> assert false
| [hd] ->
  describe_definition hd
| hd :: (_ :: _ as tl) ->
  sprintf "(or %s\n%s)" (describe_definition hd) (describe_definitions tl)
(*
  "(or " ^ describe_definition hd ^ "\n" ^ describe_definitions tl ^ ")"
*)

(** Inductive predicate to least fixed point in string format.
  * @param op String representation of fixed point type to be translated.
  * @param defs List of predicate definitions in ordered, one-to-one
  *   correspondence with the elements of 'idtys'.
  * @param idtys List of tuples containing the names and types of the
  *   predicates involved in the definition.
  * @return String encoding of fixed point representing the predicate(s).
  * @raise Mutually recursive definitions. Definitions involving unsupported
  *   features. Possibly invalid structures, without any guarantees throughout
  *   (we are assuming an error-free Abella parse tree).
  * @todo Add support for mutual recursion. *)
let describe_fixed_point op defs = function
| [] -> assert false
| _ :: _ :: _ -> failwith "mutual recursion not supported"
| [(name, _)] ->
  let decorate str = if String.length str = 0 then "" else "\n:=\n" ^ str in
  sprintf
    "Define %s : (i -> bool) -> prop by\n\
     %s (%s Pred\\Args\\\n\
     %s\n\
     )%s.\n"
    name
    name op
    (describe_definitions defs)
    (describe_dependencies name defs decorate)

(*
  "Define " ^ name ^ " : (i -> bool) -> prop by\n" ^
  name ^ " (" ^ op ^ " Pred\\Args\\\n" ^
  describe_definitions defs ^
  "\n)" ^
  describe_dependencies name defs decorate ^
  ".\n"
*)

let describe_define defs idtys = describe_fixed_point "mu" defs idtys
let describe_codefine defs idtys = describe_fixed_point "nu" defs idtys

(*******************************************************************************
 * Theorems *
 ************)

(** Theorem to predicate as a formula (object-level fixed point) as string.
  * @param name Name of the theorem.
  * @param thm Theorem as metaterm.
  * @param Inductive definition that returns the theorem formula, as string.
  * @raise Unsupported metaterms.
  * @todo The main encodings are UNTOWARD HACKS and must be fixed. Recursion is
  *   not relevant as concerns dependencies. The name is optional in some
  *   contexts. Dependencies should work first on metaterms and then extend to
  *   defs. Rename, refactor, etc. *)
let describe_theorem name thm =
  let decorate str = if String.length str = 0 then "" else  str ^ " /\\ " in
  let thm_str = describe_metaterm "" thm in (*HACK*)
  let deps_str = describe_dependencies "" [(True, thm)] decorate in (*HACK*)
  sprintf
    "Define %s : bool -> prop by\n\
     %s F :=\n\
     %sF =\n\
     %s.\n"
    name
    name
    deps_str
    thm_str
(*
  "Define " ^ name ^ " : bool -> prop by\n" ^
  name ^ " F :=\n" ^
  deps_str ^  "F =\n" ^
  thm_str ^
  ".\n"
*)

(*******************************************************************************
 * Theorem proofs *
 ******************)

(** List of theorem names acting as possible lemmas to another theorem (i.e. the
  * list of theorems that has been defined and proved to date).
  * @param pred_name Name of the theorem.
  * @return List of allowed lemma names.
  * @todo Ensure no repeats and oddities, e.g. on theorem redefinitions. *)
let get_lemma_names pred_name =

  let rec discard_until_theorem name = function
  | [] -> []
  | CTheorem(id, _) :: tl when id = name -> tl
  | _ :: tl -> discard_until_theorem name tl in

  let is_theorem = function
  | CTheorem(_, _) -> true
  | CDefine(_, _) | CCoDefine(_, _) | CImport(_) | CKind(_)| CType(_, _) |
    CClose(_) -> false in

  let theorem_name = function
  | CTheorem(id, _) -> id
  | CDefine(_, _) | CCoDefine(_, _) | CImport(_) | CKind(_)| CType(_, _) |
    CClose(_) -> failwith "not a theorem" in

  !commands |>
  discard_until_theorem pred_name |>
  List.filter is_theorem |>
  List.map theorem_name

(** Declaration of admissible lemmas in a proof.
  * @param lemmas Set of lemma names.
  * @return Meta-level declaration of lemmas by convention, in string format.
  * @todo Not checking set-ness, make sure no craziness can happen (and add
  *   check anyway). *)
let describe_lemma_list lemmas =
  let prepend_lemma_descr lemma_name descr =
    let lemma_var = String.capitalize lemma_name in
    sprintf "(lemma (name \"%s\") %s) :: %s" lemma_name lemma_var descr in
  List.fold_right prepend_lemma_descr lemmas "nil"

(** Name of the proof predicate for a given theorem predicate.
  * @param pred_name Name of the theorem predicate.
  * @return Name of the associated proof predicate (must not be used as user-
  *   defined predicate name). *)
let proof_name pred_name =
  pred_name ^ "__proof__"

(** Generate proof predicate for a given theorem, in string format.
  *   By default, all previous lemmas are made available to the certificate.
  * This will offer more choice than is necessary and slow down checking, but
  * does not consider any proof details whatsoever and is most flexible. For now
  * a good starting point, even though using proof scripts if at all available
  * is much better.
  * @param pred_name Name of the theorem predicate.
  * @return Name of the associated proof predicate (must not be used as user-
  *   defined predicate name).
  * @raise (Given by subfunctions, likely nothing by construction.)
  * @todo lemma_deps: consider common computations with describe_dependencies
  *   and friends and refactor. Also, newlines. Together with lemmas, improve
  *   legibility.
  * @todo Use proof scripts if at all possible (i.e., extend parser). *)
let describe_proof_stub pred_name =

  let proof_pred = proof_name pred_name in
  let pred_var = String.capitalize pred_name in
  
  let decorate str = if String.length str = 0 then "" else  str ^ " /\\\n" in
  let lemmas =
    get_lemma_names pred_name |>
    List.filter (fun x -> x <> pred_name) in
  let lemma_deps =
    lemmas |>
    List.map describe_dependency |>
    and_descriptions |>
    decorate in

  sprintf
    "Define %s : cert -> prop by\n\
     %s Cert :=\n\
     %s %s /\\\n\
     %s\
     prove_with_lemmas Cert %s\n\
     (%s)\n\
     .\n"
    proof_pred
    proof_pred
    pred_name pred_var
    lemma_deps
    pred_var
    (describe_lemma_list lemmas)

(** Assert proof predicate, with certificate placeholder.
  * @param pred_name Name of the theorem predicate.
  * @return String assertion for the proof predicate associated to the given
  *   theorem predicate. *)
let describe_proof_check pred_name =
  sprintf "#assert %s\n**your certificate here**\n.\n" (proof_name pred_name)

(*******************************************************************************
 * Output file manipulation *
 ****************************)

(** Append string to a file.
  *   It obviously makes for inefficient I/O and is a remnant of the first,
  * fully interactive-oriented implementation. But for now, quick and relatively
  * "clean".
  * @param text String.
  * @param file Filename. *)
let append text file =
  let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 file in
  output_string oc text ;
  close_out oc

(* Gosh, top-level hiding doesn't make any sense!
let describe_copy_i =
  let (_, ctable) = !sign in
  ctable |> List.map fst |> String.concat " "
*)

(*******************************************************************************
 * File generation *
 *******************)

(** Create list of prefixed, numbered arguments.
  *   Clearly suboptimal. Not prettily, but not substantially, generated in
  * reverse order for simplicity.
  * @param argc Length of the list/number of arguments. Nonnegative (no check).
  * @param prefix Shared name prefix.
  * @return List of 'argc' strings prefixed with 'prefix', from 'argc' to 1. *)
let rec generate_argument_list argc prefix =
  if argc = 0 then []
  else
    let hd = prefix ^ string_of_int argc in
    let tl = generate_argument_list (argc - 1) prefix in
    hd :: tl

(** Instantiate type constructor, string format.
  * @param name Constructor name.
  * @param argc Constructor cardinality.
  * @param prefix Name prefix of numbered list of arguments.
  * @return Constructor as string.
  * @todo Brittle, i.e. accepts wrong cardinalities (and negatives).
  * @todo Test with infix operators. *)
let describe_constructor name argc prefix =
  let arg_list argc prefix =
    generate_argument_list argc prefix |> String.concat " " in
  if argc = 0 then name else sprintf "(%s %s)" name (arg_list argc prefix)

(** Generate two lists of variables and the meta-level string that copies each
  * pair of the lists.
  * @param argc Number of variables in each list.
  * @param prefix1 Name prefix of the first numbered list.
  * @param prefix2 Name prefix of the second numbered list.
  * @return Predicate as string.
  * @todo Prefixes must be different, argc positive.
  * @todo Both inefficient and arguably ugly when used (see below). It seems
  *   better to reflect dependencies in computation. *)
let describe_copy_i_constructor argc prefix1 prefix2 =
  let args1 = generate_argument_list argc prefix1
  and args2 = generate_argument_list argc prefix2
  and copy_i_pair var1 var2 = sprintf "copy_i Theta %s %s" var1 var2 in
  let copies = List.map2 copy_i_pair args1 args2 |> and_descriptions in
  if argc = 0 then "" else sprintf ":= %s " copies

(** Generate term copy predicate for declared type constructors.
  * @return Predicate as string.
  * @todo Refactoring, constants... probably treat "kernel pervasives" in a
  *   unified way. Poly-Ty pattern. *)
let describe_copy_i () =

  let user_constructors (_, Poly(_, Ty(_, base))) =
    not (List.exists (fun x -> x = base) (fst pervasive_sign)) in
  let constructor_nameargc (name, Poly(_, Ty(args, _))) =
    (name, List.length args) in
  let map_copy_i (name, argc) =
    let constr1 = describe_constructor name argc "A"
    and constr2 = describe_constructor name argc "B"
    and copy_vars = describe_copy_i_constructor argc "A" "B" in
    sprintf "copy_i Theta %s %s %s;\n" constr1 constr2 copy_vars in

  let (_, ctable) = !sign in
  let body_str =
    ctable |>
    List.filter user_constructors |>
    List.map constructor_nameargc |>
    List.map map_copy_i |>
    String.concat "" in

  sprintf
    "Define copy_i : list imap -> i -> i -> prop by\n\
     %s\
     copy_i Theta argv argv ;\n\
     copy_i Theta (X ++ Y) (U ++ V) := copy_i Theta X U /\\ copy_i Theta Y V."
    body_str

(** Pervasive predicate check.
  * @param name Predicate name.
  * @returns True iff 'name' is not user-defined (belongs to Abella's pervasive
  *   signature).
  * @todo Improved legibility. *)
let is_pervasive name =
  pervasive_sign |>
  snd |>
  List.map fst |>
  List.exists (fun x -> x = name)

(** Generate debugging predicate for declared fixed points.
  * @return Predicate as string.
  * @todo Refactor code from (old) id_type, copy_i patterns, use of
  *   pervasive_sign and filtering function, capitalization patterns with
  *   proper functions, is_predicate constants, etc.
  * @todo Test with no user-defined predicates, extravagant as it is. *)
let describe_name_mnu () =

  (* Filter function. *)
  let is_predicate (_, Poly(_, Ty(_, base))) = base = "prop" in

  (* List of user-defined predicates. *)
  let (_, ctable) = !sign in
  let preds =
    ctable |>
    List.filter is_predicate |>
    List.map fst |>
    List.filter (fun x -> not (is_pervasive x)) in

  (* Treat empty predicate list. *)
  let def_nopreds = 
    "Define name_mnu : string -> (i -> bool) -> prop by name_mnu _ _ := false."

  (* Treat nonempty predicate list. *)
  and def_preds preds =
    let map_name_mnu pred =
      let predvar = String.capitalize pred in
      sprintf "name_mnu \"%s\" %s := %s %s" pred predvar pred predvar in
    let body = preds |> List.map map_name_mnu |> String.concat " ;\n" in
    sprintf "Define name_mnu : string -> (i -> bool) -> prop by\n%s." body in
  
  if List.length preds = 0 then def_nopreds else def_preds preds

(** Signature file.
  * @return File contents as string. *)
let describe_signature () =
  sprintf
    "#include \"fpc-decl.mod\".\n\
     \n\
     %s\n\
     \n\
     %s\n\
     \n"
    (describe_copy_i ())
    (describe_name_mnu ())

(** Stitch all the parts together to get a working checking instance.
  *   Because of the very primitive modular support in Bedwyr, we need to do
  * this as in the olden days, resolving dependencies by convention and
  * carefully separating everything into modules. This is going to be VERY
  * sensitive to changes, but hopefully will not change much.
  *   This goes at the top of the test file (i.e., the only file that the user
  * needs to interact with). *)
let describe_kernel () =
  "#include \"logic.thm\".\n\
   #include \"cert-sig.thm\".\n\
   #include \"admin-fpc.thm\".\n\
   #include \"fpc-sign.mod\".\n\
   #include \"kernel.thm\".\n\
   #include \"fpc-thms.mod\".\n\
   \n"

(** Start translation initializing output files.
  *   Basically, take care of the parts that have an order dependency, and
  * cannot be performed stepwise. Most importantly the signature, which requires
  * the whole set of instructions to proceed, but also the "system declaration"
  * of the test file (in some circumstances, this could be done separately and
  * at the beginning, but it becomes trickier in practice).
  * @todo Clear files at the top. *)
let start_files () =
  append (describe_signature ()) "fpc-sign.mod" ;
  append (describe_kernel ()) "fpc-test.mod"

(*******************************************************************************
 * Command processing *
 **********************)

(** Translate single command.
  * @param cmd Compiled command.
  * @raise Unsupported commands and translation errors. *)
let process_command = function
| CTheorem(id, mterm) ->
  append (describe_theorem id mterm) "fpc-thms.mod" ;
  append (describe_proof_stub id) "fpc-thms.mod" ;
  append (describe_proof_check id) "fpc-test.mod"
| CDefine(idtys, defs) ->
  append (describe_define defs idtys) "fpc-decl.mod"
| CCoDefine(idtys, defs) ->
  append (describe_codefine defs idtys) "fpc-decl.mod"
| CType(ids, ty) ->
  append (describe_type ids ty) "fpc-decl.mod"
| CKind(_) | CImport(_) | CClose(_) -> failwith "unsupported command"

(** Process command queue in chronological order.
  * @raise Translation errors. *)
let process_commands () =
  !commands |>
  List.rev |>
  List.iter process_command
  
(*******************************************************************************
 * Module interface *
 ********************)

(*I'm unsure that decomposing the commands into their arguments is best*)
(*There are much more elegant architectures. Ideally, I would translate the
  parse tree into another target parse tree, and implement printing functions
  for each of these components.*)

(** Queue command for batch translation.
  * @param cmd Compiled command.
  * @raise Unsupported commands. *)
let register cmd = match cmd with
| CTheorem(_, _)
| CDefine(_, _)
| CCoDefine(_, _)
| CType(_,_) -> commands := (cmd :: !commands)
| CKind(_) -> ()
| CImport(_) | CClose(_) -> failwith "unsupported command"

(** Translate the queue of stored commands into a standard set of files for
  * consumption of the checker.
  *   At least part of the translation must be triggered by one such command.
  *   Currently, certification generates a translation of the command queue that
  * can be fed into the proof checker using the "standard" administrative FPC
  * architecture. At the moment filenames are hardwired. The files being
  * generated and their contents are: {
  *   {- fpc-decl.mod: type constructores and predicate declarations.}
  *   {- fpc-sign.mod: signature of the declarations, automatically derived from
  *      these and used by the kernel and for debugging. It includes the
  *      declarations file for further uses and defines copy_i and name_mnu.}
  *   {- fpc-thms.mod: encoded theorems and their associated proof predicates.}
  *   {- fpc-test.mod: assembly of all previous files and assertion stubs for
  *      proof predicates. Certificates need to be filled out, but everything is
  *      otherwise "plug and play".}}
  * @raise Unsupported structures present in the list (may still produce a
  *   partial translation). *)
let certify () =
  start_files () ;
  process_commands () ;
  commands := []
