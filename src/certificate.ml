(*
(******************************************************************************)
(*RB*)(*A translation module should be hack-added here*)

(* TODO
   - Substitute predicate names for logic variables and add their identification
     with the corresponding generated fixed points.
   - Unary predicates (bad argument sequence) and variables as atoms. To tell
     these two apart, I need symbol tables again. *)

(*************************
 * Interface with Abella *
 *************************)


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

(* much of this can be refactored, see define_descr ... *)
let fpc_theorem_formula name thm =
  "Define " ^ name ^ " : bool -> prop by\n" ^
  name ^ " F :=\n" ^
  fpc_udefs_ext name [(UTrue,thm)] (* there are some things to format there! *) ^  " /\ F =\n" ^
  fpc_udef_body name thm ^ (* where is the name here? *)
  "."

let fpc_theorem name thm =
  (* As nested functions?
     1. Define formula predicate
     2. Define prover predicate (we can include the certificate here and keep things simple)
        - Allow all previously defined theorems as lemmas
        - Provide a certificate
     3. Define test *)
  fpc_theorem_formula name thm (*^
  fpc_theorem_proof name thm ^
  fpc_theorem_check name*)

let fpc_codefine idtys udefs =
  fprintf stdout "FPC codefine"
*)

open Metaterm
open Prover
open Term (* phase this out? *)
open Typing

let check_noredef ids =
  let (_, ctable) = !sign in
    List.iter (
      fun id -> if List.mem id (List.map fst ctable) then
        failwith "Predicate or constant already exists"
    ) ids

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

(*
let rec fpc_uterm = function
  | UCon(pos, id, ty) -> "{Con/" ^ id ^ ", " ^ ty_descr ty ^ "}"
  | ULam(pos, id, ty, uterm) -> "{Lam/" ^ id ^ ", " ^ ty_descr ty ^ ", " ^ fpc_uterm uterm ^ "}"
  | UApp(pos, uterm_x, uterm_y) -> "{App/" ^ fpc_uterm uterm_x ^ ", " ^ fpc_uterm uterm_y ^ "}"


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

*)
(******************************************************************************)

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
            grammars, for me the context is different). *)
let describe_predicate name pred args =
  let pred_str = if pred = name then "Pred" else String.capitalize pred in
  "(" ^ pred_str ^ " " ^ describe_arguments args ^ ")"

(***************
 * Definitions *
 ***************)

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
let rec parse_term =
  (** Translation: argument of a predicate call.
      @param uterm Term representing an argument in a predicate call.
      @return String representation of the argument of a predicate call.
      @raise Matching errors on invalid structures.
      @author Rob Blanco
      @todo I had some notes here that I think have been taken proper care of.
            Consult if something goes wrong or greater generality is still
            needed. *)
(*
  let parse_arg term =
    (** Translation: argument of a predicate call, recursive elaboration.
        Arguments to predicate calls are either monotype variables or, more
        generally, expressions involving monotype variables and monotype
        constructors. These constructors can take parameters and be nested.
        @param level Current parse depth.
        @param uterm (Sub)term representing an argument in a predicate call.
        @return String representation of the argument of a predicate call.
        @raise Matching errors on invalid structures.
        @author Rob Blanco *)
    let rec parse_arg_rec level = function
      (* An identifier at the top is a variable, at the bottom of a degenerate
         left chain it is a constructor that opens the string representation of
         the term. *)
      | Var(var) ->
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
        (* parse_arg_rec *)
        if level = 0
        then if fpc_declared_id var.name
          then ([], var.name)
          else ([var.name], var.name)
        else ([], "(" ^ var.name)
      (* An application always consists of two parts: a left traversal of the
         degenerate tree with its previous arguments, if any, yielding an open
         (incomplete) term representation. This is the recursive part proper. On
         the right, the corresponding argument is parsed and added to the string
         representation. At the top of the chain, this closes the term. *)
      | App(_, uterm_l, uterm_r) ->
        let (vars_l, arg_l) = parse_arg_rec (level + 1) uterm_l in
        let (vars_r, arg_r) = parse_arg_rec 0 uterm_r in
        let terminator = if level = 0 then ")" else "" in
        (vars_l @ vars_r, arg_l ^ " " ^ arg_r ^ terminator)
      (* Error *)
      | Lam(_,_,_,_)|DB(_)|Susp(_,_,_,_)|Ptr(_) -> failwith "term not supported"
    (* parse_arg *)
    in
    parse_arg_rec 0 uterm
  (* parse_head *)
  in *) function
  | Var(v) ->
    ( match check_id v.name with
    | Type -> Printf.sprintf "[Var-Type %s]" v.name
    | Predicate -> Printf.sprintf "[Var-Pred %s]" v.name
    | Variable -> Printf.sprintf "[Var-Var %s]" v.name )
  | DB(i) -> Printf.sprintf "[DB %d]" i
  | Lam (tyctx, term) -> Printf.sprintf "[Lambda %s]" (parse_term term)
  | App (term, terms) ->
    let term_str = parse_term term in
    let terms_str = List.map parse_term terms |> String.concat " ; " in
    Printf.sprintf "[App %s {%s}]" term_str terms_str
  | Susp(term, _, _, _) -> Printf.sprintf "[Susp %s]" (parse_term term)
  | Ptr p as t -> Printf.sprintf "[Ptr %s]" (parse_term (observe t))
  (**  
  (* Base case: predicate name at the bottom on the left *)
  | Var(var) -> (var.name, [], [])
  (* Recursive case: process each argument *)
  | App(_, term_l, term_r) ->
      let (name, vars_l, args_l) = parse_term term_l in
      let (vars_r, arg_r) = parse_arg term_r in
      let vars_uniq = List.sort_uniq String.compare (vars_l @ vars_r) in
      (name, vars_uniq, args_l @ [arg_r])
  (* Errors *)
  | Lam(_,_,_,_)|DB(_)|Susp(_,_,_,_)|Ptr(_) -> failwith "term not supported"
**)

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
(*TODO this must be generalized*)
let parse_head = function
  (* Errors *)
  | True|False|Eq(_,_)|Obj(_,_)|Arrow(_,_)|Binding(_,_,_)|Or(_,_)|And(_,_) ->
    failwith "metaterm not supported"
  (* Treatment for predicates *)
  | Pred(term, _) -> parse_term term
(******************************************************************************)

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
let rec describe_metaterm name = function
  (* describe_metaterm *)
  | True -> "tt"
  | False -> "ff"
  | Eq(t1, t2) -> (* This case may work, but it doesn't look clean at all *)
(*
    let (pred1, _, args1) = parse_term t1 in
    let (pred2, _, args2) = parse_term t2 in
    let t1_str = describe_predicate name pred1 args1 in
    let t2_str = describe_predicate name pred2 args2 in
*) let t1_str = parse_term t1 in let t2_str = parse_term t2 in
    "(eq " ^ t1_str ^ " " ^ t2_str ^ ")"
  | Arrow(mt1, mt2) ->
    "(imp " ^ describe_metaterm name mt1 ^ " " ^ describe_metaterm name mt2 ^ ")"
  | Binding(b, idtys, mt) ->
    let ids = List.map (fun (id, _) -> id) idtys in (* Used elsewhere? *)
    let ids_str = quantify b ids in
    "(" ^ ids_str ^ " " ^ describe_metaterm name mt ^ ")"
  | Or(mt1, mt2) ->
    "(or "  ^ describe_metaterm name mt1 ^ " " ^ describe_metaterm name mt2 ^ ")"
  | And(mt1, mt2) ->
    "(and " ^ describe_metaterm name mt1 ^ " " ^ describe_metaterm name mt2 ^ ")"
  | Pred(_, _) as p ->
    (*let (pred, _, args) =*) parse_head p (*in
    describe_predicate name pred args*)
  | Obj(_, _) ->
    failwith "metaterm not supported"

let describe_body name body = describe_metaterm name body

(** Translation: single clause in a predicate definition to (disjunctive) clause
    in the fixed point encoding.
    @param def Clause tuple consisting of two components: {ol
     {- the head of the clause; and}
     {- the body of the clause.}}
    @return String representation of the encoding of the clause.
    @raise On invalid structures including unsupported features.
    @author Rob Blanco *)
(*A flexible idea: a category of functions "visit_predicates"... that take other functions instructing what to do with the selected nodes, so we may reuse and clarify things*)
let describe_definition (head, body) =
  let (*name, vars, args*)temp_str = parse_head head in
  (*let vars_str = quantify Exists vars in
  let args_str = describe_arguments args in*)
  let body_str = describe_body (*name*)"dummy" body in
  (*"(" ^ vars_str ^ " (and (eq Args " ^ args_str ^ ")\n"*) temp_str ^
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

(******************************************************************************)

(*********
 * Kinds *
 *********)

let describe_kind ids = "" (* Everything will be transparently 'i'-typed *)

(******************************************************************************)

(*********
 * Types *
 *********)

let describe_ids ids =
  String.concat ", " ids

let rec describe_ty = function Ty(tys, id) ->
  let tys_str = List.map describe_ty tys |> String.concat " -> " in
  match tys with
  | []          ->                             id (* Simple type *)
  | [_]         -> "( " ^ tys_str ^ " ) -> " ^ id (* Left-associative *)
  | _ :: _ :: _ ->        tys_str ^   " -> " ^ id (* Right-associative *)

let describe_type ids ty =
  let ids_str = describe_ids ids in
  let ty_str = describe_ty ty in
  "Type " ^ ids_str ^ " " ^ ty_str ^ ".\n"

(******************************************************************************)



(*************************
 * Inductive definitions *
 *************************)

let describe_dependency id = id ^ " " ^ String.capitalize id
let and_descriptions strs = String.concat " /\ " strs
 
let describe_body defs = describe_definitions defs






let rec get_predicates = function
  | True|False|Eq(_, _) -> []
  | Arrow(mt1, mt2)
  | Or(mt1, mt2)
  | And(mt1, mt2)       -> get_predicates mt1 @ get_predicates mt2
  | Binding(_, _, mt)   -> get_predicates mt
  | Pred(_, _) as p     -> [p]
  | Obj(_, _)           -> failwith "metaterm not supported"

(*name polymorphism?
  also very important: when changing to FUNCTION, make sure to clean up the argument!*)
let get_predicate_name =
  (*let rec get_predicate_name_rec = function
    | UApp(_, term_l, _) -> get_predicate_name_rec term_l
    | UCon(_, id, _) -> id
    | _ -> failwith "term not supported"
  in*) function
  | Pred(term, _) -> (*get_predicate_name_rec term*)"Calimero"
  | _ -> failwith "not a predicate"

let get_dependencies name defs =
  (*List.concat_map get_predicates defs |> *)
  List.map get_predicates defs |>
  List.concat |>
  List.map get_predicate_name |>
  List.filter (fun x -> String.compare x name <> 0) |>
(*  List.map describe_predicate_name |> *)
  List.sort_uniq String.compare (*|>
  String.concat " /\ " |>
  sandwich ":= " "."*)

(*
let fpc_udefs_ext name defs =
  let decorate str =
    if String.length str = 0
    then ""
    else "\n:=\n" ^ str
  in
(*  List.map (fun (_, body) -> test_fun name body) udefs |> *)
  List.map (fun (_, body) -> body) defs |>
  get_dependencies name |>
(*  List.concat |>
  List.sort_uniq String.compare |> *)
  List.map describe_dependency |>
  and_descriptions |>
  decorate

(*let get_dependencies name defs = []*)
*)






let describe_dependencies name defs =
  let decorate str =
    if String.length str = 0
    then ""
    else "\n:=\n" ^ str
  in
  List.map (fun (_, body) -> body) defs |>
  get_dependencies name |>
  List.map describe_dependency |>
  and_descriptions |>
  decorate

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
let describe_fixed_point op defs = function
  | [] -> assert false
  | _ :: _ :: _ -> failwith "mutual recursion not supported"
  | (name, _) :: [] ->
    "Define " ^ name ^ " : (i -> bool) -> prop by\n" ^
    name ^ " (" ^ op ^ " Pred\\Args\\\n" ^
    describe_body defs ^
    "\n)" ^
    describe_dependencies name defs ^
    ".\n"

(* New names
  fpc_udefs ->  define_descr_body
  fpc_udefs_ext -> define_descr_deps
  These are udefs, but I'll name them defs and translate... *)
(*
  let (name, _) = List.hd idtys in
  "Define " ^ name ^ " : (i -> bool) -> prop by\n" ^
  name ^ " (mu Pred\\Args\\\n" ^
  fpc_udefs udefs ^
  "\n)."
*)

let describe_define defs idtys = describe_fixed_point "mu" defs idtys
let describe_codefine defs idtys = describe_fixed_point "nu" defs idtys

(******************************************************************************)
let append text file =
  let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 file in
  output_string oc text ;
  close_out oc
(******************************************************************************)

let ckind ids = append (describe_kind ids) "fpc-decl.mod"
let ctype ids ty = append (describe_type ids ty) "fpc-decl.mod"
let cdefine defs idtys = append (describe_define defs idtys) "fpc-decl.mod"
let ccodefine defs idtys = append (describe_codefine defs idtys) "fpc-decl.mod"
let ctheorem id mterm = append "ctheorem" "fpc-decl.mod"
