(* Should I have an object-oriented syntax, with files to dump to? For now, strings *)

(* Compiled declarations *)
val ckind : Term.id list -> string
val ctype : Term.id list -> Term.ty -> string
val cdefine : Abella_types.defs -> Term.tyctx -> string
val ccodefine : Abella_types.defs -> Term.tyctx -> string
val ctheorem : Term.id -> Metaterm.metaterm -> string

(* Interactive declarations *)
