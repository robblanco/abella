(* Should I have an object-oriented syntax, with files to dump to? For now, strings *)

(* Compiled declarations *)
val ckind : Term.id list -> unit
val ctype : Term.id list -> Term.ty -> unit
val cdefine : Abella_types.defs -> Term.tyctx -> unit
val ccodefine : Abella_types.defs -> Term.tyctx -> unit
val ctheorem : Term.id -> Metaterm.metaterm -> unit

(* Interactive declarations *)
