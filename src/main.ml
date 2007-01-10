open Prover
open Pprint
open Lppterm

let rec process ?(interactive=true) lexbuf =
  try while true do try
    if interactive then Format.printf "LPP < %!" ;
    begin match Parser.command Lexer.token lexbuf with
      | Induction(args) -> induction args
      | Apply(h, args) -> apply h args
      | Case(str) -> case str
      | Search -> search ()
      | Theorem(thm) -> theorem thm
      | Intros -> intros ()
    end ;
    display () ;
    if interactive then flush stdout
  with
    | Failure "lexing: empty token" ->
        exit (if interactive then 0 else 1)
    | Failure s ->
        Format.printf "Error: %s\n" s
    | e ->
        Format.printf "Unknown error: %s\n%!" (Printexc.to_string e)
  done with
  | Failure "eof" -> ()
  

let welcome_msg = "Lambda Prolog Prover 0.1\n"

let usage_message = ""
  
let _ =
  Format.printf "%s%!" welcome_msg ;
  Arg.parse []
    (fun file_name ->
       Printf.printf "Reading clauses from %s\n" file_name ;
       clauses :=
         List.append (Parser.clauses Lexer.token
                        (Lexing.from_channel (open_in file_name)))
           !clauses)
    usage_message ;
  Pprint.set_infix [("=>", Pprint.Right)] ;
  process ~interactive:true (Lexing.from_channel stdin)











