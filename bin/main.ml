open Batteries
open Nap

module ArgParse = struct
  let usage =
    "Usage: main.exe [parse|compile|translate] filename [-verbose] [-o \
     out_file]"

  let verbose = ref false

  let atomize = ref false

  let in_file = ref ""

  let out_file = ref "out.p4"

  let command = ref ""

  let anon_fun str =
    if str = "parse" || str = "compile" || str = "translate" then
      if !command = "" then command := str
      else
        Console.error
          (Printf.sprintf "[CMD] Duplicate [parse|compile|translate] commands.")
    else if !in_file = "" then in_file := str
    else Console.error (Printf.sprintf "[CMD] Duplicate filenames.")

  let speclist =
    [ ("-verbose", Arg.Set verbose, "Enable verbose output.")
    ; ( "-atomize"
      , Arg.Set atomize
      , "Atomize tables for a more stable allocation." )
    ; ( "-o"
      , Arg.Set_string out_file
      , "Set output filename; default to ./out.p4." ) ]

  let parse_args () = Arg.parse speclist anon_fun usage
end

let main () =
  ArgParse.parse_args () ;
  match !ArgParse.command with
  | "parse" ->
      let ds = Input.parse_file !ArgParse.in_file in
      print_endline @@ Printing.decls_to_string ds
  | "compile" ->
      ignore
        (Input.compile_file !ArgParse.in_file !ArgParse.verbose
           !ArgParse.atomize )
  | "translate" ->
      ignore
        (Input.translate_file !ArgParse.in_file !ArgParse.out_file
           !ArgParse.verbose !ArgParse.atomize )
  | _ ->
      Console.error (Printf.sprintf "[CMD] Unrecognized command.")

let _ = main ()

(* let parse_command =
     let open Command.Spec in
     Command.basic_spec
       ~summary: "Parse a CtrlApp program"
       (empty
        +> flag "-v" no_arg ~doc:" Enable verbose output"
        +> anon ("file" %: string))
       (fun verbose file () -> ignore (parse_file file verbose))

   let compile_command =
     let open Command.Spec in
     Command.basic_spec
       ~summary: "Compile a CtrlApp program to P4"
       (empty
        +> flag "-v" no_arg ~doc:" Enable verbose output"
        +> anon ("file" %: string))
       (fun verbose file () -> ignore (compile_file file verbose))


   let command =
     Command.group
       ~summary: "CtrlApp: dataplane"
       [ "parse", parse_command;
         "compile", compile_command ]

   let () = Command.run ~version: "0.0.1" command *)
