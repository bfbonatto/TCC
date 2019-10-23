open Core.Std

open Format
open Rconfig

let ident_pervasive = Ident.create_persistent "Pervasives"

let get_initial_environment () =
  let file_name = Filename.concat !Rpath.ocaml_raml_runtime "pervasive.mli" in
  let ch = In_channel.create file_name in
  let buf = Lexing.from_channel ch in
  let _ = Location.init buf file_name in
  let parsetree = Parse.interface buf in
  let _ = In_channel.close ch in
  let typedtree = Typemod.transl_signature Env.initial parsetree in
  Env.open_signature Asttypes.Fresh (Path.Pident ident_pervasive)
                     typedtree.Typedtree.sig_type Env.initial

let parse_ocaml buf =
  try
    let parsetree = Parse.implementation buf in
    let env = get_initial_environment () in
    fst3 @@ Typemod.type_structure env parsetree (Location.curr buf)
  with Not_found -> Misc.fatal_error "Cannot open implicit module Pervasives"
     | e -> Errors.report_error std_formatter e
          ; if !print_stack_on_exn then printf "%s@," (Exn.backtrace ())
          ; Misc.fatal_error ""

let parse_ocaml_from_file file_name =
  let ch = In_channel.create file_name in
  let buf = Lexing.from_channel ch in
  let _ = Location.init buf file_name in
  let typed_expression = parse_ocaml buf in
  let _ = In_channel.close ch
  in typed_expression

let parse_ocaml_module file_name =
  let ch = In_channel.create file_name in
  let buf = Lexing.from_channel ch in
  let _ = Location.init buf file_name in
  let parsetree = Parse.implementation buf in
  let _ = In_channel.close ch in
  try
    let env = get_initial_environment () in
    let dummy_filename_prefix = Filename.concat Filename.temp_dir_name "cmt" in
    let module_name = String.capitalize @@ fst @@ Filename.split_extension @@
                      Filename.basename file_name in
    let _ = Clflags.dont_write_files := true
    in fst @@ Typemod.type_implementation
                file_name dummy_filename_prefix module_name
                env parsetree
  with Not_found -> printf "Cannot open implicit module Pervasives\n@?"
                  ; exit 1
     | e -> Errors.report_error std_formatter e
          ; if !print_stack_on_exn then printf "%s@," (Exn.backtrace ())
          ; exit 1

let fprint_raml_type f rty = Pprint.fprint_raml_type f rty

let ocaml_to_raml simplify typed_expression = try
  try let (e, env, cenv) = simplify typed_expression
      in Pprint.set_constr_map cenv; e, env
      with e -> Errors.report_error std_formatter e; exit 1
  with Simplify.Eunsupported_type (loc, t, reason) ->
       printf "Simplify: unsupported type at %a (%s):\n%a\n%s@?"
         Location.print_loc loc reason
         Printtyp.type_expr t
         (if !print_stack_on_exn then Exn.backtrace () else "")
     ; exit 2

     | Simplify.Eunsupported_pattern p ->
       printf "Simplify: unsupported pattern at %a:\n%a\n%s@?"
         Location.print_loc p.Typedtree.pat_loc
         Printtyped.pattern p
         (if !print_stack_on_exn then Exn.backtrace () else "")
     ; exit 2

     | Simplify.Eunsupported_constant (loc, c) ->
       printf "Simplify: unsupported constant at %a:\n%a\n%s@?"
         Location.print_loc loc
         Printast.constant c
         (if !print_stack_on_exn then Exn.backtrace () else "")
     ; exit 2

     | Simplify.Eunsupported_expr e ->
       printf "Simplify: unsupported expression at %a:\n%a\n%s@?"
         Location.print_loc e.Typedtree.exp_loc
         Printtyped.expression e
         (if !print_stack_on_exn then Exn.backtrace () else "")
     ; exit 2

     | Simplify.Eunsupported_primitive s ->
       printf "Simplify: unsupported built-in function: %s\n%s@?"
         s
         (if !print_stack_on_exn then Exn.backtrace () else "")
     ; exit 2

     | Simplify.Eno_main_expression ->
       printf "Simplify: last statement is not an executable expression\n%s@?"
         (if !print_stack_on_exn then Exn.backtrace () else "")
     ; exit 2

    | Simplify.Enot_an_instance (tbase, tinst) ->
      printf "Simplify: type `%a' is not an instance of `%a'@.%s@?"
        fprint_raml_type tinst
        fprint_raml_type tbase
        (if !print_stack_on_exn then Exn.backtrace () else "")
     ; exit 2

   | Simplify.Emonomorphic_var (name, t1, loc1, t2, loc2) ->
     printf ("Monomorphic variable `%s' used with different types:\n@." ^^
             "  %a at %a\n\nand\n@.  %a at %a\n@.%s@?") name
         fprint_raml_type t1 Location.print_loc loc1
         fprint_raml_type t2 Location.print_loc loc2
         (if !print_stack_on_exn then Exn.backtrace () else "")
     ; exit 2

   | e -> let backtrace = Exn.backtrace () in
          printf "Exception %s\n@?" (Exn.to_string e)
        ; if !print_stack_on_exn then printf "%s@," backtrace
        ; exit 2

let parse_raml buf = ocaml_to_raml Simplify.simplify_structure (parse_ocaml buf)
let parse_raml_from_file file_name =
      ocaml_to_raml Simplify.simplify_structure (parse_ocaml_from_file file_name)

let parse_raml_module file_name =
      ocaml_to_raml Simplify.simplify_module (parse_ocaml_from_file file_name)
