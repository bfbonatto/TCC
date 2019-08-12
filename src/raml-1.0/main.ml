
let sys_time = Sys.time

open Core.Std

open Format

let raml_version = 1.0
let raml_release_date = "July 2015"
let raml_authors = ["Jan Hoffmann (Yale University)"
		   ;"Shu-Chun Weng (Yale University)"
		   ]
let raml_website = "http://raml.tcs.ifi.lmu.de"

let _ = Config.load_path := [""; !Rpath.ocaml_raml_runtime]

let print_welcome () =
  printf "\nResource Aware ML, Version %.2f, %s\n\n" raml_version raml_release_date

let sys_name = Sys.executable_name

let print_usage () =
  printf ("Usage:\n" ^^
          "  %s action [-m] [prog.raml]\n" ^^
          "\n" ^^
          "    prog.raml            Input file.\n" ^^
          "    -m                   Input file is a module instead of a program.\n" ^^
          "\n" ^^
          "  If the file name is absent, %s reads from the standard input.\n" ^^
          "\n" ^^
          "  Actions: \n" ^^
          "    eval cost            Evaluate the input program and print resource-usage\n" ^^
          "                         information for the built-in metrics.\n" ^^
          "\n" ^^
          "    eval                 Evaluate the input program. Print the return value and\n" ^^
          "                         resource-usage information for the built-in metrics.\n" ^^
          "\n" ^^
          "    analyze <metric> <deg> [-print (all | none | level <lev> )]\n" ^^
	  "                         analyze the input program and print bounds.\n" ^^
          "                         <metric>   Metric for the analysis. Built-in metrics\n" ^^
          "                                    are heap, steps, and ticks.\n" ^^
          "                         <deg>      Maximal degree of the candidate bounds.\n" ^^
          "                         -print     Print the types used in function applications.\n" ^^
          "                                    all          Print all.\n" ^^
          "                                    none         Print none.\n" ^^
          "                                    level <lev>  Print types withing depth <lev> in\n" ^^
          "                                                 the syntax tree.\n" ^^
          "\n" ^^
          "    usage                Print this message.\n" ^^
          "    version              Print version information.\n" ^^
          "    typecheck            Typecheck the input program.\n" ^^
          "    print simple[+t]     Print simplified syntax tree [with types].\n" ^^
          "    print sharelet[+t]   Print syntax tree in share-let-normal form [with types].\n" ^^
          "\n" ^^
          "  Example usage:\n" ^^
          "    %s analyze heap 4\n" ^^
          "    %s analyze steps 3 -print level 1 -m quicksort.raml\n@.")
          sys_name sys_name sys_name sys_name


let print_usage_error error_msg =
  printf (
    "%s\n" ^^
    "Run '%s usage' for usage information.\n@."
  ) error_msg sys_name


let print_info () =
  let rec print_authors authors pref =
    match authors with
      | [] -> ()
      | auth::auths -> 
	printf "%s%s\n" pref auth;
	print_authors auths pref
  in
  printf "Authors:\n";
  print_authors raml_authors "  ";
  printf (
    "Website:\n" ^^
    "  %s\n@."
  ) raml_website

  
let print_expression print_types form e =
  printf "%s:\n@." form
   ; Pprint.print_expression ~print_types e
   ; printf "\n@."


let print_module print_types form m =
  let fprint_raml_type f t = Pprint.fprint_raml_type f t
  in printf "%s:\n@." form
   ; List.iter m (fun (f, e) ->
         printf "===== %s : %a =====@."
           f fprint_raml_type e.Expressions.exp_type
       ; Pprint.print_expression ~print_types e
       ; printf "\n@.")


let tcheck_prog e env =
  printf "Typechecking expression ...\n"
  ; Typecheck.typecheck ~linear:false e env
  ; printf "  Typecheck successful.\n"
  ; ignore @@ Typecheck.typecheck_stack ~linear:false e env
  ; printf "  Stack-based typecheck successful.\n@."


let tcheck_module m env =
  printf "Typechecking module ...\n"
  ; let f (g,e) =
      Typecheck.typecheck ~linear:false e env
    in
    List.iter ~f m
  ; printf "  Typecheck successful.\n"
  ; let f (g,e) = 
      ignore @@ Typecheck.typecheck_stack ~linear:false e env
    in
    List.iter ~f m
  ; printf "  Stack-based typecheck successful.\n@."


let eval ?(cost_only=false) e =
    printf "Evaluating expression ...\n"
  ; let metrics = [Metric.m_eval; Metric.m_tick; Metric.m_heap] in
    let (result, costs) = Eval.evaluate e metrics in
    if cost_only then
      ()
    else begin
      printf "\n  Return value:\n    "
      ; match result with
        | Some loc_heap -> Pprint.print_value loc_heap
        | None -> printf "Exception (undefined)" 
    end;
    match costs with
    | [(eval1,_); (tick1,_); (heap1,_)] ->
      printf (
        "\n" ^^
	"  Evaluation steps: %.2f\n" ^^
        "  Ticks:            %.2f\n" ^^
        "  Heap space:       %.2f\n@."
      ) eval1 tick1 heap1 
    | _ -> Misc.fatal_error "This is dead code."

let print_data m_name degree time constr =
  printf (
    "\n" ^^
      "  Metric:        %s\n" ^^
      "  Degree:        %d\n" ^^
      "  Run time:      %.2f seconds\n" ^^
      "  #Constraints:  %d\n@."
  ) m_name degree time constr


let analyze_prog m_name metric degree collect_fun_types e env =
  let start_time = sys_time () in
  let () = tcheck_prog e env in
  let e_normal = Shareletnormal.share_let_normal "#" e in
  let e_normal_stack = Typecheck.typecheck_stack ~linear:true e_normal env in
  let () = printf "Analyzing expression ...\n" in
  let module Clp = Solver.Clp( Solver.Clp_std_options ) in
  let module Analysis = Analysis.Make( Clp ) in
  let () =
    match Analysis.analyze_expression e_normal_stack ~metric ~degree ~collect_fun_types with
      | None -> 
	printf "\n  No bound could be derived. The linear program is infeasible.\n"
      | Some (q, fun_type_list) ->
	let () = printf "\n  Function types:\n" in
	let print_fun_types atype =
          Pprint.print_anno_funtype ~indent:("  ") ~simple_name:true atype
        in 
	List.iter fun_type_list print_fun_types
        ; printf "\n==\n\n  Derived bound: %.2f\n" q
  in
  let constr = Clp.get_num_constraints () in
  let time = sys_time () -. start_time in
  print_data m_name degree time constr


let analyze_module m_name metric degree m env =

  let analyze_fun f_name e =
    let start_time = sys_time () in
    let e_normal = Shareletnormal.share_let_normal "#" e in
    let e_normal_stack = Typecheck.typecheck_stack ~linear:true e_normal env in
    let () = printf "Analyzing function %s ...\n" f_name in
    let module Clp = Solver.Clp( Solver.Clp_std_options ) in
    let module Analysis = Analysis.Make( Clp ) in
    let () =
      match Analysis.analyze_function e_normal_stack ~metric ~degree with
	| None -> 
	  printf "\n  A bound for %s could not be derived. The linear program is infeasible.\n" f_name
	| Some (atarg,atres) ->
            Pprint.print_anno_funtype ~indent:("  ") (f_name, atarg, atres)
    in
    let constr = Clp.get_num_constraints () in
    let time = sys_time () -. start_time in
    printf "--";
    print_data m_name degree time constr;
    printf "====\n\n"
  in

  let () = tcheck_module m env in
  let f (f_name,e) =
    match e.Expressions.exp_type with
      | Rtypes.Tarrow _ -> analyze_fun f_name e
      | _ -> ()
  in
  List.iter ~f m


let main argv = 
  let args = List.tl_exn (Array.to_list argv) in

  let main_cont args action_p action_m =
    match args with
      | [] -> 
	let buf = Lexing.from_channel stdin in
        let _ = Location.init buf "<stdin>" in
        let (e, env) = Parseraml.parse_raml buf in
        action_p e env
      | ["-m"]
      | ["-module"] ->
	print_usage_error "Expecting file name of the module."
      | [file] ->
	if Sys.file_exists file <> `Yes then
	  print_usage_error ("File '" ^ file ^ "' not found.")
	else 
	  let (e, env) = Parseraml.parse_raml_from_file file in
	  action_p e env
      | ["-m";file]
      | ["-module";file] ->
	if Sys.file_exists file <> `Yes then
	  print_usage_error ("File '" ^ file ^ "' not found.")
	else 
	  let (m, env) = Parseraml.parse_raml_module file in
	  action_m m env
      | _ ->
	let arg_string = 
	  let f str acc =
	    str ^ " " ^ acc
	  in
	  List.fold ~init:"" ~f args
	in
	print_usage_error ("Too many arguments: '"^ arg_string ^ "'.")
  in

  let () = print_welcome () in
  match args with
    | [] -> print_usage_error "Expecting an action to execute."
    | action::args ->
      match action with
	| "usage" ->print_usage ()
	| "info"
	| "version" -> print_info ()
	| "type-check"
	| "typecheck" ->
	  main_cont args tcheck_prog tcheck_module
	| "evaluate"
	| "eval" ->
	  let (cost_only,args) =
	    match args with
	      | "cost"::args' -> (true,args')
	      | _ -> (false,args)
	  in
	  let eval_p e env =
	    tcheck_prog e env;
	    eval ~cost_only e
	  in
	  let eval_m _ _ =
	    print_usage_error "Modules cannot be evaluated."
	  in
	  main_cont args eval_p eval_m
	| "analyse"
	| "analyze" -> begin
	  match args with
	    | m_name::deg::args ->
	      let metric =
		match m_name with
		  | "steps" -> Metric.m_eval
		  | "heap"  -> Metric.m_heap
		  | "ticks" -> Metric.m_tick
		  | _ -> 
		    print_usage_error ("The metric '" ^ m_name ^ "' is not a built-in metric.")
		    ; exit(-1)
	      in
	      let deg =
		try
		  let deg = Int.of_string deg in
		  if deg > 0 then
		    deg
		  else
		    raise (Invalid_argument "Negative number or zero.")
		with _ ->
		  print_usage_error  ("The degree '" ^ deg ^ "' is not a positive number.")
		  ; exit(-1)
	      in
	      let (pmode,args) =
		match args with
		  | "-print"::"all"::args ->
		    (Rconfig.Pall,args)
		  | "-print"::"none"::args ->
		    (Rconfig.Pnone,args)
		  | "-print"::"level"::lev::args -> begin
		    try
		      let lev = Int.of_string lev in
		      if lev >= 0 then
			(Rconfig.Plevel lev,args)
		      else
			raise (Invalid_argument "Negative number or zero.")
		    with _ ->
		      print_usage_error  ("The level '" ^ lev ^ "' is not a non-negative number.")
		      ; exit(-1) end
		  | "-print"::_ ->
		    print_usage_error "The usage for the print mode is '-print (all | none | level <lev> )'."
		    ; exit(-1)
		  | _ -> (Rconfig.Pnone,args)
	      in
	      let analyze_p = analyze_prog m_name metric deg pmode in
	      let analyze_m = analyze_module m_name metric deg in
	      main_cont args analyze_p analyze_m
	    | _ ->
	      print_usage_error 
		"The action analyze has to be followed by a metric and a degree."
	end
	| "print" -> begin
	  match args with
	    | ("simple" as a)::args
	    | ("simple+t" as a)::args ->
	      let with_types = 
		if String.is_suffix a "+t" then
		  true
		else
		  false
	      in
	      let p_print e _ =
		print_expression with_types "Simplified expression" e 
	      in
	      let m_print m _ = 
		print_module with_types "Simplified module" m
	      in
	      main_cont args p_print m_print 
	    | ("sharelet" as a)::args
	    | ("sharelet+t" as a)::args ->
	      let with_types =
		if String.is_suffix a "+t" then
		  true
		else
		  false
	      in
	      let p_print e env =
		let _ = Typecheck.typecheck ~linear:false e env in
		let e_normal = Shareletnormal.share_let_normal "#" e in
		print_expression with_types "Expression in share-let-normal form" e_normal
	      in
	      let m_print m env =
		let f (g,e) =
		  let _ = Typecheck.typecheck ~linear:false e env in
		  (g, Shareletnormal.share_let_normal "#" e)
		in
		let m_normal = List.map ~f m in
		print_module with_types "Module in share-let-normal form" m_normal
	      in
	      main_cont args p_print m_print 
	    | [] -> print_usage_error "The action 'print' needs an argument."
	    | a::args -> print_usage_error ("'"^a^"' is not a valid argument for the action 'print'.")
	end
	| _ -> print_usage_error ("'" ^ action ^ "' is not a valid action.")


let _ = main Sys.argv
