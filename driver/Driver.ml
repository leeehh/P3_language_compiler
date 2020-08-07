(**************************************
  Filename:  Driver.ml
  Project:   P3 Compilers
  Author:    Ling.Li
  Date:      2019.10.30
**************************************)

let generate_ast content =
  let rec inf = Parser.S inf in
  let lexbuf = Lexing.from_string content in
  let parsing_result = Parser.root inf (Lexer.token_stream lexbuf) in
  (
    match parsing_result with
    | Parser.Parser.Inter.Fail_pr ->
      print_string "[ERROR] Generate AST Failed!\n";
      exit (-2)
    | Parser.Parser.Inter.Timeout_pr ->
      print_string "[ERROR] Timed Out!\n";
      exit (-3)
    | Parser.Parser.Inter.Parsed_pr (output, _) ->
      let abstract_syntax_tree : Tree.program = Obj.magic output in
        abstract_syntax_tree
  )
;;

let generate_asm ast = 
  let result = AsmGen.program_to_asm ast in
  (
    match result with
    | Errors.OK asm -> 
      asm
    | Errors.Error msg -> 
      print_string "[ERROR] Generate ASM Failed!\n";
      exit (-4)
  )
;;

let print_error_code error_code =
  match error_code with
  | Errors.MSG msg -> print_string (Camlcoq.camlstring_of_coqstring msg)
  | Errors.CTX ctx -> print_string "CTX"
  | Errors.POS pos -> print_string "POS"
;;

let type_check ast =
  let result = Typing.typechecker ast in
  (
    match result with
    | Errors.OK p -> 
      p
    | Errors.Error error_code ->
      List.map print_error_code error_code;
      exit(-4)
  )
;;

let run_compiler filename =
  let source_code = Input.read_file filename in
  let ast = generate_ast source_code in
  let typed_ast = type_check ast in
  if !Option.flag_print_ast then 
    Output.write_ast (Filename.chop_extension filename) (AstWriter.ast_to_string typed_ast)
  else 
    ();
  let asm = generate_asm typed_ast in
  if !Option.flag_print_asm then 
    Output.write_asm (Filename.chop_extension filename) (AsmWriter.asm_to_string asm)
  else
    ();
;;

let app_main () =
  if (Array.length Sys.argv) = 1 then
    print_string Option.usage_info
  else
    Arg.parse (Arg.align Option.option_list) run_compiler Option.usage_info
  ;;

app_main();;
