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
      print_string "Parsing Failed!\n";
      exit (-2)
    | Parser.Parser.Inter.Timeout_pr ->
      print_string "Timed Out!\n";
      exit (-3)
    | Parser.Parser.Inter.Parsed_pr (output, _) ->
      let abstract_syntax_tree : Tree.program = Obj.magic output in
        abstract_syntax_tree
  )
;;

let run_compiler filename =
  let source_code = Input.read_file filename in
  let ast = generate_ast source_code in
  if !Option.flag_print_ast then 
    Output.write_ast (Filename.chop_extension filename) (AstWriter.ast_to_string ast)
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