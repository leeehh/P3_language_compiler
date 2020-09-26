open Format

let write_ast filepath ast_content =
  let ast_channel = open_out (filepath ^ ".ast") in
  fprintf (formatter_of_out_channel ast_channel) "%s\n" ast_content;
  close_out ast_channel
;;

let write_asm filepath asm_content =
  let asm_channel = open_out (filepath ^ ".asm") in
  fprintf (formatter_of_out_channel asm_channel) "%s\n" asm_content;
  close_out asm_channel
;;

let write_json filepath json_content =
  let json_channel = open_out (filepath ^ ".json") in
  fprintf (formatter_of_out_channel json_channel) "%s\n" json_content;
  close_out json_channel
;;