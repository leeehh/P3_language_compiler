open Format

let write_ast filepath ast_content =
  let channel = open_out (filepath ^ ".ast") in
  fprintf (formatter_of_out_channel channel) "%s\n" ast_content;
  close_out channel
;;
