open Arg
open Version

let usage_info = "\
USAGE: p3c [options] <source.ppp>

options:
    -print-ast:    Print AST of source code
    -print-asm:    Print ASM of source code
    -print-json:   Print AST in JSON format
    -version:      Print P3C version and exit
    -help:         Print this list of options
";;

let flag_print_ast = ref false;;

let flag_print_asm = ref false;;

let flag_print_json = ref false;;

let option_list = [
  ( "-print-ast", Set flag_print_ast, "    Print AST of source code" );
  ( "-print-asm", Set flag_print_asm, "    Print ASM of source code" );
  ( "-print-json", Set flag_print_json, "    Print AST in JSON format" );
  ( "-version", Unit ( fun() -> ( print_string version_info ) ), "      Print P3C version and exit" );
  ( "-help", Unit ( fun() -> ( print_string usage_info ) ), "         Print this list of options" );
];;