open Arg
open Version

let usage_info = "\
USAGE: p3c [options] <source.ppp>

options:
    -version:      Print P3C version and exit
    -help:         Print this list of options

";;

let flag_print_ast = ref false;;

let option_list = [
  ( "-print-ast", Set flag_print_ast, "Print AST of source code" );
  ( "-version", Unit ( fun() -> ( print_string version_info ) ), "Print P3C version and exit" );
  ( "-help", Unit ( fun() -> ( print_string usage_info ) ), "Print this list of options" );
];;