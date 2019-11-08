(**************************************
  Filename: Lexer.mll
  Project:  P3 Compilers
  Author:   Ling.Li
  Date:     2018.06.20
**************************************)

{

open Lexing
open Parser
open String
open Aut.GramDefs
exception Eof

}

rule token = parse
(* keywords *)
  | "pset"
    { get_token PSET'token }
  | "lset"
    { get_token LSET'token }
  | "const"
    { get_token CONST'token }
  | "type"
    { get_token TYPE'token }
  | "register"
    { get_token REGISTER'token }
  | "protocol"
    { get_token PROTOCOL'token }
  | "int"
    { get_token INT'token }
  | "hexes"
    { get_token HEXADECIMAL'token }
  | "bits"
    { get_token BITS'token }
  | "not"
    { get_token NOT'token }
  | "set"
    { get_token INS_SET'token }
  | "mov"
    { get_token INS_MOV'token }
  | "eq"
    { get_token INS_EQ'token }
  | "lg"
    { get_token INS_LG'token }
  | "if"
    { get_token IF'token }
  | "else"
    { get_token ELSE'token }
  | "elseif"
    { get_token ELSEIF'token }
  | "endif"
    { get_token ENDIF'token }
  | "action"
    { get_token ACTION'token }
  | "next_header"
    { get_token NEXT_HEADER'token }
  | "length"
    { get_token LENGTH'token }
  | "fields"
    { get_token FIELDS'token }
  | "var"
    { get_token VAR'token }
  | "options"
    { get_token OPTIONS'token }
  | "bypass"
    { get_token BYPASS'token }
  | "cellA"
    { get_token CELLA'token }
  | "cellB0"
    { get_token CELLB0'token }
  | "cellB1"
    { get_token CELLB1'token }
  | "ARegisters"
    { get_token AREGISTERS'token }
  | "B0Registers"
    { get_token B0REGISTERS'token }
  | "B1Registers"
    { get_token B1REGISTERS'token }
  | "lreglen"
    { get_token LREGLEN'token }
  | "creglen"
    { get_token CREGLEN'token }
  | "bytes"
    { get_token BYTES'token }
  | "IRF"
    { get_token IRF'token }
(* parentheses *)
  | "{"
    { get_token LBRACE'token }
  | "}"
    { get_token RBRACE'token }
  | "["
    { get_token LBRACKET'token }
  | "]"
    { get_token RBRACKET'token }
  | "("
    { get_token LPAREN'token }
  | ")"
    { get_token RPAREN'token }
(* characters *)
  | ","
    { get_token COMMA'token }
  | ";"
    { get_token SEMICOLON'token }
  | ":"
    { get_token COLON'token }
  | "="
    { get_token EQ'token }
  | "."
    { get_token DOT'token }
(* operators *)
  | "~"
    { get_token TILDE'token }
  | "+"
    { get_token ADD'token }
  | "-"
    { get_token SUB'token }
  | "*"
    { get_token MUL'token }
  | "/"
    { get_token DIV'token }
  | "%"
    { get_token MOD'token }
  | "&&"
    { get_token ANDAND'token }
  | "||"
    { get_token OROR'token }
  | "&"
    { get_token AND'token }
  | "|"
    { get_token OR'token }
  | "^"
    { get_token XOR'token }
  | "=="
    { get_token EQEQ'token }
  | "<>"
    { get_token NE'token }
  | "<"
    { get_token LES'token }
  | ">"
    { get_token GRE'token }
  | "<="
    { get_token LESEQ'token }
  | ">="
    { get_token GREEQ'token }
  | "<<"
    { get_token LESLES'token }
  | ">>"
    { get_token GREGRE'token }
  | "++"
    { get_token ADDADD'token }
(* identifiers *)
  | ['a'-'z''A'-'Z''_']['a'-'z''A'-'Z''0'-'9''_''-']* as lxm  
    { get_token (IDENT'token lxm) }
  | ['0'-'9']+ as lxm  
    { get_token (CONST_INT'token lxm) }
  | "0"['x''X']['0'-'9' 'A'-'F' 'a'-'f']+ as lxm
    { get_token (CONST_HEX'token lxm) }
  | "'"['0''1']+"'" as lxm
    { get_token (CONST_BIT'token (String.sub lxm 1 (String.length lxm - 2))) }
(* end_of_file *)
  | eof
    { get_token EOF'token }
(* blanks *)
  | [' ' '\t' '\n' '\r']+
    { token lexbuf }
(* comments *)
  | "//"[^'\n']*
    { token lexbuf }
(* others *)
  | _ as lxm
    { print_string "Unexpected Token: "; print_char lxm; print_string "\n" ; token lexbuf }

{
  let token_stream lexbuf : token stream =
    let rec compute_token_stream () =
      let loop c_exist =
        Cons (c_exist, Lazy.from_fun compute_token_stream)
      in loop (token lexbuf)
    in Lazy.from_fun compute_token_stream
}