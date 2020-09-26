(**************************************
  Filename: Parser.vy
  Project:  P3 Compilers
  Author:   Ling.Li
  Date:     2018.06.20
**************************************)

%{

Require Import BinNums.
Require Import Tree.
Require Import String.
Require Import List.

Open Scope string_scope.

Parameter intern_string: String.string -> positive.
Parameter ocaml_string: String.string -> integer.

%}

(* keyword *)
%token PSET LSET CONST TYPE REGISTER PROTOCOL 
%token INT HEXADECIMAL BITS
%token NOT INS_SET INS_MOV INS_EQ INS_LG
%token IF ELSE ELSEIF ENDIF ACTION NEXT_HEADER LENGTH FIELDS VAR OPTIONS BYPASS
%token CELLA CELLB0 CELLB1 AREGISTERS B0REGISTERS B1REGISTERS LREGLEN CREGLEN BYTES IRF

(* parentheses *)
%token LBRACE RBRACE LBRACKET RBRACKET LPAREN RPAREN

(* characters *)
%token COMMA SEMICOLON COLON EQ DOT

(* operators *)
%token TILDE ADD SUB MUL DIV MOD ANDAND OROR AND OR XOR EQEQ NE LES GRE LESEQ GREEQ LESLES GREGRE ADDADD

(* identifiers *)
%token<string> IDENT CONST_INT CONST_HEX CONST_BIT

(* end_of_file *)
%token EOF

%type<protocol_set> protocol_set
%type<layer_register_length> layer_register_length
%type<cell_register_length> cell_register_length
%type<list identifier> id_list
%type<identifier> identifier
%type<layer_set> layer_set
%type<list declaration> declaration_list
%type<declaration> declaration
%type<constant_declaration> constant_declaration
%type<constant> constant
%type<protocol_declaration> protocol_declaration
%type<protocol> protocol
%type<fields> fields
%type<list field> field_list
%type<field> field
%type<optional_field> optional_field
%type<protocol_statement> protocol_statement
%type<list select_statement> select_statement_list
%type<select_statement> select_statement
%type<if_statement> if_statement
%type<if_branch> if_branch
%type<list if_branch> else_if_branch_list
%type<if_branch> else_if_branch
%type<else_branch> else_branch
%type<list statement> statement_list
%type<statement> statement
%type<action_statement> action_statement
%type<list instruction> instruction_list
%type<instruction> instruction
%type<target_register_access_name> target_register_access_name
%type<move_register_access_name> move_register_access_name
%type<list register_access_set> register_access_set_list
%type<register_access_set> register_access_set
%type<layer_action> layer_action
%type<list layer_declaration> layer_declaration_list
%type<layer_declaration> layer_declaration
%type<local_register_declaration> local_register_declaration
%type<cell_a_register> cell_a_register
%type<cell_b0_register> cell_b0_register
%type<cell_b1_register> cell_b1_register
%type<local_action> local_action
%type<cell_a_action> cell_a_action
%type<cell_b0_action> cell_b0_action
%type<cell_b1_action> cell_b1_action
%type<layer_statement> layer_statement

%type<expression> expression
%type<expression> logical_or_expression
%type<expression> logical_and_expression
%type<expression> bitwise_or_expression
%type<expression> bitwise_xor_expression
%type<expression> bitwise_and_expression
%type<expression> equality_expression
%type<expression> relational_expression
%type<expression> shift_expression
%type<expression> additive_expression
%type<expression> multiplicative_expression
%type<expression> concatenation_expression
%type<expression> cast_expression
%type<expression> unary_expression
%type<expression> postfix_expression
%type<expression> primary_expression

%start<program> root
%%

(* <parser_spec> *)
root:
  | v1 = layer_register_length; v2 = cell_register_length; v3 = protocol_set; v4 = layer_set; v5 = declaration_list; EOF
    { Program v1 v2 v3 v4 v5 }
  ;

(* <layer_reg_len> *)
layer_register_length:
  | LREGLEN; EQ; v1 = constant; BYTES; SEMICOLON
    { Layer_Register_Length v1 }
  ;

(* <cell_reg_len> *)
cell_register_length:
  | CREGLEN; EQ; v1 = constant; BYTES; SEMICOLON
    { Cell_Register_Length v1 }
  ;

(* <protocol_set> *)
protocol_set:
  | PSET; EQ; LBRACE; v1 = id_list; RBRACE; SEMICOLON
    { Protocol_Set v1 }
  ;

(* <layer_set> *)
layer_set:
  | LSET; EQ; LBRACE; v1 = id_list; RBRACE; SEMICOLON
    { Layer_Set v1 }
  ;

(* <id_list> *)
id_list:
  | v1 = identifier; COMMA; v2 = id_list
    { v1 :: v2 }
  | v1 = identifier
    { [ v1 ] }
  ;

(* <IDENT> *)
identifier:
  | v1 = IDENT
    { {| name := v1; key := intern_string v1 |} }
  ;

(* { <decl> } *)
declaration_list:
  | v1 = declaration; v2 = declaration_list
    { v1 :: v2 }
  | (* empty *)
    { [] }
  ;

(* <decl> *)
declaration:
  | v1 = constant_declaration
    { As_Constant v1 }
  | v1 = protocol_declaration
    { As_Protocol v1 }
  | v1 = register_access_set
    { As_Register_Access v1 }
  | v1 = layer_action
    { As_Layer v1 }
  ;

(* <const_decl> *)
constant_declaration:
  | CONST; v1 = identifier; EQ; v2 = constant; SEMICOLON
    { Constant_Declaration v1 v2 }
  ;

(* <const> *)
constant:
  | v1 = IDENT
    { Const_Identifier {| name := v1; key := intern_string v1 |} }
  | v1 = CONST_INT
    { Const_Int {| name := v1; key := xH |} }
  | v1 = CONST_HEX
    { Const_Hex {| name := v1; key := xH |} }
  | v1 = CONST_BIT
    { Const_Bit {| name := v1; key := xH |} }
  ;

(* <protocol_decl> *)
protocol_declaration:
  | PROTOCOL; v1 = identifier; LBRACE; v2 = protocol; RBRACE
    { Protocol_Declaration v1 v2 }
  ;

(* <protocol> *)
protocol:
  | v1 = fields; v2 = protocol_statement
    { Protocol v1 v2 }
  ;

(* <fields> *)
fields:
  | FIELDS; EQ; LBRACE; v1 = field_list; v2 = optional_field; RBRACE
    { Fields v1 v2 }
  ;

(* { <field> } *)
field_list:
  | v1 = field; v2 = field_list
    { v1 :: v2 }
  | (* empty *)
    { [] }
  ;

(* <field> *)
field:
  | v1 = identifier; COLON; v2 = constant; SEMICOLON
    { Field v1 v2 }
  ;

(* <option_field> *)
optional_field:
  | OPTIONS; COLON; MUL; SEMICOLON;
    { Optional_Field {| name := ocaml_string "options"; key := intern_string "options" |} ( Const_Int {| name := ocaml_string "0"; key := xH |} ) }
  | (* empty *)
    { No_Optional_Field }
  ;

(* <p_stmts> *)
protocol_statement:
  | v1 = select_statement_list
    { Protocol_Statement v1 }
  ;

(* { <select_stmt> } *)
select_statement_list:
  | v1 = select_statement; v2 = select_statement_list
    { v1 :: v2 }
  | (* empty *)
    { [] }
  ;

(* <select_stmt> *)
select_statement:
  | v1 = if_statement
    { As_If v1 }
  | v1 = statement
    { As_Simple v1 }
  ;

(* <if_else_stmt> *)
if_statement:
  | v1 = if_branch; v2 = else_if_branch_list; v3 = else_branch; ENDIF
    { If_Statement (v1 :: v2) v3 }
  ;

if_branch:
  | IF; LPAREN; v1 = expression; RPAREN; v2 = statement_list
    { If_Branch v1 v2 }
  ;

else_if_branch_list:
  | v1 = else_if_branch; v2 = else_if_branch_list
    { v1 :: v2 }
  | (* empty *)
    { [] }
  ;

else_if_branch:
  | ELSEIF; LPAREN; v1 = expression; RPAREN; v2 = statement_list
    { If_Branch v1 v2 }
  ;

else_branch:
  | ELSE; v1 = statement_list;
    { Else_Branch v1 }
  | (* empty *)
    { Else_Branch [] }
  ;

statement_list:
  | v1 = statement; v2 = statement_list
    { v1 :: v2 }
  | (* empty *)
    { [] }
  ;

statement:
  | BYPASS; EQ; v1 = constant; SEMICOLON
    { Bypass_Statement v1 }
  | NEXT_HEADER; EQ; v1 = identifier; SEMICOLON
    { Next_Header_Statement v1 }
  | LENGTH; EQ; v1 = expression; SEMICOLON
    { Length_Statement v1 }
  | v1 = action_statement
    { Action_Statement v1 }
  ;

(* <action_stmt> *)
action_statement:
  | ACTION; EQ; LBRACE; v1 = instruction_list; RBRACE
    { Act_Statement v1 }
  | v1 = instruction
    { Act_Statement [ v1 ] }
  ;

(* <instructions> *)
instruction_list:
  | v1 = instruction; v2 = instruction_list
    { v1 :: v2 }
  | (* empty *)
    { [] }
  ;

(* <instruction> *)
instruction:
  | INS_SET; v1 = target_register_access_name; COMMA; v2 = expression; SEMICOLON
    { Set_Instruction v1 v2 }
  | INS_MOV; v1 = move_register_access_name; COMMA; v2 = expression; SEMICOLON
    { Mov_Instruction v1 v2 }
  | INS_LG; v1 = target_register_access_name; COMMA; v2 = expression; COMMA; v3 = expression; SEMICOLON
    { Lg_Instruction v1 v2 v3 }
  | INS_EQ; v1 = target_register_access_name; COMMA; v2 = expression; COMMA; v3 = expression; SEMICOLON
    { Eq_Instruction v1 v2 v3 }
  ;

(* <tgt_reg_acc_name> *)
target_register_access_name:
  | v1 = identifier
    { Target_Register_Id v1 }
  | v1 = target_register_access_name; LBRACKET; v2 = expression; COLON; v3 = expression; RBRACKET
    { Target_Register_Section v1 v2 v3 }
  | v1 = target_register_access_name; LBRACKET; v2 = expression; RBRACKET
    { Target_Register_Bit v1 v2 }
  ;

(* <mov_reg_acc_name> *)
move_register_access_name:
  | v1 = target_register_access_name
    { Move_Register_Single v1 }
  | v1 = move_register_access_name; ADDADD; v2 = target_register_access_name
    { Move_Register_Double v1 v2 }
  ;

(* { <reg_acc_set> } *)
register_access_set_list:
  | v1 = register_access_set; v2 = register_access_set_list
    { v1 :: v2 }
  | (* empty *)
    { [] }
  ;

(* <reg_acc_set> *)
register_access_set:
  | v1 = identifier; EQ; IRF; LBRACKET; v2 = expression; COLON; v3 = expression; RBRACKET; SEMICOLON
    { Register_Access_Set_Section v1 v2 v3 }
  | v1 = identifier; EQ; IRF; LBRACKET; v2 = expression; RBRACKET; SEMICOLON
    { Register_Access_Set_Bit v1 v2 }
  ;

(* <layer_action> *)
layer_action:
  | v1 = identifier; LBRACE; v2 = local_register_declaration; v3 = layer_declaration_list; v4 = local_action; RBRACE
    { Layer_Action v1 v2 v3 v4 }
  ;

(* <local_reg_decl> *)
local_register_declaration:
  | v1 = cell_a_register; v2 = cell_b0_register; v3 = cell_b1_register
    { Local_Register_Declaration v1 v2 v3 }
  ;

(* <cella_regs> *)
cell_a_register:
  | AREGISTERS; LBRACE; v1 = register_access_set_list; RBRACE
    { Cell_A_Register v1 }
  | (* empty *)
    { Cell_A_Register [] }
  ;

(* <cellb0_regs> *)
cell_b0_register:
  | B0REGISTERS; LBRACE; v1 = register_access_set_list; RBRACE
    { Cell_B0_Register v1 }
  | (* empty *)
    { Cell_B0_Register [] }
  ;

(* <cellb1_regs> *)
cell_b1_register:
  | B1REGISTERS; LBRACE; v1 = register_access_set_list; RBRACE
    { Cell_B1_Register v1 }
  | (* empty *)
    { Cell_B1_Register [] }
  ;

(* <l_decls> *)
layer_declaration_list:
  | v1 = layer_declaration; v2 = layer_declaration_list
    { v1 :: v2 }
  | (* empty *)
    { [] }
  ;

(* <l_decl> *)
layer_declaration:
  | v1 = identifier; v2 = id_list; SEMICOLON
    { Layer_As_Protocol v1 v2 }
  ;

(* <l_actions> *)
local_action:
  | v1 = cell_a_action; v2 = cell_b0_action; v3 = cell_b1_action
    { Local_Action v1 v2 v3 }
  ;

(* <cella_actions> *)
cell_a_action:
  | CELLA; LBRACE; v1 = layer_statement; RBRACE
    { Cell_A_Action v1 }
  | (* empty *)
    { Cell_A_Action (Layer_Statement []) }
  ;

(* <cellb0_actions> *)
cell_b0_action:
  | CELLB0; LBRACE; v1 = layer_statement; RBRACE
    { Cell_B0_Action v1 }
  | (* empty *)
    { Cell_B0_Action (Layer_Statement []) }
  ;

(* <cellb1_actions> *)
cell_b1_action:
  | CELLB1; LBRACE; v1 = layer_statement; RBRACE
    { Cell_B1_Action v1 }
  | (* empty *)
    { Cell_B1_Action (Layer_Statement []) }
  ;

(* <l_stmts> *)
layer_statement:
  | v1 = select_statement_list
    { Layer_Statement v1 }
  ;

/// Expression Part ///

expression:
  | v1 = logical_or_expression
    { v1 }
  ;

logical_or_expression:
  | v1 = logical_and_expression
    { v1 }
  | v1 = logical_or_expression; OROR; v2 = logical_and_expression
    { Binary_Expression Binary_OrOr v1 v2 }
  ;

logical_and_expression:
  | v1 = bitwise_or_expression
    { v1 }
  | v1 = logical_and_expression; ANDAND; v2 = bitwise_or_expression
    { Binary_Expression Binary_AndAnd v1 v2 }
  ;

bitwise_or_expression:
  | v1 = bitwise_xor_expression
    { v1 }
  | v1 = bitwise_or_expression; OR; v2 = bitwise_xor_expression
    { Binary_Expression Binary_Or v1 v2 }
  ;

bitwise_xor_expression:
  | v1 = bitwise_and_expression
    { v1 }
  | v1 = bitwise_xor_expression; XOR; v2 = bitwise_and_expression
    { Binary_Expression Binary_Xor v1 v2 }
  ;

bitwise_and_expression:
  | v1 = equality_expression
    { v1 }
  | v1 = bitwise_and_expression; AND; v2 = equality_expression
    { Binary_Expression Binary_And v1 v2 }
  ;

equality_expression:
  | v1 = relational_expression
    { v1 }
  | v1 = equality_expression; EQEQ; v2 = relational_expression
    { Binary_Expression Binary_EqEq v1 v2 }
  | v1 = equality_expression; NE; v2 = relational_expression
    { Binary_Expression Binary_Neq v1 v2 }
  ;

relational_expression:
  | v1 = shift_expression
    { v1 }
  | v1 = relational_expression; GRE; v2 = shift_expression
    { Binary_Expression Binary_Gre v1 v2 }
  | v1 = relational_expression; LES; v2 = shift_expression
    { Binary_Expression Binary_Les v1 v2 }
  | v1 = relational_expression; GREEQ; v2 = shift_expression
    { Binary_Expression Binary_GreEq v1 v2 }
  | v1 = relational_expression; LESEQ; v2 = shift_expression
    { Binary_Expression Binary_LesEq v1 v2 }
  ;

shift_expression:
  | v1 = additive_expression
    { v1 }
  | v1 = shift_expression; LESLES; v2 = additive_expression
    { Binary_Expression Binary_LesLes v1 v2 }
  | v1 = shift_expression; GREGRE; v2 = additive_expression
    { Binary_Expression Binary_GreGre v1 v2 }
  ;

additive_expression:
  | v1 = multiplicative_expression
    { v1 }
  | v1 = additive_expression; ADD; v2 = multiplicative_expression
    { Binary_Expression Binary_Add v1 v2 }
  | v1 = additive_expression; SUB; v2 = multiplicative_expression
    { Binary_Expression Binary_Sub v1 v2 }
  ;

multiplicative_expression:
  | v1 = concatenation_expression
    { v1 }
  | v1 = multiplicative_expression; MUL; v2 = concatenation_expression
    { Binary_Expression Binary_Mul v1 v2 }
  | v1 = multiplicative_expression; DIV; v2 = concatenation_expression
    { Binary_Expression Binary_Div v1 v2 }
  | v1 = multiplicative_expression; MOD; v2 = concatenation_expression
    { Binary_Expression Binary_Mod v1 v2 }
  ;

concatenation_expression:
  | v1 = cast_expression
    { v1 }
  | v1 = concatenation_expression; ADDADD; v2 = cast_expression
    { Binary_Expression Binary_AddAdd v1 v2 }

cast_expression:
  | v1 = unary_expression
    { v1 }
  | v1 = cast_expression; HEXADECIMAL; v2 = unary_expression
    { Binary_Expression Binary_Hex v1 v2 }
  | v1 = cast_expression; BITS; v2 = unary_expression
    { Binary_Expression Binary_Bit v1 v2 }
  ;

unary_expression:
  | v1 = postfix_expression
    { v1 }
  | TILDE; v1 = unary_expression
    { Unary_Expression  Unary_Tilde v1 }
  | NOT; v1 = unary_expression
    { Unary_Expression Unary_Not v1 }
  | INT; v1 = unary_expression
    { Unary_Expression Unary_Int v1 }
  ;

postfix_expression:
  | v1 = primary_expression
    { v1 }
  | v1 = postfix_expression; DOT; v2 = identifier
    { Field_Expression v1 v2 }
  | v1 = postfix_expression; LBRACKET; v2 = expression; RBRACKET
    { Bit_Expression v1 v2 }
  | v1 = postfix_expression; LBRACKET; v2 = expression; COLON; v3 = expression; RBRACKET
    { Section_Expression v1 v2 v3 }
  ;

primary_expression:
  | v1 = constant
    { Constant_Expression v1 }
  | LENGTH; LPAREN; v1 = identifier; RPAREN
    { Length_Expression v1 }
  | LPAREN; v1 = expression; RPAREN
    { Parentheses_Expression v1 }
  ;
