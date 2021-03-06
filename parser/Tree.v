(**************************************
  Filename: Tree.v
  Project:  P3 Compiler
  Author:   Ling.Li
  Date:     2019.06.20
**************************************)

Require Import BinNums.
Require Import Coqlib.
Require Import String.

Definition str := string.
Definition integer := str.

Record identifier := {
  name : str;
  key : positive
}.

(* <parser_spec> *)
Inductive program :=
  | Program : layer_register_length -> cell_register_length -> protocol_set -> layer_set -> list declaration -> program

(* <layer_reg_len> *)
with layer_register_length :=
  | Layer_Register_Length : constant -> layer_register_length

(* <cell_reg_len> *)
with cell_register_length :=
  | Cell_Register_Length : constant -> cell_register_length

(* <protocol_set> *)
with protocol_set :=
  | Protocol_Set : list identifier -> protocol_set

(* <layer_set> *)
with layer_set :=
  | Layer_Set : list identifier -> layer_set

(* <decl> *)
with declaration :=
  | As_Constant : constant_declaration -> declaration
  | As_Protocol : protocol_declaration -> declaration
  | As_Register_Access : register_access_set -> declaration
  | As_Layer : layer_action -> declaration

(* <const_decl> *)
with constant_declaration :=
  | Constant_Declaration : identifier -> constant -> constant_declaration

(* <const> *)
with constant :=
  | Const_Identifier : identifier -> constant
  | Const_Int : identifier -> constant
  | Const_Hex : identifier -> constant
  | Const_Bit : identifier -> constant

(* <protocol_decl> *)
with protocol_declaration :=
  | Protocol_Declaration : identifier -> protocol -> protocol_declaration

(* <protocol> *)
with protocol :=
  | Protocol : fields -> protocol_statement -> protocol

(* <fields> *)
with fields :=
  | Fields : list field -> optional_field -> fields

(* <field> *)
with field :=
  | Field : identifier -> constant -> field

(* <option_field> *)
with optional_field :=
  | Optional_Field : identifier -> constant -> optional_field
  | No_Optional_Field : optional_field

(* <p_stmts> *)
with protocol_statement :=
  | Protocol_Statement : list select_statement -> protocol_statement


(* <if_else_stmt> *)
with select_statement :=
  | As_If : if_statement -> select_statement
  | As_Simple : statement -> select_statement

(* <if_else_stmt> *)
with if_statement :=
  | If_Statement : list if_branch -> else_branch -> if_statement

(* <if_branch> *)
with if_branch :=
  | If_Branch : expression -> list statement -> if_branch

(* <else_branch> *)
with else_branch :=
  | Else_Branch : list statement -> else_branch

(* <stmt> *)
with statement :=
  | Next_Header_Statement : identifier -> statement
  | Length_Statement : expression -> statement
  | Bypass_Statement : constant -> statement
  | Action_Statement : action_statement -> statement

(* <action_stmt> *)
with action_statement :=
  | Act_Statement : list instruction -> action_statement

(* <instruction> *)
with instruction :=
  | Set_Instruction : target_register_access_name -> expression -> instruction
  | Mov_Instruction : move_register_access_name -> expression -> instruction
  | Lg_Instruction : target_register_access_name -> expression -> expression -> instruction
  | Eq_Instruction : target_register_access_name -> expression -> expression -> instruction

(* <reg_acc_set> *)
with register_access_set :=
  | Register_Access_Set_Section : identifier -> expression -> expression -> register_access_set
  | Register_Access_Set_Bit : identifier -> expression -> register_access_set

(* <tgt_reg_acc_name> *)
with target_register_access_name :=
  | Target_Register_Id : identifier -> target_register_access_name
  | Target_Register_Section : target_register_access_name -> expression -> expression -> target_register_access_name
  | Target_Register_Bit : target_register_access_name -> expression -> target_register_access_name

(* <move_reg_acc_name> *)
with move_register_access_name :=
  | Move_Register_Single : target_register_access_name -> move_register_access_name
  | Move_Register_Double : move_register_access_name -> target_register_access_name -> move_register_access_name

(* <layer_action> *)
with layer_action :=
  | Layer_Action : identifier -> local_register_declaration -> list layer_declaration -> local_action -> layer_action

(* <l_decl> *)
with layer_declaration :=
  | Layer_As_Protocol : identifier -> list identifier -> layer_declaration

(* <local_reg_decl> *)
with local_register_declaration :=
  | Local_Register_Declaration : cell_a_register -> cell_b0_register -> cell_b1_register -> local_register_declaration

(* <cella_regs> *)
with cell_a_register :=
  | Cell_A_Register : list register_access_set -> cell_a_register

(* <cellb0_regs> *)
with cell_b0_register :=
  | Cell_B0_Register : list register_access_set -> cell_b0_register

(* <cellb1_regs> *)
with cell_b1_register :=
  | Cell_B1_Register : list register_access_set -> cell_b1_register

(* <l_actions> *)
with local_action :=
  | Local_Action : cell_a_action -> cell_b0_action -> cell_b1_action -> local_action

(* <cella_actions> *)
with cell_a_action :=
  | Cell_A_Action : layer_statement -> cell_a_action

(* <cellb_actions> *)
with cell_b0_action :=
  | Cell_B0_Action : layer_statement -> cell_b0_action

(* <cellb1_actions> *)
with cell_b1_action :=
  | Cell_B1_Action : layer_statement -> cell_b1_action

(* <l_stmts> *)
with layer_statement :=
  | Layer_Statement : list select_statement -> layer_statement

(* <unop> *)
with unary_operator :=
  | Unary_Int : unary_operator
  | Unary_Not : unary_operator
  | Unary_Tilde : unary_operator 

(* <binop> *)
with binary_operator :=
  | Binary_Add : binary_operator
  | Binary_Sub : binary_operator
  | Binary_Mul : binary_operator
  | Binary_Div : binary_operator
  | Binary_Mod : binary_operator
  | Binary_AndAnd : binary_operator
  | Binary_OrOr : binary_operator
  | Binary_And : binary_operator
  | Binary_Or : binary_operator
  | Binary_Xor : binary_operator
  | Binary_EqEq : binary_operator
  | Binary_Neq : binary_operator
  | Binary_Les : binary_operator
  | Binary_Gre : binary_operator
  | Binary_LesEq : binary_operator
  | Binary_GreEq : binary_operator
  | Binary_LesLes : binary_operator
  | Binary_GreGre : binary_operator
  | Binary_AddAdd : binary_operator
  | Binary_Hex : binary_operator
  | Binary_Bit : binary_operator

(* <expr> *)
with expression :=
  | Constant_Expression : constant -> expression
  | Unary_Expression : unary_operator -> expression -> expression
  | Binary_Expression : binary_operator -> expression -> expression -> expression
  | Field_Expression : expression -> identifier -> expression
  | Bit_Expression : expression -> expression -> expression
  | Section_Expression : expression -> expression -> expression -> expression
  | Length_Expression : identifier -> expression
  | Parentheses_Expression : expression -> expression
  .
