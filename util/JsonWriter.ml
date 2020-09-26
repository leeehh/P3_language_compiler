(**************************************
  Filename: JsonWriter.ml
  Project:  P3 Compilers
  Author:   Ling.Li
  Date:     2018.06.21
**************************************)

open Tree

let rec bin2int i = match i with
  | BinNums.Coq_xI p -> let n = bin2int p in n + n + 1
  | BinNums.Coq_xO p -> let n = bin2int p in n + n
  | BinNums.Coq_xH -> 1

let bin2string i = string_of_int (bin2int i)

let indent depth str = Printf.sprintf "%s%s" (String.make (depth * 4) ' ') str

let put_tag depth key value = indent depth (Printf.sprintf "\"%s\": \"%s\"," key value)

let put_node depth name children =
  String.concat "\n" [
    indent depth "{";
    put_tag (depth + 1) "name" name;
    indent (depth + 1) "\"children\": [";
    children;
    indent (depth + 1) "]";
    indent depth "}";
  ]

let put_id depth name id key =
  String.concat "\n" [
    indent depth "{";
    put_tag (depth + 1) "name" name;
    put_tag (depth + 1) "id" id;
    put_tag (depth + 1) "key" key;
    indent (depth + 1) "\"children\": []";
    indent depth "}";
  ]

let put_op depth name op =
  String.concat "\n" [
    indent depth "{";
    put_tag (depth + 1) "name" name;
    put_tag (depth + 1) "op" op;
    indent (depth + 1) "\"children\": []";
    indent depth "}";
  ]

let rec print_parser depth node = match node with
  | Program (v1, v2, v3, v4, v5) ->
    let child = String.concat ",\n" [
      print_layer_register_length (depth + 2) v1;
      print_cell_register_length (depth + 2) v2;
      print_protocol_set (depth + 2) v3;
      print_layer_set (depth + 2) v4;
      print_declaration_list (depth + 2) v5;
    ] in put_node depth "program" child

and print_layer_register_length depth node = match node with
  | Layer_Register_Length v1 ->
    let child = String.concat ",\n" [
      print_constant (depth + 2) v1;
    ] in put_node depth "layer_reg_len" child

and print_cell_register_length depth node = match node with
  | Cell_Register_Length v1 ->
    let child = String.concat ",\n" [
      print_constant (depth + 2) v1;
    ] in put_node depth "cell_reg_len" child

and print_constant depth node = match node with
  | Const_Identifier v1 ->
    let child = String.concat ",\n" [
      print_identifier (depth + 2) v1;
    ] in put_node depth "const_id" child
  | Const_Int v1 ->
    let child = String.concat ",\n" [
      print_integer (depth + 2) v1;
    ] in put_node depth "const_int" child
  | Const_Hex v1 ->
    let child = String.concat ",\n" [
      print_hexadecimal (depth + 2) v1;
    ] in put_node depth "const_hex" child
  | Const_Bit v1 ->
    let child = String.concat ",\n" [
      print_bit (depth + 2) v1;
    ] in put_node depth "const_bit" child

and print_identifier depth node = 
  put_id depth "identifier" node.name (bin2string node.key)

and print_integer depth node =
  put_id depth "identifier" node.name (bin2string node.key)

and print_hexadecimal depth node =
  put_id depth "identifier" node.name (bin2string node.key)

and print_bit depth node =
  put_id depth "identifier" node.name (bin2string node.key)

and print_id_list depth node =
  let child = String.concat ",\n" (List.map (print_identifier (depth + 2)) node)
    in put_node depth "id_list" child
  
and print_protocol_set depth node = match node with
  | Protocol_Set v1 ->
    let child = String.concat ",\n" [
      print_id_list (depth + 2) v1;
    ] in put_node depth "protocol_set" child

and print_layer_set depth node = match node with
  | Layer_Set v1 ->
    let child = String.concat "\n" [
      print_id_list (depth + 2) v1;
    ] in put_node depth "layer_set" child

and print_declaration_list depth node =
  let child = String.concat ",\n" (List.map (print_declaration (depth + 2)) node) 
    in put_node depth "declaration_list" child

and print_declaration depth node = match node with
  | As_Constant v1 ->
    let child = String.concat ",\n" [
      print_constant_declaration (depth + 2) v1;
    ] in put_node depth "decl" child
  | As_Protocol v1 ->
    let child = String.concat ",\n" [
      print_protocol_declaration (depth + 2) v1;
    ] in put_node depth "decl" child
  | As_Register_Access v1 ->
    let child = String.concat ",\n" [
      print_register_access_set (depth + 2) v1;
    ] in put_node depth "decl" child
  | As_Layer v1 ->
    let child = String.concat ",\n" [
      print_layer_action (depth + 2) v1;
    ] in put_node depth "decl" child

and print_constant_declaration depth node = match node with
  | Constant_Declaration (v1, v2) ->
    let child = String.concat ",\n" [
      print_identifier (depth + 2) v1;
      print_constant (depth + 2) v2;
    ] in put_node depth "const_decl" child

and print_protocol_declaration depth node = match node with
  | Protocol_Declaration (v1, v2) ->
    let child = String.concat ",\n" [
      print_identifier (depth + 2) v1;
      print_protocol (depth + 2) v2;
    ] in put_node depth "protocol_decl" child

and print_protocol depth node = match node with
  | Protocol (v1, v2) ->
    let child = String.concat ",\n" [
      print_fields (depth + 2) v1;
      print_protocol_statement (depth + 2) v2;
    ] in put_node depth "protocol" child

and print_fields depth node = match node with
  | Fields (v1, v2) ->
    let child = String.concat ",\n" [
      print_field_list (depth + 2) v1;
      print_optional_field (depth + 2) v2;
    ] in put_node depth "fields" child

and print_field_list depth node =
  let child = String.concat ",\n" (List.map (print_field (depth + 2)) node)
    in put_node depth "field_list" child
  
and print_field depth node = match node with
  | Field (v1, v2) ->
    let child = String.concat ",\n" [
      print_identifier (depth + 2) v1;
      print_constant (depth + 2) v2;
    ] in put_node depth "field" child

and print_optional_field depth node = match node with
  | Optional_Field (v1, v2) ->
    let child = String.concat ",\n" [
      print_identifier (depth + 2) v1;
      print_constant (depth + 2) v2;
    ] in put_node depth "option_field" child
  | No_Optional_Field ->
    put_node depth "no_option_field" ""

and print_protocol_statement depth node = match node with
  | Protocol_Statement v1 ->
    let child = String.concat ",\n" [
      print_select_statement_list (depth + 2) v1;
    ] in put_node depth "protocol_stmt" child

and print_select_statement_list depth node =
  let child = String.concat ",\n" (List.map (print_select_statement (depth + 2)) node)
    in put_node depth "select_stmt_list" child
  
and print_select_statement depth node = match node with
  | As_If v1 ->
    let child = String.concat ",\n" [
      print_if_statement (depth + 2) v1;
    ] in put_node depth "select_if" child
  | As_Simple v1 ->
    let child = String.concat ",\n" [
      print_statement (depth + 2) v1;
    ] in put_node depth "select_simple" child

and print_if_statement depth node = match node with
  | If_Statement (v1, v2) ->
    let child = String.concat ",\n" [
      print_if_branch_list (depth + 2) v1;
      print_else_branch (depth + 2) v2;
    ] in put_node depth "if_stmt" child

and print_if_branch_list depth node =
  let child = String.concat ",\n" (List.map (print_if_branch (depth + 2)) node)
    in put_node depth "if_branch_list" child

and print_if_branch depth node = match node with
  | If_Branch (v1, v2) ->
    let child = String.concat ",\n" [
      print_expression (depth + 2) v1;
      print_statement_list (depth + 2) v2;
    ] in put_node depth "if_branch" child

and print_else_branch depth node = match node with
  | Else_Branch v1 ->
    let child = String.concat ",\n" [
      print_statement_list (depth + 2) v1;
    ] in put_node depth "else_branch" child

and print_statement_list depth node =
  let child = String.concat ",\n" (List.map (print_statement (depth + 2)) node)
    in put_node depth "statement_list" child

and print_statement depth node = match node with
  | Next_Header_Statement v1 ->
    let child = String.concat ",\n" [
      print_identifier (depth + 2) v1;
    ] in put_node depth "header_stmt" child
  | Length_Statement v1 ->
    let child = String.concat ",\n" [
      print_expression (depth + 2) v1;
    ] in put_node depth "length_stmt" child
  | Bypass_Statement v1 ->
    let child = String.concat ",\n" [
      print_constant (depth + 2) v1;
    ] in put_node depth "bypass_stmt" child
  | Action_Statement v1 ->
    let child = String.concat ",\n" [
      print_action_statement (depth + 2) v1;
    ] in put_node depth "action_stmt" child

and print_action_statement depth node = match node with
  | Act_Statement v1 ->
    let child = String.concat ",\n" [
      print_instruction_list (depth + 2) v1;
    ] in put_node depth "action" child

and print_instruction_list depth node = 
    let child = String.concat ",\n" (List.map (print_instruction (depth + 2)) node)
      in put_node depth "instruction_list" child

and print_instruction depth node = match node with
  | Set_Instruction (v1, v2) ->
    let child = String.concat ",\n" [
      print_target_register_access_name (depth + 2) v1;
      print_expression (depth + 2) v2;
    ] in put_node depth "set_instruction" child
  | Mov_Instruction (v1, v2) ->
    let child = String.concat ",\n" [
      print_move_register_access_name (depth + 2) v1;
      print_expression (depth + 2) v2;
    ] in put_node depth "mov_instruction" child
  | Lg_Instruction (v1, v2, v3) ->
    let child = String.concat ",\n" [
      print_target_register_access_name (depth + 2) v1;
      print_expression (depth + 2) v2;
      print_expression (depth + 2) v3;
    ] in put_node depth "lg_instruction" child
  | Eq_Instruction (v1, v2, v3) ->
    let child = String.concat ",\n" [
      print_target_register_access_name (depth + 2) v1;
      print_expression (depth + 2) v2;
      print_expression (depth + 2) v3;
    ] in put_node depth "eq_instruction" child

and print_register_access_set_list depth node =
  let child = String.concat ",\n" (List.map (print_register_access_set (depth + 2)) node)
    in put_node depth "reg_acc_set_list" child

and print_register_access_set depth node = match node with
  | Register_Access_Set_Section (v1, v2, v3) ->
    let child = String.concat ",\n" [
      print_register_access_name (depth + 2) v1;
      print_expression (depth + 2) v2;
      print_expression (depth + 2) v3;
    ] in put_node depth "reg_acc_set_section" child
  | Register_Access_Set_Bit (v1, v2) ->
    let child = String.concat ",\n" [
      print_register_access_name (depth + 2) v1;
      print_expression (depth + 2) v2;
    ] in put_node depth "reg_acc_set_bit" child

and print_register_access_name depth node =
  let child = String.concat ",\n" [
    print_identifier (depth + 2) node
  ] in put_node depth "reg_acc_name" child

and print_target_register_access_name depth node = match node with
  | Target_Register_Id v1 ->
    let child = String.concat ",\n" [
      print_identifier (depth + 2) v1;
    ] in put_node depth "tgt_reg_acc_id" child
  | Target_Register_Section (v1, v2, v3) ->
    let child = String.concat ",\n" [
      print_target_register_access_name (depth + 2) v1;
      print_expression (depth + 2) v2;
      print_expression (depth + 2) v3;
    ] in put_node depth "tgt_reg_acc_section" child
  | Target_Register_Bit (v1, v2) ->
    let child = String.concat ",\n" [
      print_target_register_access_name (depth + 2) v1;
      print_expression (depth + 2) v2;
    ] in put_node depth "tgt_reg_acc_bit" child

and print_move_register_access_name depth node = match node with
  | Move_Register_Single v1 ->
    let child = String.concat ",\n" [
      print_target_register_access_name (depth + 2) v1;
    ] in put_node depth "mov_reg_acc_single" child
  | Move_Register_Double (v1, v2) ->
    let child = String.concat ",\n" [
      print_move_register_access_name (depth + 2) v1;
      print_target_register_access_name (depth + 2) v2;
    ] in put_node depth "mov_reg_acc_double" child

and print_layer_action depth node = match node with
  | Layer_Action (v1, v2, v3, v4) ->
    let child = String.concat ",\n" [
      print_identifier (depth + 2) v1;
      print_local_register_declaration (depth + 2) v2;
      print_layer_declaration_list (depth + 2) v3;
      print_local_action (depth + 2) v4;
    ] in put_node depth "layer_action" child

and print_layer_declaration_list depth node =
  let child = String.concat ",\n" (List.map (print_layer_declaration (depth + 2)) node)
    in put_node depth "layer_decl_list" child

and print_layer_declaration depth node = match node with
  | Layer_As_Protocol (v1, v2) ->
    let child = String.concat ",\n" [
      print_identifier (depth + 2) v1;
      print_id_list (depth + 2) v2;
    ] in put_node depth "l_decl" child

and print_local_register_declaration depth node = match node with
  | Local_Register_Declaration (v1, v2, v3) ->
    let child = String.concat ",\n" [
      print_cell_a_register (depth + 2) v1;
      print_cell_b0_register (depth + 2) v2;
      print_cell_b1_register (depth + 2) v3;
    ] in put_node depth "local_reg_decl" child

and print_cell_a_register depth node = match node with
  | Cell_A_Register v1 ->
    let child = String.concat ",\n" [
      print_register_access_set_list (depth + 2) v1;
    ] in put_node depth "cella_regs" child

and print_cell_b0_register depth node = match node with
  | Cell_B0_Register v1 ->
    let child = String.concat ",\n" [
      print_register_access_set_list (depth + 2) v1;
    ] in put_node depth "cellb0_regs" child

and print_cell_b1_register depth node = match node with
  | Cell_B1_Register v1 ->
    let child = String.concat ",\n" [
      print_register_access_set_list (depth + 2) v1;
    ] in put_node depth "cellb1_regs" child

and print_local_action depth node = match node with
  | Local_Action (v1, v2, v3) ->
    let child = String.concat ",\n" [
      print_cell_a_action (depth + 2) v1;
      print_cell_b0_action (depth + 2) v2;
      print_cell_b1_action (depth + 2) v3;
    ] in put_node depth "l_actions" child

and print_cell_a_action depth node = match node with
  | Cell_A_Action v1 ->
    let child = String.concat ",\n" [
      print_layer_statement (depth + 2) v1;
    ] in put_node depth "cella_actions" child

and print_cell_b0_action depth node = match node with
  | Cell_B0_Action v1 ->
    let child = String.concat ",\n" [
      print_layer_statement (depth + 2) v1;
    ] in put_node depth "cellb0_actions" child

and print_cell_b1_action depth node = match node with
  | Cell_B1_Action v1 ->
    let child = String.concat ",\n" [
      print_layer_statement (depth + 2) v1;
    ] in put_node depth "cellb1_actions" child

and print_layer_statement depth node = match node with
  | Layer_Statement v1 ->
    let child = String.concat ",\n" [
      print_select_statement_list (depth + 2) v1;
    ] in put_node depth "l_stmt" child

and print_expression depth node = match node with
  | Constant_Expression v1 ->
    let child = String.concat ",\n" [
      print_constant (depth + 2) v1;
    ] in put_node depth "const_expr" child
  | Unary_Expression (v1, v2) ->
    let child = String.concat ",\n" [
      print_unary_operator (depth + 2) v1;
      print_expression (depth + 2) v2;
    ] in put_node depth "unop_expr" child
  | Binary_Expression (v1, v2, v3) ->
    let child = String.concat ",\n" [
      print_binary_operator (depth + 2) v1;
      print_expression (depth + 2) v2;
      print_expression (depth + 2) v3;
    ] in put_node depth "binop_expr" child
  | Field_Expression (v1, v2) ->
    let child = String.concat ",\n" [
      print_expression (depth + 2) v1;
      print_identifier (depth + 2) v2;
    ] in put_node depth "field_expr" child
  | Bit_Expression (v1, v2) ->
    let child = String.concat ",\n" [
      print_expression (depth + 2) v1;
      print_expression (depth + 2) v2;
    ] in put_node depth "bit_expr" child
  | Section_Expression (v1, v2, v3) ->
    let child = String.concat ",\n" [
      print_expression (depth + 2) v1;
      print_expression (depth + 2) v2;
      print_expression (depth + 2) v3;
    ] in put_node depth "section_expr" child
  | Parentheses_Expression v1 ->
    let child = String.concat ",\n" [
      print_expression (depth + 2) v1;
    ] in put_node depth "paren_expr" child
  | Length_Expression v1 ->
    let child = String.concat ",\n" [
      print_identifier (depth + 2) v1;
    ] in put_node depth "length_expr" child

and print_unary_operator depth node = match node with
  | Unary_Int ->
    put_op depth "unop" "int"
  | Unary_Not ->
    put_op depth "unop" "not"
  | Unary_Tilde ->
    put_op depth "unop" "~"

and print_binary_operator depth node = match node with
  | Binary_Add ->
    put_op depth "binop" "+"
  | Binary_Sub ->
    put_op depth "binop" "-"
  | Binary_Mul ->
    put_op depth "binop" "*"
  | Binary_Div ->
    put_op depth "binop" "/"
  | Binary_Mod ->
    put_op depth "binop" "%"
  | Binary_AndAnd ->
    put_op depth "binop" "&&"
  | Binary_OrOr ->
    put_op depth "binop" "||"
  | Binary_And ->
    put_op depth "binop" "&"
  | Binary_Or ->
    put_op depth "binop" "|"
  | Binary_Xor ->
    put_op depth "binop" "^"
  | Binary_EqEq ->
    put_op depth "binop" "=="
  | Binary_Neq ->
    put_op depth "binop" "<>"
  | Binary_Les ->
    put_op depth "binop" "<"
  | Binary_Gre ->
    put_op depth "binop" ">"
  | Binary_LesEq ->
    put_op depth "binop" "<="
  | Binary_GreEq ->
    put_op depth "binop" ">="
  | Binary_LesLes ->
    put_op depth "binop" "<<"
  | Binary_GreGre ->
    put_op depth "binop" ">>"
  | Binary_AddAdd ->
    put_op depth "binop" "++"
  | Binary_Hex ->
    put_op depth "binop" "hex"
  | Binary_Bit ->
    put_op depth "binop" "bit"

let ast_to_json ast =
  print_parser 0 ast
;;