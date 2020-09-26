(**************************************
  Filename: AstWriter.ml
  Project:  P3 Compilers
  Author:   Ling.Li
  Date:     2018.06.21
**************************************)

open Tree

let rec bin2int i = match i with
  | BinNums.Coq_xI p -> let n = bin2int p in n + n + 1
  | BinNums.Coq_xO p -> let n = bin2int p in n + n
  | BinNums.Coq_xH -> 1

let indent depth str = Printf.sprintf "%s%s" (String.make (depth * 2) ' ') str

let rec print_parser depth node = match node with
  | Program (v1, v2, v3, v4, v5) ->
    String.concat "\n" [
      indent depth "<program>";
      print_layer_register_length (depth + 1) v1;
      print_cell_register_length (depth + 1) v2;
      print_protocol_set (depth + 1) v3;
      print_layer_set (depth + 1) v4;
      print_declaration_list (depth + 1) v5;
    ]

and print_layer_register_length depth node = match node with
  | Layer_Register_Length v1 ->
    String.concat "\n" [
      indent depth "<layer_reg_len>";
      print_constant (depth + 1) v1;
    ]

and print_cell_register_length depth node = match node with
  | Cell_Register_Length v1 ->
    String.concat "\n" [
      indent depth "<cell_reg_len>";
      print_constant (depth + 1) v1;
    ]

and print_constant depth node = match node with
  | Const_Identifier v1 ->
    String.concat "\n" [
      indent depth "<const_id>";
      print_identifier (depth + 1) v1;
    ]
  | Const_Int v1 ->
    String.concat "\n" [
      indent depth "<const_int>";
      print_integer (depth + 1) v1;
    ]
  | Const_Hex v1 ->
    String.concat "\n" [
      indent depth "<const_hex>";
      print_hexadecimal (depth + 1) v1;
    ]
  | Const_Bit v1 ->
    String.concat "\n" [
      indent depth "<const_bit>";
      print_bit (depth + 1) v1;
    ]

and print_identifier depth node = 
  indent depth (Printf.sprintf "<id>(%s - %d)" node.name (bin2int node.key))

and print_integer depth node =
  indent depth (Printf.sprintf "<id>(%s - %d)" node.name (bin2int node.key))

and print_hexadecimal depth node =
  indent depth (Printf.sprintf "<id>(%s - %d)" node.name (bin2int node.key))

and print_bit depth node =
  indent depth (Printf.sprintf "<id>(%s - %d)" node.name (bin2int node.key))

and print_id_list depth node =
  String.concat "\n" (List.map (print_identifier depth) node);
  
and print_protocol_set depth node = match node with
  | Protocol_Set v1 ->
    String.concat "\n" [
      indent depth "<protocol_set>";
      print_id_list (depth + 1) v1;
    ]

and print_layer_set depth node = match node with
  | Layer_Set v1 ->
    String.concat "\n" [
      indent depth "<layer_set>";
      print_id_list (depth + 1) v1;
    ]

and print_declaration_list depth node =
  String.concat "\n" (List.map (print_declaration depth) node)

and print_declaration depth node = match node with
  | As_Constant v1 ->
    String.concat "\n" [
      indent depth "<decl>";
      print_constant_declaration (depth + 1) v1;
    ]
  | As_Protocol v1 ->
    String.concat "\n" [
      indent depth "<decl>";
      print_protocol_declaration (depth + 1) v1;
    ]
  | As_Register_Access v1 ->
    String.concat "\n" [
      indent depth "<decl>";
      print_register_access_set (depth + 1) v1;
    ]
  | As_Layer v1 ->
    String.concat "\n" [
      indent depth "<decl>";
      print_layer_action (depth + 1) v1;
    ]

and print_constant_declaration depth node = match node with
  | Constant_Declaration (v1, v2) ->
    String.concat "\n" [
      indent depth "<constant_decl>";
      print_identifier (depth + 1) v1;
      print_constant (depth + 1) v2;
    ]

and print_protocol_declaration depth node = match node with
  | Protocol_Declaration (v1, v2) ->
    String.concat "\n" [
      indent depth  "<protocol_decl>";
      print_identifier (depth + 1) v1;
      print_protocol (depth + 1) v2;
    ]

and print_protocol depth node = match node with
  | Protocol (v1, v2) ->
    String.concat "\n" [
      indent depth "<protocol>";
      print_fields (depth + 1) v1;
      print_protocol_statement (depth + 1) v2;
    ]

and print_fields depth node = match node with
  | Fields (v1, v2) ->
    String.concat "\n" [
      indent depth "<fields>";
      print_field_list (depth + 1) v1;
      print_optional_field (depth + 1) v2;
    ]

and print_field_list depth node =
  String.concat "\n" (List.map (print_field depth) node)
  
and print_field depth node = match node with
  | Field (v1, v2) ->
    String.concat "\n" [
      indent depth "<field>";
      print_identifier (depth + 1) v1;
      print_constant (depth + 1) v2;
    ]

and print_optional_field depth node = match node with
  | Optional_Field (v1, v2) ->
    String.concat "\n" [
      indent depth "<option_field>";
      print_identifier (depth + 1) v1;
      print_constant (depth + 1) v2;
    ]
  | No_Optional_Field ->
    indent depth "<no_option_field>"

and print_protocol_statement depth node = match node with
  | Protocol_Statement v1 ->
    String.concat "\n" [
      indent depth "<p_stmts>";
      print_select_statement_list (depth + 1) v1;
    ]

and print_select_statement_list depth node =
  String.concat "\n" (List.map (print_select_statement depth) node)

and print_select_statement depth node = match node with
  | As_If v1 ->
    String.concat "\n" [
      indent depth "<select_stmt>";
      print_if_statement (depth + 1) v1;
    ]
  | As_Simple v1 ->
    String.concat "\n" [
      indent depth "<select_stmt>";
      print_statement (depth + 1) v1;
    ]

and print_if_statement depth node = match node with
  | If_Statement (v1, v2) ->
    String.concat "\n" [
      indent depth "<if_else_stmt>";
      print_if_branch_list (depth + 1) v1;
      print_else_branch (depth + 1) v2;
    ]

and print_if_branch_list depth node =
  String.concat "\n" (List.map (print_if_branch depth) node)

and print_if_branch depth node = match node with
  | If_Branch (v1, v2) ->
    String.concat "\n" [
      indent depth "<if_branch>";
      print_expression (depth + 1) v1;
      print_statement_list (depth + 1) v2;
    ]

and print_else_branch depth node = match node with
  | Else_Branch v1 ->
    String.concat "\n" [
      indent depth "<else_branch>";
      print_statement_list (depth + 1) v1;
    ]

and print_statement_list depth node =
  String.concat "\n" (List.map (print_statement depth) node)

and print_statement depth node = match node with
  | Next_Header_Statement v1 ->
    String.concat "\n" [
      indent depth "<header_stmt>";
      print_identifier (depth + 1) v1;
    ]
  | Length_Statement v1 ->
    String.concat "\n" [
      indent depth "<length_stmt>";
      print_expression (depth + 1) v1;
    ]
  | Bypass_Statement v1 ->
    String.concat "\n" [
      indent depth "<bypass_stmt>";
      print_constant (depth + 1) v1;
    ]
  | Action_Statement v1 ->
    String.concat "\n" [
      indent depth "<action_stmt>";
      print_action_statement (depth + 1) v1;
    ]


and print_action_statement depth node = match node with
  | Act_Statement v1 ->
    String.concat "\n" [
      indent depth "<action>";
      print_instruction_list (depth + 1) v1;
    ]

and print_instruction_list depth node = 
    String.concat "\n" (List.map (print_instruction depth) node)

and print_instruction depth node = match node with
  | Set_Instruction (v1, v2) ->
    String.concat "\n" [
      indent depth "<set_instruction>";
      print_target_register_access_name (depth + 1) v1;
      print_expression (depth + 1) v2;
    ]
  | Mov_Instruction (v1, v2) ->
    String.concat "\n" [
      indent depth "<mov_instruction>";
      print_move_register_access_name (depth + 1) v1;
      print_expression (depth + 1) v2;
    ]
  | Lg_Instruction (v1, v2, v3) ->
    String.concat "\n" [
      indent depth "<lg_instruction>";
      print_target_register_access_name (depth + 1) v1;
      print_expression (depth + 1) v2;
      print_expression (depth + 1) v3;
    ]
  | Eq_Instruction (v1, v2, v3) ->
    String.concat "\n" [
      indent depth "<eq_instruction>";
      print_target_register_access_name (depth + 1) v1;
      print_expression (depth + 1) v2;
      print_expression (depth + 1) v3;
    ]

and print_register_access_set_list depth node =
  String.concat "\n" (List.map (print_register_access_set depth) node)

and print_register_access_set depth node = match node with
  | Register_Access_Set_Section (v1, v2, v3) ->
    String.concat "\n" [
      indent depth "<reg_acc_set_section>";
      print_register_access_name (depth + 1) v1;
      print_expression (depth + 1) v2;
      print_expression (depth + 1) v3;
    ]
  | Register_Access_Set_Bit (v1, v2) ->
    String.concat "\n" [
      indent depth "<reg_acc_set_bit>";
      print_register_access_name (depth + 1) v1;
      print_expression (depth + 1) v2;
    ]

and print_register_access_name depth node =
  String.concat "\n" [
    indent depth "<reg_acc_name>";
    print_identifier (depth + 1) node
  ]

and print_target_register_access_name depth node = match node with
  | Target_Register_Id v1 ->
    String.concat "\n" [
      indent depth "<tgt_reg_acc_id>";
      print_identifier (depth + 1) v1;
    ]
  | Target_Register_Section (v1, v2, v3) ->
    String.concat "\n" [
      indent depth "<tgt_reg_acc_section>";
      print_target_register_access_name (depth + 1) v1;
      print_expression (depth + 1) v2;
      print_expression (depth + 1) v3;
    ]
  | Target_Register_Bit (v1, v2) ->
    String.concat "\n" [
      indent depth "<tgt_reg_acc_bit>";
      print_target_register_access_name (depth + 1) v1;
      print_expression (depth + 1) v2;
    ]

and print_move_register_access_name depth node = match node with
  | Move_Register_Single v1 ->
    String.concat "\n" [
      indent depth "<mov_reg_acc_single>";
      print_target_register_access_name (depth + 1) v1;
    ]
  | Move_Register_Double (v1, v2) ->
    String.concat "\n" [
      indent depth "<mov_reg_acc_double>";
      print_move_register_access_name (depth + 1) v1;
      print_target_register_access_name (depth + 1) v2;
    ]

and print_layer_action depth node = match node with
  | Layer_Action (v1, v2, v3, v4) ->
    String.concat "\n" [
      indent depth "<layer_action>";
      print_identifier (depth + 1) v1;
      print_local_register_declaration (depth + 1) v2;
      print_layer_declaration_list (depth + 1) v3;
      print_local_action (depth + 1) v4;
    ]

and print_layer_declaration_list depth node =
  String.concat "\n" (List.map (print_layer_declaration depth) node)

and print_layer_declaration depth node = match node with
  | Layer_As_Protocol (v1, v2) ->
    String.concat "\n" [
      indent depth "<l_decl>";
      print_identifier (depth + 1) v1;
      print_id_list (depth + 1) v2;
    ]

and print_local_register_declaration depth node = match node with
  | Local_Register_Declaration (v1, v2, v3) ->
    String.concat "\n" [
      indent depth "<local_reg_decl>";
      print_cell_a_register (depth + 1) v1;
      print_cell_b0_register (depth + 1) v2;
      print_cell_b1_register (depth + 1) v3;
    ]

and print_cell_a_register depth node = match node with
  | Cell_A_Register v1 ->
    String.concat "\n" [
      indent depth "<cella_regs>";
      print_register_access_set_list (depth + 1) v1;
    ]

and print_cell_b0_register depth node = match node with
  | Cell_B0_Register v1 ->
    String.concat "\n" [
      indent depth "<cellb0_regs>";
      print_register_access_set_list (depth + 1) v1;
    ]

and print_cell_b1_register depth node = match node with
  | Cell_B1_Register v1 ->
    String.concat "\n" [
      indent depth "<cellb1_regs>";
      print_register_access_set_list (depth + 1) v1;
    ]

and print_local_action depth node = match node with
  | Local_Action (v1, v2, v3) ->
    String.concat "\n" [
      indent depth "<l_actions>";
      print_cell_a_action (depth + 1) v1;
      print_cell_b0_action (depth + 1) v2;
      print_cell_b1_action (depth + 1) v3;
    ]

and print_cell_a_action depth node = match node with
  | Cell_A_Action v1 ->
    String.concat "\n" [
      indent depth "<cella_actions>";
      print_layer_statement (depth + 1) v1;
    ]

and print_cell_b0_action depth node = match node with
  | Cell_B0_Action v1 ->
    String.concat "\n" [
      indent depth "<cellb0_actions>";
      print_layer_statement (depth + 1) v1;
    ]

and print_cell_b1_action depth node = match node with
  | Cell_B1_Action v1 ->
    String.concat "\n" [
      indent depth "<cellb1_actions>";
      print_layer_statement (depth + 1) v1;
    ]

and print_layer_statement depth node = match node with
  | Layer_Statement v1 ->
    String.concat "\n" [
      indent depth "<l_stmts>";
      print_select_statement_list (depth + 1) v1;
    ]

and print_expression depth node = match node with
  | Constant_Expression v1 ->
    String.concat "\n" [
      indent depth "<const_expr>";
      print_constant (depth + 1) v1;
    ]
  | Unary_Expression (v1, v2) ->
    String.concat "\n" [
      indent depth "<unop_expr>";
      print_unary_operator (depth + 1) v1;
      print_expression (depth + 1) v2;
    ]
  | Binary_Expression (v1, v2, v3) ->
    String.concat "\n" [
      indent depth "<binop_expr>";
      print_binary_operator (depth + 1) v1;
      print_expression (depth + 1) v2;
      print_expression (depth + 1) v3;
    ]
  | Field_Expression (v1, v2) ->
    String.concat "\n" [
      indent depth "<field_expr>";
      print_expression (depth + 1) v1;
      print_identifier (depth + 1) v2;
    ]
  | Bit_Expression (v1, v2) ->
    String.concat "\n" [
      indent depth "<bit_expr>";
      print_expression (depth + 1) v1;
      print_expression (depth + 1) v2;
    ]
  | Section_Expression (v1, v2, v3) ->
    String.concat "\n" [
      indent depth "<section_expr>";
      print_expression (depth + 1) v1;
      print_expression (depth + 1) v2;
      print_expression (depth + 1) v3;
    ]
  | Parentheses_Expression v1 ->
    String.concat "\n" [
      indent depth "<paren_expr>";
      print_expression (depth + 1) v1;
    ]
  | Length_Expression v1 ->
    String.concat "\n" [
      indent depth "<length_expr>";
      print_identifier (depth + 1) v1;
    ]

and print_unary_operator depth node = match node with
  | Unary_Int ->
    indent depth "<unop>(int)"
  | Unary_Not ->
    indent depth "<unop>(not)"
  | Unary_Tilde ->
    indent depth "<unop>(~)"

and print_binary_operator depth node = match node with
  | Binary_Add ->
    indent depth "<binop>(+)"
  | Binary_Sub ->
    indent depth "<binop>(-)"
  | Binary_Mul ->
    indent depth "<binop>(*)"
  | Binary_Div ->
    indent depth "<binop>(/)"
  | Binary_Mod ->
    indent depth "<binop>(%)"
  | Binary_AndAnd ->
    indent depth "<binop>(&&)"
  | Binary_OrOr ->
    indent depth "<binop>(||)"
  | Binary_And ->
    indent depth "<binop>(&)"
  | Binary_Or ->
    indent depth "<binop>(|)"
  | Binary_Xor ->
    indent depth "<binop>(^)"
  | Binary_EqEq ->
    indent depth "<binop>(==)"
  | Binary_Neq ->
    indent depth "<binop>(<>)"
  | Binary_Les ->
    indent depth "<binop>(<)"
  | Binary_Gre ->
    indent depth "<binop>(>)"
  | Binary_LesEq ->
    indent depth "<binop>(<=)"
  | Binary_GreEq ->
    indent depth "<binop>(>=)"
  | Binary_LesLes ->
    indent depth "<binop>(<<)"
  | Binary_GreGre ->
    indent depth "<binop>(>>)"
  | Binary_AddAdd ->
    indent depth "<binop>(++)"
  | Binary_Hex ->
    indent depth "<binop>(hex)"
  | Binary_Bit ->
    indent depth "<binop>(bit)>"

let ast_to_string ast =
  print_parser 0 ast
;;