(**************************************
  Filename: AsmWriter.ml
  Project:  P3 Compilers
  Author:   Ling.Li
  Date:     2018.06.21
**************************************)

open Asm
open Tree
open Camlcoq
open AstWriter

let to_int i = Camlcoq.camlint_of_coqint i

let rec print_program_asm node = 
  String.concat "\n" [
    print_layer_block_list node.layer_block_list;
  ]

and print_layer_block_list node =
  String.concat "\n" (List.map print_layer_block node)

and print_layer_block node = match node with
  | Layer_Block (v1, v2, v3, v4, v5) ->
    String.concat "\n" [
      print_layer_id v1;
      print_pin_list v2;
      print_cell_alpha v3;
      print_cell_zero v4;
      print_cell_one v5;
    ]

and print_layer_id node = 
  (Printf.sprintf "%s:" node.name)

and print_pin_list node =
  String.concat "\n" (List.map print_pin node)

and print_pin node = match node with
  | Pin (v1, v2) ->
    (Printf.sprintf "Pins (%s, %ld)" v1.name (to_int v2))

and print_cell_alpha node = match node with
  | Cell_Alpha (v1, v2) ->
    String.concat "\n" [
      "Abegin";
      print_cell_alpha_pb v1;
      "Aend";
      "ACbegin";
      print_cell_alpha_pc v2;
      "ACend";
    ]

and print_cell_alpha_pb node = match node with
  | Alpha_Pb v1 ->
    String.concat "\n" (List.map print_cell_alpha_pb_item v1)
  
and print_cell_alpha_pb_item node = match node with
  | Alpha_Pb_Item (v1, v2, v3, v4, v5) ->
    (Printf.sprintf "%#lx, { %s }, %#lx, %#lx, %ld" (to_int v1) (print_condition_list v2) (to_int v3) (to_int v4) (to_int v5))

and print_condition_list node = 
  String.concat "," (List.map print_condition node)

and print_condition node = match node with
  | Reg_Condition (v1, v2) ->
    (Printf.sprintf "%s == %#lx" (print_reg_segment v1) (to_int v2))
  | Ins_Condition (v1, v2) ->
    (Printf.sprintf "%s == %#lx" (print_ins_segment v1) (to_int v2))

and print_reg_segment node = match node with
  | Reg_Segment (v1, v2) ->
    (Printf.sprintf "(IRF, %ld, %ld)" (to_int v1) (to_int v2))

and print_ins_segment node = match node with
  | Ins_Segment (v1, v2, v3) ->
    (Printf.sprintf "(%s, %ld, %ld)" v1.name (to_int v2) (to_int v3))

and print_cell_alpha_pc node = match node with
  | Alpha_Pc v1 ->
    String.concat "\n" (List.map print_cell_alpha_pc_item v1)

and print_cell_alpha_pc_item node = match node with
  | Alpha_Pc_Item (v1, v2, v3) ->
    (Printf.sprintf "%#lx, { %#lx }, %#lx" (to_int v1) (*print_condition_list v2*) (to_int v2) (Int32.div (to_int v3) (Int32.of_int 8)))

and print_cell_zero node = match node with
  | Cell_Zero (v1, v2) ->
    String.concat "\n" [
      "B0begin";
      print_cell_zero_pb v1;
      "B0end";
      "B0Cbegin";
      print_cell_zero_pc v2;
      "B0Cend";
    ]

and print_cell_zero_pb node = match node with
  | Zero_Pb v1 ->
    String.concat "\n" (List.map print_cell_zero_pb_item v1)
  
and print_cell_zero_pb_item node = match node with
  | Zero_Pb_Item (v1, v2, v3) ->
    (Printf.sprintf "%#lx, { %s }, %#lx" (to_int v1) (print_condition_list v2) (to_int v3))

and print_cell_zero_pc node = match node with
  | Zero_Pc v1 ->
    String.concat "\n" (List.map print_cell_zero_pc_item v1)

and print_cell_zero_pc_item node = match node with
  | Zero_Pc_Item (v1, v2) ->
    (Printf.sprintf "%#lx, { %#lx }" (to_int v1) (*print_condition_list v2*) (to_int v2))

and print_cell_one node = match node with
  | Cell_One (v1, v2) ->
    String.concat "\n" [
      "B1begin";
      print_cell_one_pb v1;
      "B1end";
      "B1Cbegin";
      print_cell_one_pc v2;
      "B1Cend";
    ]

and print_cell_one_pb node = match node with
  | One_Pb v1 ->
    String.concat "\n" (List.map print_cell_one_pb_item v1)
  
and print_cell_one_pb_item node = match node with
  | One_Pb_Item (v1, v2, v3) ->
    (Printf.sprintf "%#lx, { %s }, %#lx" (to_int v1) (print_condition_list v2) (to_int v3))

and print_cell_one_pc node = match node with
  | One_Pc v1 ->
    String.concat "\n" (List.map print_cell_one_pc_item v1)

and print_cell_one_pc_item node = match node with
  | One_Pc_Item (v1, v2) ->
    (Printf.sprintf "%#lx, { %#lx }" (to_int v1) (*print_condition_list v2*) (to_int v2))

(* 
and print_constant_list_asm node =
  String.concat "\n" (List.map print_constant_asm node)

and print_constant_asm node = match node with
  | Constant_Declaration_Asm (v1, v2) -> 
    (Printf.sprintf "const %s = %s;" v1.name v2.name)

and print_cella_pc_cur_asm node = match node with
  | A_Pc_Cur v1 ->
    print_cella_pc_cur_item_list_asm v1

and print_cella_pc_cur_item_list_asm node =
  String.concat "\n" (List.map print_cella_pc_cur_item_asm node)

and print_cella_pc_cur_item_asm node = match node with
  | A_Pc_Cur_Item v1 ->
    (Printf.sprintf "%s" (print_sub_id_asm v1))

and print_sub_id_asm node = match node with
  | Sub_Id v1 ->
    (Printf.sprintf "%#lx" (to_int v1)) *)

let asm_to_string asm =
  print_program_asm asm
;;