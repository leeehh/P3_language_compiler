(**************************************
  Filename: AsmWriter.ml
  Project:  P3 Compilers
  Author:   Ling.Li
  Date:     2018.06.21
**************************************)

open Asm
open Tree
open Camlcoq

let to_int i = Camlcoq.camlint_of_coqint i

let rec print_program_asm node = 
  String.concat "\n" [
    print_protocol_info node.protocol_info_list;
    print_layer_block_list_asm node.layer_block_list;
  ]

and print_protocol_info node =
  String.concat "\n" (List.map print_protocol node)

and print_protocol node =
  (Printf.sprintf "protocol %s = %ld" node.protocol_id.name (to_int node.protocol_length))

and print_constant_list_asm node =
  String.concat "\n" (List.map print_constant_asm node)

and print_constant_asm node = match node with
  | Constant_Declaration_Asm (v1, v2) -> 
    (Printf.sprintf "const %s = %s;" v1.name v2.name)

and print_layer_block_list_asm node =
  String.concat "\n" (List.map print_layer_block_asm node)

and print_layer_block_asm node = match node with
  | Layer_Block_Asm (v1, v2) ->
    String.concat "\n" [
      print_layer_id_asm v1;
      print_pin_list_asm v2;
    ]

and print_layer_id_asm node = 
  (Printf.sprintf "%s:" node.name)

and print_pin_list_asm node =
  String.concat "\n" (List.map print_pin_asm node)

and print_pin_asm node = match node with
  | Pin_Asm (v1, v2) ->
    (Printf.sprintf "Pins (%s, %ld)" v1.name (to_int v2))

let asm_to_string asm =
  print_program_asm asm
;;