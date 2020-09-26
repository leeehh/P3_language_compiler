Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Tree.
Require Import String.
Require Import Asm.

Require Extractor.
Require TransProtoInfo.
Require TransLayerBlock.

Local Open Scope error_monad_scope.

Set Implicit Arguments.

(* Ling.Li, 2020.09.01 *)
(* This is the entrance of the whole translator *)
Definition translate (p : program) : res program_asm := 
  match p with
  | Program layer_reg_len cell_reg_len proto_set layer_set decl_list =>
    do proto_decl_list <- Extractor.extract_protocol_declaration_list decl_list;
    do proto_info_list <- TransProtoInfo.translate proto_decl_list;

    do layer_action_list <- Extractor.extract_layer_action_list decl_list;
    do layer_block_list <- TransLayerBlock.translate layer_action_list proto_info_list proto_set;

    OK (ProgramAsm proto_info_list layer_block_list)
  end.