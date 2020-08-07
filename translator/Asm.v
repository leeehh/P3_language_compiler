Require Import Coqlib.
Require Import Integers.
Require Import String.
Require Import Tree.

Set Implicit Arguments.

Definition num := int.

Record protocol_info := {
  protocol_id : identifier;
  protocol_length : int
}.

(* <const_decl> *)
Inductive constant_declaration_asm :=
  | Constant_Declaration_Asm : identifier -> identifier -> constant_declaration_asm
with layer_block_asm :=
  | Layer_Block_Asm : identifier -> list pin_asm -> layer_block_asm
with pin_asm :=
  | Pin_Asm : identifier -> int -> pin_asm
  .

(* <parser_asm> *)
Inductive program_asm := ProgramAsm {
  protocol_info_list : list protocol_info;
  layer_block_list : list layer_block_asm
}.