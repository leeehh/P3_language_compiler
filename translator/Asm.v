Require Import Coqlib.
Require Import Integers.
Require Import String.
Require Import Tree.

Set Implicit Arguments.

Definition num := int.

Inductive condition :=
  | Reg_Condition : reg_segment -> int -> condition
  | Ins_Condition : ins_segment -> int -> condition
with reg_segment :=
  | Reg_Segment : int -> int -> reg_segment
with ins_segment :=
  | Ins_Segment : identifier -> int -> int -> ins_segment
  .

Record branch_info := {
  cond : list condition;
  stmt : list statement
}.

Record protocol_info := {
  proto_id : identifier;
  proto_length : int;
  proto_stmt : list branch_info
}.

Record pin_info := {
  proto_info : protocol_info;
  pin_name : identifier
}.

Inductive layer_block :=
  | Layer_Block : identifier -> list pin -> cell_alpha -> layer_block
with pin :=
  | Pin : identifier -> int -> pin
with cell_alpha :=
  | Cell_Alpha : alpha_pb -> cell_alpha
with alpha_pb :=
  | Alpha_Pb : list alpha_pb_item -> alpha_pb
with alpha_pb_item :=
  | Alpha_Pb_Item : int -> list condition -> int -> int -> int -> alpha_pb_item
  .

(* <parser_asm> *)
Inductive program_asm := ProgramAsm {
  protocol_info_list : list protocol_info;
  layer_block_list : list layer_block
}.