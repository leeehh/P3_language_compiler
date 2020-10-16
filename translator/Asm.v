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
  proto_field : list field;
  proto_stmt : list branch_info
}.

Record pin_info := {
  proto_info : protocol_info;
  pin_name : identifier
}.

Inductive layer_block :=
  | Layer_Block : identifier -> list pin -> cell_alpha -> cell_zero -> cell_one -> layer_block

with pin :=
  | Pin : identifier -> int -> pin

with cell_alpha :=
  | Cell_Alpha : alpha_pb -> alpha_pc -> cell_alpha
with alpha_pb :=
  | Alpha_Pb : list alpha_pb_item -> alpha_pb
with alpha_pb_item :=
  | Alpha_Pb_Item : int -> list condition -> int -> int -> int -> alpha_pb_item
with alpha_pc :=
  | Alpha_Pc : list alpha_pc_item -> alpha_pc
with alpha_pc_item :=
  | Alpha_Pc_Item : int -> (*command*)int -> int -> alpha_pc_item

with cell_zero :=
  | Cell_Zero : zero_pb -> zero_pc -> cell_zero
with zero_pb :=
  | Zero_Pb : list zero_pb_item -> zero_pb
with zero_pb_item :=
  | Zero_Pb_Item : int -> list condition -> int -> zero_pb_item
with zero_pc :=
  | Zero_Pc : list zero_pc_item -> zero_pc
with zero_pc_item :=
  | Zero_Pc_Item : int -> (*command*)int -> zero_pc_item

with cell_one :=
  | Cell_One : one_pb -> one_pc -> cell_one
with one_pb :=
  | One_Pb : list one_pb_item -> one_pb
with one_pb_item :=
  | One_Pb_Item : int -> list condition -> int -> one_pb_item
with one_pc :=
  | One_Pc : list one_pc_item -> one_pc
with one_pc_item :=
  | One_Pc_Item : int -> (*command*)int -> one_pc_item
  .

(* <parser_asm> *)
Inductive program_asm := ProgramAsm {
  protocol_info_list : list protocol_info;
  layer_block_list : list layer_block
}.