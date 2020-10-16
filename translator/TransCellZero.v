Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Tree.
Require Import String.
Require Import Asm.

Require Extractor.
Require TransUtil.
Require TransLayerStatement.
Require TransBranchInfo.

Local Open Scope error_monad_scope.

Set Implicit Arguments.

Fixpoint calculate_length (e : expression) (pil : list pin_info) : res int :=
  match e with
  | Length_Expression id =>
    do proto_info <- TransUtil.find_protocol_info_in_pin_list id pil;
    OK (proto_length proto_info)
  | Binary_Expression bin_op bin_expr1 bin_expr2 =>
    do len1 <- calculate_length bin_expr1 pil;
    do len2 <- calculate_length bin_expr2 pil;
    OK (Int.add len1 len2)
  | Constant_Expression con =>
    TransUtil.to_int con
  | _ =>
    Error (msg "invalid expression type b0!")
  end.

Definition trans_cell_zero_pc_item
  (b_index : int)
  (bi : branch_info)
  (pil : list pin_info) : res zero_pc_item :=
  do stmt_list <- OK (stmt bi);
  OK (Zero_Pc_Item b_index Int.one)
  .

Fixpoint trans_cell_zero_pc_item_list
  (b_index : int)
  (bil : list branch_info)
  (pil : list pin_info) : res (list zero_pc_item) :=
  match bil with
  | nil =>
    OK nil
  | hd :: tl =>
    do v1 <- trans_cell_zero_pc_item b_index hd pil;
    do v2 <- trans_cell_zero_pc_item_list (Int.add b_index Int.one) tl pil;
    OK (v1 :: v2)
  end.

Definition trans_cell_zero_pc
  (bil : list branch_info)
  (pil : list pin_info) : res zero_pc :=
  do zero_pc_item_list <- trans_cell_zero_pc_item_list Int.one bil pil;
  OK (Zero_Pc zero_pc_item_list)
  .


Fixpoint trans_cell_zero_pb_item
  (l_index : int) 
  (b_index : int) 
  (bi : branch_info) 
  (pil : list pin_info) 
  (ps : protocol_set) : res zero_pb_item :=
  OK (Zero_Pb_Item l_index (cond bi) b_index ).

Fixpoint trans_cell_zero_pb_item_list 
  (l_index : int) 
  (b_index : int) 
  (ibl : list branch_info) 
  (pil : list pin_info) 
  (ps : protocol_set) : res (list zero_pb_item) :=
  match ibl with
  | nil =>
    OK nil
  | hd :: tl =>
    do v1 <- trans_cell_zero_pb_item l_index b_index hd pil ps;
    do v2 <- trans_cell_zero_pb_item_list l_index (Int.add b_index Int.one) tl pil ps;
    OK (v1 :: v2)
  end.

Definition trans_cell_zero_pb 
  (l_index : int) 
  (bil : list branch_info) 
  (pil : list pin_info) 
  (ps : protocol_set) : res zero_pb :=
  do zero_pb_item_list <- trans_cell_zero_pb_item_list  l_index Int.one bil pil ps;
  OK (Zero_Pb zero_pb_item_list)
  .

Definition translate 
  (l_index : int) 
  (cba : cell_b0_action) 
  (cbr : cell_b0_register) 
  (pil : list pin_info) 
  (ps : protocol_set) : res cell_zero := 
  match cba with
  | Cell_B0_Action layer_stmt =>
    match layer_stmt with
    | Layer_Statement stmt_list =>
      do layer_branch_info_list <- TransLayerStatement.translate stmt_list pil;
      do zero_pb <- trans_cell_zero_pb l_index layer_branch_info_list pil ps;
      do zero_pc <- trans_cell_zero_pc layer_branch_info_list pil;
      OK (Cell_Zero zero_pb zero_pc)
    end
  end.
