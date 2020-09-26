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

Fixpoint trans_cell_alpha_pb_item
  (l_index : int) 
  (b_index : int) 
  (bi : branch_info) 
  (pil : list pin_info) 
  (ps : protocol_set) : res alpha_pb_item :=
  do stmt_list <- OK (stmt bi);
  do next_id <- TransUtil.find_next_header stmt_list ps;
  do bypass_id <- TransUtil.find_bypass stmt_list;

  OK (Alpha_Pb_Item l_index (cond bi) b_index next_id bypass_id ).

Fixpoint trans_cell_alpha_pb_item_list 
  (l_index : int) 
  (b_index : int) 
  (ibl : list branch_info) 
  (pil : list pin_info) 
  (ps : protocol_set) : res (list alpha_pb_item) :=
  match ibl with
  | nil =>
    OK nil
  | hd :: tl =>
    do v1 <- trans_cell_alpha_pb_item l_index b_index hd pil ps;
    do v2 <- trans_cell_alpha_pb_item_list l_index (Int.add b_index Int.one) tl pil ps;
    OK (v1 :: v2)
  end.

Definition trans_cell_alpha_pb 
  (l_index : int) 
  (bil : list branch_info) 
  (pil : list pin_info) 
  (ps : protocol_set) : res alpha_pb :=
  do alpha_pb_item_list <- trans_cell_alpha_pb_item_list  l_index Int.one bil pil ps;
  OK (Alpha_Pb alpha_pb_item_list)
  .

Definition translate 
  (l_index : int) 
  (caa : cell_a_action) 
  (car : cell_a_register) 
  (pil : list pin_info) 
  (ps : protocol_set) : res cell_alpha := 
  match caa with
  | Cell_A_Action layer_stmt =>
    match layer_stmt with
    | Layer_Statement stmt_list =>
      do layer_branch_info_list <- TransLayerStatement.translate stmt_list;
      do proto_branch_info_list <- Extractor.extract_protocol_branch_info_list pil;
      do all_branch_info_list <- TransBranchInfo.mix_branch_info (layer_branch_info_list :: proto_branch_info_list);
      do alpha_pb <- trans_cell_alpha_pb l_index all_branch_info_list pil ps;
      OK (Cell_Alpha alpha_pb)
    end
  end.
