Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Tree.
Require Import String.
Require Import Asm.

Require Extractor.
Require TransPin.
Require TransCellAlpha.

(* Require TransBase.
Require TransA. *)

Local Open Scope error_monad_scope.

Set Implicit Arguments.

Definition trans_layer_block 
  (l_index : int) 
  (la : layer_action) 
  (pil : list protocol_info) 
  (ps : protocol_set) : res layer_block := 
  match la with
  | Layer_Action layer_id local_reg_decl layer_decl_list local_action =>
    do pin_info_list <- TransPin.translate layer_decl_list pil;
    do pin_list <- TransPin.info_to_pin_list pin_info_list;
    
    do cell_alpha_register <- Extractor.extract_cell_alpha_register local_reg_decl;
    do cell_alpha_action <- Extractor.extract_cell_alpha_action local_action;
    do cell_alpha <- TransCellAlpha.translate l_index cell_alpha_action cell_alpha_register pin_info_list ps;

    OK (Layer_Block layer_id pin_list cell_alpha)
  end.

Fixpoint trans_layer_block_list 
  (l_index : int) 
  (lal : list layer_action) 
  (pil : list protocol_info)
  (ps : protocol_set) : res (list layer_block) := 
  match lal with
  | nil => OK nil
  | hd :: tl =>
    do v1 <- trans_layer_block l_index hd pil ps;
    do v2 <- trans_layer_block_list (Int.add l_index Int.one) tl pil ps;
    OK (v1 :: v2)
  end.

Definition translate 
  (lal : list layer_action) 
  (pil : list protocol_info) 
  (ps : protocol_set) : res (list layer_block) := 
  trans_layer_block_list Int.one lal pil ps.