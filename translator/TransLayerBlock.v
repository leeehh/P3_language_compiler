Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Tree.
Require Import String.
Require Import Asm.

Require TransBase.
Require TransPin.

Local Open Scope error_monad_scope.

Set Implicit Arguments.

Definition to_layer_block_asm (index : int) (la : layer_action) (pil : list protocol_info) : res (layer_block_asm) :=
  match la with
  | Layer_Action v1 v2 v3 v4 =>
    do asm_pin_list <- TransPin.to_pin_asm_list v3 pil;
    OK (Layer_Block_Asm v1 asm_pin_list)
  end.

Fixpoint to_layer_block_asm_list (index : int) (lal : list layer_action) (pil : list protocol_info) : res (list layer_block_asm) :=
  match lal with
  | nil => OK nil
  | hd :: tl =>
    do v1 <- to_layer_block_asm index hd pil;
    do v2 <- to_layer_block_asm_list (Int.add index Int.one) tl pil;
    OK (v1 :: v2)
  end.