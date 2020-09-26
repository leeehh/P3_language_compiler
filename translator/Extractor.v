Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Tree.
Require Import String.
Require Import Asm.

Local Open Scope error_monad_scope.

Set Implicit Arguments.

(* Extractor for Type layer_action *)

Definition extract_cell_alpha_action (la : local_action) : res cell_a_action := 
  match la with
  | Local_Action alpha_action beta_action delta_action => 
    OK alpha_action
  end.

Definition extract_cell_alpha_register (lrd : local_register_declaration) : res cell_a_register := 
  match lrd with
  | Local_Register_Declaration alpha_register beta_register delta_register =>
    OK alpha_register
  end.


(* Extractor of Type layer_action *)

Definition extract_layer_action (d : declaration) : res (list layer_action) :=
  match d with
  | As_Layer v1 => OK (v1 :: nil)
  | _ => OK nil
  end.

Fixpoint extract_layer_action_list (dl : list declaration) : res (list layer_action) := 
  match dl with
  | nil => OK nil
  | hd :: tl =>
    do v1 <- extract_layer_action hd;
    do v2 <- extract_layer_action_list tl;
    OK (v1 ++ v2)
  end.


(* Extractor of Type protocol_declaration *)

Definition extract_protocol_declaration (d : declaration) : res (list protocol_declaration) :=
  match d with
  | As_Protocol v1 => OK (v1 :: nil)
  | _ => OK nil
  end.

Fixpoint extract_protocol_declaration_list (l : list declaration) : res (list protocol_declaration) :=
  match l with
  | nil => OK nil
  | hd :: tl =>
    do v1 <- extract_protocol_declaration hd;
    do v2 <- extract_protocol_declaration_list tl;
    OK (v1 ++ v2)
  end.

Definition extract_protocol_branch_info (pi : pin_info) : res (list branch_info) :=
  OK (proto_stmt (proto_info pi)).

Fixpoint extract_protocol_branch_info_list (pil : list pin_info) : res (list (list branch_info)) :=
  match pil with
  | nil => 
    OK nil
  | hd :: tl =>
    do v1 <- extract_protocol_branch_info hd;
    do v2 <- extract_protocol_branch_info_list tl;
    OK (v1 :: v2)
  end.

Definition extract_constant_id (c : constant) : res identifier := 
  match c with
  | Const_Identifier id =>
    OK id
  | Const_Int i => 
    OK i
  | Const_Hex h =>
    OK h
  | Const_Bit b =>
    OK b
  end.
