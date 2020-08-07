Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Tree.
Require Import String.
Require Import Asm.

Require TransProtocol.
Require TransLayerBlock.

Local Open Scope error_monad_scope.

Set Implicit Arguments.

(* Fixpoint get_protocol_length (list declaration) : res (list (identifier * int)) := *)

(******* FROM FUNCTIONS BEGINS *******)

(* FUNCTION protocol_declaration_from *)
Definition protocol_declaration_from (d : declaration) : res (list protocol_declaration) :=
  match d with
  | As_Protocol v1 => OK (v1 :: nil)
  | _ => OK nil
  end.

(* FUNCTION protocol_declaration_list_from *)
Fixpoint protocol_declaration_list_from (l : list declaration) : res (list protocol_declaration) :=
  match l with
  | nil => OK nil
  | hd :: tl =>
    do v1 <- protocol_declaration_from hd;
    do v2 <- protocol_declaration_list_from tl;
    OK (v1 ++ v2)
  end.

(* FUNCTION layer_action_from *)
Definition layer_action_from (d : declaration) : res (list layer_action) :=
  match d with
  | As_Layer v1 => OK (v1 :: nil)
  | _ => OK nil
  end.

(* FUNCTION layer_action_list_from *)
Fixpoint layer_action_list_from (l : list declaration) : res (list layer_action) :=
  match l with
  | nil => OK nil
  | hd :: tl =>
    do v1 <- layer_action_from hd;
    do v2 <- layer_action_list_from tl;
    OK (v1 ++ v2)
  end.

(******** FROM FUNCTIONS ENDS ********)

Definition program_to_asm (p : program) : res program_asm := 
  match p with
  | Program v1 v2 v3 v4 v5 =>
    do pdl <- protocol_declaration_list_from v5;
    do pil <- TransProtocol.to_protocol_info_list pdl;

    do lal <- layer_action_list_from v5;
    do asm_lbl <- TransLayerBlock.to_layer_block_asm_list Int.one lal pil;
    OK (ProgramAsm pil asm_lbl)
  end.
