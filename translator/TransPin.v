Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Tree.
Require Import String.
Require Import Asm.

Require TransBase.

Local Open Scope error_monad_scope.

Set Implicit Arguments.

Definition make_pin_asm (l : int) (id : identifier) : pin_asm :=
  Pin_Asm id l
  .

Fixpoint get_protocol_length (id : identifier) (pil : list protocol_info) : res int :=
  match pil with
  | nil => Error (msg "canot be found in protocol!!")
  | hd :: tl =>
    if TransBase.identifier_eq id (protocol_id hd) then
      OK (protocol_length hd)
    else
      get_protocol_length id tl
  end.

Definition to_pin_asm (ld : layer_declaration) (pil : list protocol_info) : res (list pin_asm) :=
  match ld with
  | Layer_As_Protocol v1 v2 =>
    do len <- get_protocol_length v1 pil;
    OK (List.map (make_pin_asm len) v2 )
  end.
 

Fixpoint to_pin_asm_list (ldl : list layer_declaration) (pil : list protocol_info) : res (list pin_asm) :=
  match ldl with
  | nil => OK nil
  | hd :: tl =>
    do v1 <- to_pin_asm hd pil;
    do v2 <- to_pin_asm_list tl pil;
    OK (v1 ++ v2)
  end.