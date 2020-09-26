Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Tree.
Require Import String.
Require Import Asm.

Require TransUtil.

Local Open Scope error_monad_scope.

Set Implicit Arguments.

Definition info_to_pin (pi : pin_info) : res pin :=
  OK (Pin (pin_name pi) (proto_length (proto_info pi))).

Fixpoint info_to_pin_list (pil : list pin_info) : res (list pin) :=
  match pil with
  | nil =>
    OK nil
  | hd :: tl =>
    do v1 <- info_to_pin hd;
    do v2 <- info_to_pin_list tl;
    OK (v1 :: v2)
  end.

Definition make_pin_info (pi : protocol_info) (pn : identifier) : pin_info := {| proto_info := pi; pin_name := pn |}.

Definition trans_pin_info (ld : layer_declaration) (pil : list protocol_info) : res (list pin_info) :=
  match ld with
  | Layer_As_Protocol proto_id proto_name_list =>
    do proto_info <- TransUtil.find_protocol_info proto_id pil;
    OK (List.map (make_pin_info proto_info) proto_name_list)
  end.
 

Fixpoint trans_pin_info_list (ldl : list layer_declaration) (pil : list protocol_info) : res (list pin_info) :=
  match ldl with
  | nil => OK nil
  | hd :: tl =>
    do v1 <- trans_pin_info hd pil;
    do v2 <- trans_pin_info_list tl pil;
    OK (v1 ++ v2)
  end.

Definition translate (ldl : list layer_declaration) (pil : list protocol_info) : res (list pin_info) := 
  trans_pin_info_list ldl pil.
