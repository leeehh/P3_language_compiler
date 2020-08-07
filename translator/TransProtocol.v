Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Tree.
Require Import String.
Require Import Asm.

Require TransBase.

Local Open Scope error_monad_scope.

Set Implicit Arguments.

Fixpoint field_to_protocol_length (f : field) : res int :=
  match f with
  | Field v1 v2 =>
    TransBase.constant_to_int v2
  end.

Fixpoint field_list_to_protocol_length (fl : list field) : res int :=
  match fl with
  | nil => OK Int.zero
  | hd :: tl =>
    do sum1 <- field_to_protocol_length hd;
    do sum2 <- field_list_to_protocol_length tl;
    OK (Int.add sum1 sum2)
  end.

Fixpoint protocol_to_protocol_length (p : protocol) : res int :=
  match p with
  | Protocol v1 v2 =>
    match v1 with
    | Fields fl opt =>
      field_list_to_protocol_length fl
    end
  end.

Fixpoint to_protocol_info (pd : protocol_declaration) : res protocol_info :=
  match pd with
  | Protocol_Declaration v1 v2 =>
    do len <- protocol_to_protocol_length v2;
    OK ( {| protocol_id := v1; protocol_length := len |} )
  end.

Fixpoint to_protocol_info_list (l : list protocol_declaration) : res (list protocol_info) :=
  match l with
  | nil => OK nil
  | hd :: tl =>
    do v1 <- to_protocol_info hd;
    do v2 <- to_protocol_info_list tl;
    OK (v1 :: v2)
  end.