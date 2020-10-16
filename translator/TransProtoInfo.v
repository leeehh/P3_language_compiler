Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Tree.
Require Import String.
Require Import Asm.

Require TransUtil.
Require TransProtoStatement.

Local Open Scope error_monad_scope.

Set Implicit Arguments.

Fixpoint trans_protocol_length (fl : list field) : res int :=
  match fl with
  | nil => OK Int.zero
  | hd :: tl =>
    do add1 <- match hd with
    | Field id constant => TransUtil.to_int constant
    end;
    do add2 <- trans_protocol_length tl;
    OK (Int.add add1 add2)
  end.

Definition trans_protocol_info (pd : protocol_declaration) : res protocol_info :=
  match pd with
  | Protocol_Declaration id protocol =>
    do field_info <- match protocol with
    | Protocol fields proto_stmt =>
      match fields with
      | Fields field_list option_field => 
        OK field_list
      end
    end;
    do length <- trans_protocol_length field_info;

    do body <- match protocol with
    | Protocol fields proto_stmt =>
      match proto_stmt with
      | Protocol_Statement stmt_list =>
        TransProtoStatement.translate id stmt_list field_info
      end
    end;

    OK ( {| proto_id := id; proto_length := length; proto_field := field_info; proto_stmt := body |} )
  end.

Fixpoint trans_protocol_info_list (pdl : list protocol_declaration) : res (list protocol_info) :=
  match pdl with
  | nil => OK nil
  | hd :: tl =>
    do v1 <- trans_protocol_info hd;
    do v2 <- trans_protocol_info_list tl;
    OK (v1 :: v2)
  end.

Definition translate (pdl : list protocol_declaration) : res (list protocol_info) := trans_protocol_info_list pdl.