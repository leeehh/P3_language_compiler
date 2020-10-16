Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Tree.
Require Import String.
Require Import Asm.

Local Open Scope error_monad_scope.

Set Implicit Arguments.

Parameter bool_of_str: str -> bool.
Parameter int_of_str: str -> int.
Parameter char_of_str: str -> int.

Definition to_int (c : constant) : res int :=
  match c with
  | Const_Identifier id | Const_Int id | Const_Bit id | Const_Hex id =>
    OK (int_of_str (name id))
  end.

Definition id_eq (x : identifier)(y : identifier) := peq (key x) (key y).

Fixpoint find_id_in_id_list (id : identifier) (il : list identifier) :=
  match il with
  | nil => 
    false
  | hd :: tl =>
    if id_eq id hd then
      true
    else
      find_id_in_id_list id tl
  end.

Fixpoint find_protocol_info (id : identifier) (pil : list protocol_info) : res protocol_info :=
  match pil with
  | nil => Error (msg "canot be found in protocol!!")
  | hd :: tl =>
    if id_eq id (proto_id hd) then
      OK hd
    else
      find_protocol_info id tl
  end.

Fixpoint find_protocol_info_in_pin_list (id : identifier) (pil : list pin_info) : res protocol_info :=
  match pil with
  | nil => 
    Error (msg "cannot be found in pin_list")
  | hd :: tl =>
    if id_eq id (pin_name hd) then
     OK (proto_info hd)
    else
      find_protocol_info_in_pin_list id tl
  end.

Fixpoint find_protocol_index (id : identifier) (idl : list identifier) (index : int) : res int :=
  match idl with
  | nil => Error (msg "canot be found in protocol!!")
  | hd :: tl =>
    if id_eq id hd then
      OK index
    else
      find_protocol_index id tl (Int.add index Int.one)
  end.

Fixpoint find_next_header (sl : list statement) (ps : protocol_set) : res int :=
  match sl with
  | nil =>
    Error (msg "next_header not found")
  | hd :: tl =>
    match hd with
    | Next_Header_Statement id =>
      match ps with
      | Protocol_Set id_list =>
        find_protocol_index id id_list Int.one
      end
    | _ =>
      find_next_header tl ps
    end
  end.

Fixpoint find_bypass (sl : list statement) : res int :=
  match sl with
  | nil =>
    Error (msg "bypass not found")
  | hd :: tl =>
    match hd with
    | Bypass_Statement const =>
      to_int const
    | _ =>
      find_bypass tl
    end
  end.

Fixpoint find_field (fid : identifier) (fl : list field) (index : int) : res (int * int) :=
  match fl with
  | nil =>
    OK (Int.zero, Int.zero)
  | hd :: tl =>
    match hd with
    | Field id const =>
      do num <- to_int const;
      if id_eq fid id then
        OK (index, num)
      else
        find_field fid tl (Int.add index num)
    end
  end.
