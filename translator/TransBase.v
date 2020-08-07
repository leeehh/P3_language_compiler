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

Definition constant_to_int (c : constant) : res int :=
  match c with
  | Const_Identifier id | Const_Int id | Const_Bit id | Const_Hex id =>
    OK (int_of_str (name id))
  end.

Definition identifier_eq (x : identifier)(y : identifier) := peq (key x) (key y).