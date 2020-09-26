Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Tree.
Require Import String.
Require Import Asm.

Require TransExpression.

Local Open Scope error_monad_scope.

Set Implicit Arguments.

Definition join_branch_info (bi1 : branch_info) (bi2 : branch_info) : res branch_info :=
  match (cond bi1) with
  | nil =>
    OK {| cond := (cond bi2); stmt := (stmt bi1 ++ stmt bi2) |}
  | c1 =>
    match (cond bi2) with
    | nil =>
      OK {| cond := (cond bi1); stmt := (stmt bi1 ++ stmt bi2) |}
    | c2 =>
      OK {| cond := (cond bi1 ++ cond bi2); stmt := (stmt bi1 ++ stmt bi2) |}
    end
  end.

Fixpoint multiply_inner (bi : branch_info) (bil : list branch_info) : res (list branch_info) :=
  match bil with
  | nil =>
    OK nil
  | hd :: tl =>
    do v1 <- join_branch_info bi hd;
    do v2 <- multiply_inner bi tl;
    OK (v1 :: v2)
  end.

Fixpoint multiply_outer (bil1 : list branch_info) (bil2 : list branch_info) : res (list branch_info) :=
  match bil1 with
  | nil =>
    OK nil
  | hd :: tl =>
    do v1 <- multiply_inner hd bil2;
    do v2 <- multiply_outer tl bil2;
    OK (v1 ++ v2)
  end.

Fixpoint multiply_branch_info (bil1 : list branch_info) (bil2 : list branch_info) : res (list branch_info) :=
  match bil1 with
  | nil =>
    OK bil2
  | _ =>
    match bil2 with
    | nil => 
      OK bil1
    | _ =>
      multiply_outer bil1 bil2
    end
  end.

Fixpoint mix_branch_info (bill : list (list branch_info)) : res (list branch_info) :=
  match bill with
  | nil =>
    OK nil
  | hd :: tl =>
    do v1 <- mix_branch_info tl;
    multiply_branch_info hd v1
  end.