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
  match (expr bi1) with
  | None =>
    OK {| expr := (expr bi2); stmt := (stmt bi1 ++ stmt bi2) |}
  | Some e1 =>
    match (expr bi2) with
    | None =>
      OK {| expr := (expr bi1); stmt := (stmt bi1 ++ stmt bi2) |}
    | Some e2 =>
      OK {| expr := (Some (Binary_Expression Binary_AndAnd e1 e2)); stmt := (stmt bi1 ++ stmt bi2) |}
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

Fixpoint cons_branch_info_list (el : list expression) (sl : list statement) : res (list branch_info) :=
  match el with
  | nil =>
    OK nil
  | hd :: tl =>
    do v2 <- cons_branch_info_list tl sl;
    OK ({| expr := (Some hd); stmt := sl |} :: v2)
  end.

Definition trans_if_branch (ib : if_branch) : res (list branch_info) :=
  match ib with
  | If_Branch expr stmt_list =>
    do expr_list <- TransExpression.reorder_expression expr;
    cons_branch_info_list expr_list stmt_list
  end.


Fixpoint trans_if_branch_list (ibl : list if_branch) : res (list branch_info) :=
  match ibl with
  | nil =>
    OK nil
  | hd :: tl =>
    do v1 <- trans_if_branch hd;
    do v2 <- trans_if_branch_list tl;
    OK (v1 ++ v2)
  end.

Definition trans_select_statement (s : select_statement) : res (list branch_info) :=
  match s with
  | As_If if_stmt =>
    match if_stmt with
    | If_Statement if_branch_list else_branch =>
      trans_if_branch_list if_branch_list
    end
  | As_Simple simple_stmt =>
    OK ({| expr := None; stmt := (simple_stmt :: nil) |} :: nil)
  end.
    

Fixpoint trans_select_statement_list (sl : list select_statement) : res (list branch_info) :=
  match sl with
  | nil =>
    OK nil
  | hd :: tl =>
    do v1 <- trans_select_statement hd;
    do v2 <- trans_select_statement_list tl;
    multiply_branch_info v1 v2
  end.

Fixpoint mix_branch_info (bill : list (list branch_info)) : res (list branch_info) :=
  match bill with
  | nil =>
    OK nil
  | hd :: tl =>
    do v1 <- mix_branch_info tl;
    multiply_branch_info hd v1
  end.