Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Tree.
Require Import String.
Require Import Asm.

Require TransExpression.
Require TransBranchInfo.

Local Open Scope error_monad_scope.

Set Implicit Arguments.

Fixpoint cons_branch_info_list (el : list expression) (sl : list statement) : res (list branch_info) :=
  match el with
  | nil =>
    OK nil
  | hd :: tl =>
    do v2 <- cons_branch_info_list tl sl;
    OK ({| cond := nil; stmt := sl |} :: v2)
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
    OK ({| cond := nil; stmt := (simple_stmt :: nil) |} :: nil)
  end.

Fixpoint trans_select_statement_list (sl : list select_statement) : res (list branch_info) :=
  match sl with
  | nil =>
    OK nil
  | hd :: tl =>
    do v1 <- trans_select_statement hd;
    do v2 <- trans_select_statement_list tl;
    TransBranchInfo.multiply_branch_info v1 v2
  end.

Definition translate (sl : list select_statement) : res (list branch_info) := 
  trans_select_statement_list sl.
