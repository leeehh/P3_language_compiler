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

Fixpoint cons_branch_info_list (cl : list (list condition)) (sl : list statement) : res (list branch_info) :=
  match cl with
  | nil =>
    OK nil
  | hd :: tl =>
    do v2 <- cons_branch_info_list tl sl;
    OK ({| cond := hd; stmt := sl |} :: v2)
  end.

Definition trans_if_branch 
  (ib : if_branch)
  (pil : list pin_info) : res (list branch_info) :=
  match ib with
  | If_Branch expr stmt_list =>
    do expr_list <- TransExpression.reorder_expression expr;
    do cond_list_list <- TransExpression.layer_expression_list_to_condition_list expr_list pil;
    cons_branch_info_list cond_list_list stmt_list
  end.


Fixpoint trans_if_branch_list 
  (ibl : list if_branch)
  (pil : list pin_info) : res (list branch_info) :=
  match ibl with
  | nil =>
    OK nil
  | hd :: tl =>
    do v1 <- trans_if_branch hd pil;
    do v2 <- trans_if_branch_list tl pil;
    OK (v1 ++ v2)
  end.

Definition trans_select_statement 
  (s : select_statement)
  (pil : list pin_info) : res (list branch_info) :=
  match s with
  | As_If if_stmt =>
    match if_stmt with
    | If_Statement if_branch_list else_branch =>
      trans_if_branch_list if_branch_list pil
    end
  | As_Simple simple_stmt =>
    OK ({| cond := nil; stmt := (simple_stmt :: nil) |} :: nil)
  end.

Fixpoint trans_select_statement_list 
  (sl : list select_statement)
  (pil : list pin_info) : res (list branch_info) :=
  match sl with
  | nil =>
    OK nil
  | hd :: tl =>
    do v1 <- trans_select_statement hd pil;
    do v2 <- trans_select_statement_list tl pil;
    TransBranchInfo.multiply_branch_info v1 v2
  end.

Definition translate 
  (sl : list select_statement)
  (pil : list pin_info) : res (list branch_info) := 
  trans_select_statement_list sl pil.
