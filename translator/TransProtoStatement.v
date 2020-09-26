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

Definition trans_if_branch (id : identifier) (ib : if_branch) (fl : list field) : res (list branch_info) :=
  match ib with
  | If_Branch expr stmt_list =>
    do expr_list <- TransExpression.reorder_expression expr;
    do cond_list_list <- TransExpression.protocol_expression_list_to_condition_list id expr_list fl;
    cons_branch_info_list cond_list_list stmt_list
  end.


Fixpoint trans_if_branch_list (id : identifier) (ibl : list if_branch) (fl : list field) : res (list branch_info) :=
  match ibl with
  | nil =>
    OK nil
  | hd :: tl =>
    do v1 <- trans_if_branch id hd fl;
    do v2 <- trans_if_branch_list id tl fl;
    OK (v1 ++ v2)
  end.

Definition trans_protocol_statement (id : identifier) (s : select_statement) (fl : list field) : res (list branch_info) :=
  match s with
  | As_If if_stmt =>
    match if_stmt with
    | If_Statement if_branch_list else_branch =>
      trans_if_branch_list id if_branch_list fl
    end
  | As_Simple simple_stmt =>
    OK ({| cond := nil; stmt := (simple_stmt :: nil) |} :: nil)
  end.
    

Fixpoint trans_protocol_statement_list (id : identifier) (sl : list select_statement) (fl : list field) : res (list branch_info) :=
  match sl with
  | nil =>
    OK nil
  | hd :: tl =>
    do v1 <- trans_protocol_statement id hd fl;
    do v2 <- trans_protocol_statement_list id tl fl;
    TransBranchInfo.multiply_branch_info v1 v2
  end.

Definition translate (id : identifier) (sl : list select_statement) (fl : list field) : res (list branch_info) :=
  trans_protocol_statement_list id sl fl.
