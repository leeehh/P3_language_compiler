Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Tree.
Require Import String.
Require Import Asm.

Require Extractor.
Require TransUtil.

Local Open Scope error_monad_scope.

Set Implicit Arguments.

Fixpoint multiply_inner (expr : expression) (el : list expression) : res (list expression) :=
  match el with
  | nil =>
    OK nil
  | hd :: tl =>
    do other <- multiply_inner expr tl;
    OK ((Binary_Expression Binary_AndAnd expr hd) :: other)
  end.

Fixpoint multiply_outer (el1 : list expression) (el2 : list expression) : res (list expression) :=
  match el1 with
  | nil =>
    OK nil
  | hd :: tl =>
    do v1 <- multiply_inner hd el2;
    do v2 <- multiply_outer tl el2;
    OK (v1 ++ v2)
  end.

Fixpoint multiply_expression (el1 : list expression) (el2 : list expression) : res (list expression) :=
  match el1 with
  | nil =>
    OK el2
  | _ =>
    match el2 with
    | nil =>
      OK el1
    | _ =>
      multiply_outer el1 el2
    end
  end.

Fixpoint reorder_expression (expr : expression) : res (list expression) :=
  match expr with
  | Parentheses_Expression paren_expr =>
    reorder_expression paren_expr
  | Binary_Expression bin_op bin_expr1 bin_expr2 =>
    match bin_op with
    | Binary_AndAnd =>
      do and_res1 <- reorder_expression bin_expr1;
      do and_res2 <- reorder_expression bin_expr2;
      multiply_expression and_res1 and_res2
    | Binary_OrOr =>
      do or_res1 <- reorder_expression bin_expr1;
      do or_res2 <- reorder_expression bin_expr2;
      OK (or_res1 ++ or_res2)
    | _ =>
      OK (expr :: nil)
    end
  | _ =>
    OK (expr :: nil)
  end.

Fixpoint split_expression (e : expression) : res (list expression) :=
  match e with
  | Binary_Expression bin_op bin_expr1 bin_expr2 =>
    match bin_op with
    | Binary_AndAnd =>
      do and_res1 <- split_expression bin_expr1;
      do and_res2 <- split_expression bin_expr2;
      OK (and_res1 ++ and_res2)
    | _ =>
      OK (e :: nil)
    end
  | _ =>
    OK (e :: nil)
  end.

Definition trans_protocol_ins_segment (pid : identifier) (fid : identifier) (fl : list field) : res ins_segment :=
  do (start, length) <- TransUtil.find_field fid fl Int.zero;
  OK (Ins_Segment pid start length).

Definition protocol_simple_expression_to_condition (id : identifier) (e : expression) (fl : list field) : res condition :=
  match e with
  | Binary_Expression op bin_expr1 bin_expr2 =>
    match op with
    | Binary_EqEq =>
      match bin_expr1 with
      | Constant_Expression constant1 =>
        do field_id <- Extractor.extract_constant_id constant1;
        match bin_expr2 with
        | Constant_Expression constant2 =>
          do ins_reg <- trans_protocol_ins_segment id field_id fl;
          do num <- TransUtil.to_int constant2;
          OK (Ins_Condition ins_reg num)
        | _ =>
          Error (msg "Unknown bin_expr2!")
        end
      | _ =>
        Error (msg "Unknown bin_expr1!")
      end
    | _ =>
      Error (msg "Invalid expression op!")
    end
  | _ =>
    Error (msg "Invalid expression type!")
  end.

Fixpoint protocol_simple_expression_to_condition_list (id : identifier) (el : list expression) (fl : list field) : res (list condition) :=
  match el with
  | nil =>
    OK nil
  | hd :: tl =>
    do v1 <- protocol_simple_expression_to_condition id hd fl;
    do v2 <- protocol_simple_expression_to_condition_list id tl fl;
    OK (v1 :: v2)
  end.

Definition protocol_expression_to_condition_list (id : identifier) (e : expression) (fl : list field) : res (list condition) :=
  do simple_expr_list <- split_expression e;
  protocol_simple_expression_to_condition_list id simple_expr_list fl.

Fixpoint protocol_expression_list_to_condition_list (id : identifier) (el : list expression) (fl : list field) : res (list (list condition)) :=
  match el with
  | nil =>
    OK nil
  | hd :: tl =>
    do v1 <- protocol_expression_to_condition_list id hd fl;
    do v2 <- protocol_expression_list_to_condition_list id tl fl;
    OK (v1 :: v2)
  end.
