Require Import Coqlib Errors.
Require Import Integers.
Require Import String.
Require Import Tree.

Local Open Scope string_scope.

Parameter ocaml_string: String.string -> Tree.str.
Parameter coq_string: Tree.str -> String.string.

Inductive ty : Type :=
| TInt : ty
| TBits (n : nat) : ty
| THexes (n : nat) : ty
| TRegAcc (k i j : nat) : ty
| TFieldAcc_cell (id : identifier) (k i j : nat) : ty
| TFieldAcc_protocol (k i j : nat) : ty
| TX (id : identifier) : ty
| TConst (t : ty) (val : Z) : ty
| TBool : ty.

Inductive protocol_symbol : Type :=
| Protocol_Symbol : list (string * nat) -> optional_field -> list protocol_statement -> protocol_symbol.

Definition id_scope := list (string * ty). (* Envs : C R L Lc P *)

Definition g_scope := list (string * nat). (* Envs : G *)

Definition pid_scope := list (string * protocol_symbol). (* use to search type pid *)

Definition empty_id_env := @nil (string * ty).

Definition empty_pid_env := @nil (string * protocol_symbol).

Definition Creglen := {| name := (ocaml_string "Creglen"); key := 1|}.

Definition Lreglen := {| name := (ocaml_string "Lreglen"); key := 1|}.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Definition get_idname (id : identifier) :=
  match id with
  | {| name := a; key := b |} => (coq_string a)
  end.

Definition get_idkey (id : identifier) :=
  match id with
  | {| name := a; key := b |} => b
  end.

Fixpoint find_scope_id {A : Type} (id : identifier) (l : list (string * A)) : res A:=
  match l with
  | nil => Error (msg (String.append (get_idname id) " was not defined."))
  | (s,a) :: t => if eqb_string (get_idname id) s then OK a
                else find_scope_id id t
  end.

Fixpoint find_scope_str {A : Type} (st : string) (l : list (string * A)) : res A:=
  match l with
  | nil => Error (msg (String.append st " was not defined."))
  | (s,a) :: t => if eqb_string st s then OK a
                else find_scope_str st t
  end.

Definition update_id_without_same {A : Type} (id : identifier) (t : A) (envs : list (string * A)) :=
  match find_scope_id id envs with
  | OK _ => Error (msg (String.append (get_idname id) " has been defined repeatedly in the current enviorment."))
  | Error _ => OK (((get_idname id),t) :: envs)
  end.

Definition update_str_without_same {A : Type} (st : string) (t : A) (envs : list (string * A)) :=
  match find_scope_str st envs with
  | OK _ => Error (msg (String.append st " has been defined repeatedly in the current enviorment."))
  | Error _ => OK ((st, t) :: envs)
  end.

Definition update_id_with_same {A : Type} (id : identifier) (t : A) (envs : list (string * A)) :=
  ((get_idname id),t) :: envs.

Definition update_str_with_same {A : Type} (st : string) (t : A) (envs : list (string * A)) :=
  (st,t) :: envs.

Fixpoint update_ids_without_same {A : Type} (ids : list identifier) (t : A) (envs : list (string * A)) :=
  match ids with
  | nil => OK envs
  | id :: t' => match update_id_without_same id t envs with
              | OK new_envs => update_ids_without_same t' t new_envs
              | Error e => Error e
              end
  end.

Fixpoint update_ids_with_same {A : Type} (ids : list identifier) (t : A) (envs : list (string * A)) :=
  match ids with
  | nil => envs
  | id :: t' =>
    let new_envs := update_id_with_same id t envs in
    update_ids_with_same t' t new_envs
  end.



