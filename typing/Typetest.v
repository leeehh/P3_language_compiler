Require Import Coqlib Errors.
Require Import Integers.
Require Import String.
Require Import Types.
Require Import Tree.



Print identifier.

Compute 1.
Check 1.

Open Scope string_scope.
Definition i : identifier := {| name:="123"; key:=11 |}.

Print identifier.

Check i.

Check {| name:="123"; key:=3 |}.
Check "234".
Compute (match i with
         | {| name := a; key := b |} => (a,b)
        end).
Compute "123".
