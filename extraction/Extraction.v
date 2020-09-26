(* *********************************************************************)
(*                                                                     *)
(*              The L2C verified compiler                              *)
(*                                                                     *)
(*            L2C Group, Tsinghua University                           *)
(*                                                                     *)
(*  Copyright Tsinghua University.  All rights reserved.  This file is *)
(*  distributed under the terms of the GNU General Public License as   *)
(*  published by the Free Software Foundation, either version 2 of the *)
(*  License, or (at your option) any later version.  This file is also *)
(*  distributed under the terms of the INRIA Non-Commercial License    *)
(*  Agreement.                                                         *)
(*                                                                     *)
(* *********************************************************************)

Require AST.
Require Coqlib.
Require String.
Require Tree.
Require Parser.
Require Tokenizer.

Require Errors.
Require List.
Require Integers.
Require Floats.
Require Maps.
Require Bool.
Require Datatypes.

Require Asm.
Require AsmGen.
Require Extractor.
Require TransUtil.
Require TransExpression.
Require TransProtoInfo.
Require TransLayerBlock.
Require TransPin.
Require TransCellAlpha.
Require TransBranchInfo.
Require TransLayerStatement.
Require TransProtoStatement.

Require Types.
Require Typing.

(* Standard lib *)
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

(* AST *)
Extract Constant AST.ident_of_string =>
  "fun s -> Camlcoq.intern_string (Camlcoq.camlstring_of_coqstring s)".

(* Avoid name clashes *)
Extraction Blacklist List String Int.

(* Cutting the dependancy to R. *)
Extract Inlined Constant Fcore_defs.F2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.FF2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.B2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.round_mode => "fun _ -> assert false".
Extract Inlined Constant Fcalc_bracket.inbetween_loc => "fun _ -> assert false".

(* Extract Constant Lident.string_of_positive => 
  "fun i -> Camlcoq.coqstring_of_camlstring(string_of_int (Int32.to_int (Camlcoq.P.to_int32 i)))".
Extract Constant Lident.intern_string => 
  "fun s -> Camlcoq.intern_string (Camlcoq.camlstring_of_coqstring s)".
Extract Constant Lident.extern_atom => 
  "fun id -> Camlcoq.coqstring_of_camlstring (Camlcoq.extern_atom id)". *)

Cd "extraction".
Recursive Extraction Library Coqlib.

Recursive Extraction Library AST.
Recursive Extraction Library Errors.
Recursive Extraction Library List.
Recursive Extraction Library Integers.
Recursive Extraction Library Floats.
Recursive Extraction Library Maps.
Recursive Extraction Library Bool.
Recursive Extraction Library Coqlib.
Recursive Extraction Library Datatypes.

Set Extraction KeepSingleton.

Extract Constant Tree.str => "string".
Recursive Extraction Library Tree.

Extract Constant Tokenizer.str => "string".
Extract Constant Parser.intern_string =>
  "Obj.magic (fun s -> Camlcoq.intern_string s)".
Extract Constant Parser.ocaml_string =>
  "(fun s -> Camlcoq.camlstring_of_coqstring s)".
Extraction "Parser.ml" Parser.root Tokenizer.get_token.

Extraction Library Asm.
Extraction Library AsmGen.
Extraction Library Extractor.

Extract Constant TransUtil.bool_of_str => 
  "fun s -> bool_of_string s".
Extract Constant TransUtil.int_of_str => 
  "fun s -> Camlcoq.coqint_of_camlint(Int32.of_string s)".
Extract Constant TransUtil.char_of_str => 
  "fun s -> Camlcoq.coqint_of_camlint (Int32.of_int (int_of_char s.[0]))".

Extraction Library TransUtil.
Extraction Library TransExpression.
Extraction Library TransBranchInfo.
Extraction Library TransProtoStatement.
Extraction Library TransLayerStatement.
Extraction Library TransProtoInfo.
Extraction Library TransLayerBlock.
Extraction Library TransPin.
Extraction Library TransCellAlpha.

Extract Constant Types.ocaml_string =>
  "(fun s -> Camlcoq.camlstring_of_coqstring s)".
Extract Constant Types.coq_string =>
  "(fun s -> Camlcoq.coqstring_of_camlstring s)".
Recursive Extraction Library Types.
Recursive Extraction Library Typing.