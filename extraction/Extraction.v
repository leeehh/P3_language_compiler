(**************************************
  Filename:  Extraction.v
  Project:   P3 Compilers
  Author:    Ling.Li
  Date:      2018.06.20
**************************************)

Require String.
Require Tree.
Require Parser.
Require Tokenizer.
Require Integers.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive List.list => "list" [ "[]" "(::)" ].

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extraction Blacklist List String Int.

Cd "extraction".

Recursive Extraction Library Coqlib.
Recursive Extraction Library Integers.

Set Extraction KeepSingleton.

Extract Constant Tree.str => "string".
Recursive Extraction Library Tree.

Extract Constant Tokenizer.str => "string".
Extract Constant Parser.intern_string =>
  "Obj.magic (fun s -> Camlcoq.intern_string s)".
Extract Constant Parser.ocaml_string =>
  "(fun s -> Camlcoq.camlstring_of_coqstring s)".
Extraction "Parser.ml" Parser.root Tokenizer.get_token.
