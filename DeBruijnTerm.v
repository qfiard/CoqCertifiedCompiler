Require Import ssreflect ssrbool eqtype ssrnat.

Module DeBruijnTerms.

Section Declaration.

Inductive DBT :=
| Var (x:nat) : DBT
| Fun (x:nat) (t:DBT) : DBT
| Appl (t:DBT) (u:nat) : DBT.

End DeBruijnTerms.