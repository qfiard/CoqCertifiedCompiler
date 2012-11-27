Require Import ssreflect ssrbool eqtype ssrnat.
Require Import ListSet.

Module DeBruijnTerms.

Section Declaration.

Inductive DBT :=
| Var (x:nat) : DBT
| Fun (x:nat) (t:DBT) : DBT
| Appl (t:DBT) (u:nat) : DBT.

(* This lemma is required for the definition of natural integer sets *)
Lemma nat_unicity : forall x y:nat, {x = y} + {x <> y}.
Proof.
  move/(_ nat_eqType):eqVneq=> h.
  move => x y.
  move/(_ x y):h => h.
  case:h => h.
  left.
  done.
  right.

  (* to be continued *)
Qed.

Definition free_variables (t:DBT) : set nat.
Proof.
  (* Cas d'une variable *)
  elim:t.
  move => x.
  move/(_ nat):empty_set => s.
  move:set_add => h.
  move/(_ nat):h => h.
  apply:(x::s).
  
  (* Cas d'une fonction *)

Defined.

Fixpoint closed (t:DBT) : Prop := 
  match t with
    | Var x => false
    | Fun x t => false
    | 

End DeBruijnTerms.