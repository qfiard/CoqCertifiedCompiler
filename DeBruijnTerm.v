Require Import ssreflect ssrbool eqtype ssrnat.
Require Import ListSet.

Module DeBruijnTerms.

Section Declaration.

Inductive DBT :=
| Var (x:nat) : DBT
| Fun (t:DBT) : DBT
| Appl (t:DBT) (u:DBT) : DBT.

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
  move:h.
  move/eqP.
  done.
Qed.

(* Definition set_substract_one (s:set nat) : set nat. *)

(*
Definition 

Definition free_variables (t:DBT) : set nat.
Proof.
  (* Cas d'une variable *)
  elim:t.
  move => x.
  move/(_ nat):empty_set => s.
  move:set_add => h.
  move/(_ nat):h => h.
  apply:h.
  move:nat_unicity => h.
  done.
  done.
  done.
  
  (* Cas d'une fonction *)
  move => t free_t.
  move:set_remove => h.
  move/(_ nat):h => h.
  apply:h.
  move:nat_unicity => h.
  done.
  apply:0.
  done.

  (* Cas d'une application *)

  done.
Defined.
*)

Definition heredity_n_k (f:nat -> nat -> Prop) : Prop := forall n k:nat, f n k -> f (n+1) k.

Lemma stupid : forall x y:nat, x<y -> x<y+1.
Admitted.

Definition n_k_free (t:DBT) : { f:(nat->nat->Prop) | heredity_n_k f}.
Proof.
  elim:t.

  (* Variable *)
  move => x.
  exists (fun n:nat => (fun k:nat => ((x<k)\/(x<n)))).
  rewrite/heredity_n_k.
  move => n k h.
  case:h => h.
  by left.
  right.
  move/(_ x n):stupid => h1.
  apply:h1.
  done.

  (* Fonction *)
  move => t ih.
  case:ih => f p.
  exists (fun n => (fun k => (f n (k+1)))).
  move:p.
  rewrite/heredity_n_k.
  move => ih n k h.
  move/(_ n (k+1)):ih => ih.
  apply:ih.
  done.

  (* Application *)
  move => t iht u ihu.
  case:iht => ft pt.
  case:ihu => fu pu.

  exists (fun n => (fun k => ((ft n k)/\(fu n k)))).

  move:pt pu.
  rewrite/heredity_n_k.
  move => iht ihu n k h.
  move/(_ n k): iht => iht.
  move/(_ n k): ihu => ihu.
  split.
  apply:iht.
  by case:h => h.
  apply:ihu.
  by case:h => h.
Defined.

Fixpoint n_free (n:nat) (t:DBT) : Prop.
Proof.
  move:n_k_free => h.
  
  apply:h.
  apply:0.
  apply:t.
  apply:n.
Defined.

Lemma n_k_free_heredity : forall n k:nat, forall t:DBT, n_k_free n t k -> n_k_free (n+1) t k.
Proof.
  move => n k t.
  elim:t.

  (* Variable *)
  move => x.
  rewrite/n_k_free.

  move => h.
  elim:t.
Qed.

Lemma n_free_heredity : forall n:nat, forall t:DBT, n_free n t -> n_free (n+1) t.
Proof.
  move => n t h.
  rewrite/n_free.
  simpl.
  elim.
  

Qed.



Fixpoint closed (t:DBT) : Prop := 
  match t with
    | Var x => false
    | Fun x t => false
    | 

End DeBruijnTerms.