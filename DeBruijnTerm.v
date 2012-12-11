Require Import ssreflect ssrbool eqtype ssrnat Arith.
Require Import List ListSet.

Module DeBruijnTerms.

Section Declaration.

Inductive DBT:Type :=
| Var : nat -> DBT
| Fun : DBT -> DBT
| Appl : DBT -> DBT -> DBT.

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

Lemma lt_succ : forall x y:nat, x<y -> x<y+1.
Proof.
  move => x y.
  move/(_ x y 1):ltn_addr.
  done.
Qed.

Definition n_k_free (t:DBT) : { f:(nat->nat->bool) | heredity_n_k f}.
Proof.
  elim:t.

  (* Variable *)
  move => x.
  exists (fun n:nat => (fun k:nat => ((x<k)||(x<n)))).
  rewrite/heredity_n_k.
  move => n k.
  move/orP.
  case.
  move => -> //=.
  move => h.
  have h2:x<n+1.
  move/(_ x n):lt_succ => h1.
  apply:h1.
  done.
  move:h2 => ->.
  rewrite orbT.
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

  exists (fun n => (fun k => ((ft n k)||(fu n k)))).

  move:pt pu.
  rewrite/heredity_n_k.
  move => iht ihu n k h.
  move/(_ n k): iht => iht.
  move/(_ n k): ihu => ihu.

  move/orP:h => h.

  case:h => h.

  have h1: ft (n+1) k.
  apply:iht.
  done.

  move:h1 => -> //=.

  have h1 : fu (n+1) k.
  apply:ihu => //.

  move:h1 => ->.
  rewrite orbT.
  done.
Defined.

Definition n_free (t:DBT) : { f:nat -> bool | forall n:nat, forall t:DBT, f n -> f (n+1) }.
Proof.
  move:n_k_free => h.
  case:h.
  done.
  move => n_k_free.
  rewrite/heredity_n_k.
  move => p.
  exists (fun n => (n_k_free n 0)).

  move => n.
  move/(_ n 0):p => p.
  done.
Defined.

Fixpoint closed (t:DBT) : bool.
Proof.
  move:n_free => h.
  case:h.
  done.
  move => n p.
  apply:n 0.
Defined.

Definition t1:DBT := Var 0.
Definition t2:DBT := Fun (Var 0).
Definition t3:DBT := Fun (Var 1).

Compute closed t1.
Compute closed t2.
Compute closed t3.

Definition is_function (f:DBT) : bool :=
  match f with
    | Fun t => true
    | _ => false
  end.

Theorem is_function_eq : forall f, is_function f <-> exists x, f = Fun x.
Proof.
  split.
  case:f.
  rewrite/is_function.
  done.
  move => d p.
  exists d.
  done.
  rewrite/is_function.
  done.

  move => p.
  elim:p.
  move => x h.
  rewrite h.
  rewrite/is_function.
  done.
Qed.

Definition function_arg (f:DBT) : DBT :=
  match f with
    | Fun t => t
    | _ => f
  end.

Definition free_le (f:DBT) : nat -> bool.
Proof.
  elim:f.
  move=>m n.
  apply : (m<n).
  move=>t hr n.
  apply : (hr (n+1)).
  move=>t1 hr1 t2 hr2 n.
  have b:bool.
  apply : (hr1 n).
  have c:bool.
  apply : (hr2 n).
  apply : (b && c).
Qed.

(* add_n_to_free_k t n k  adds a constant value n to all free variables >= k in t *)
Definition add_n_to_free_k : DBT -> nat -> nat -> DBT.
Proof.
  move => t.
  elim:t.

  (* Variable *)
  move => x n k.
  apply:(if (k<=x) then (Var (x+n)) else Var (x)).


  (* Fonction Fun t*)
  move => t ih n k.
  apply: Fun (ih n (k+1)).

  (* Application Appl t1 t2 *)
  move => t1 ih1 t2 ih2 n k.
  apply: Appl (ih1 n k) (ih2 n k).
Defined.

(* add_n_to_free adds a constant value n to all the free variables of the argument DBT *)
Definition add_n_to_free : DBT -> nat -> DBT.
Proof.
  move => t n.
  apply:add_n_to_free_k t n 0.
Defined.

Compute (add_n_to_free t2 10).
Compute (add_n_to_free t3 10).

Definition shift : DBT -> DBT.
Proof.
  move => t.
  apply:add_n_to_free t 1.
Defined.

Compute (shift t3).

Definition substitute_one : DBT -> nat -> DBT -> DBT.
Proof.
  move => t.
  
  elim:t.

  (* Variable *)
  move => x n u.
  apply:(if (n==x) then u else (Var x)).

  (* Function Fun t1*)
  move => t1 ih n u.
  apply:(Fun(ih (n+1) (shift u))).
  

  (* Application Appl t1 t2*)
  move => t1 ih1 t2 ih2 n u.
  apply:(Appl (ih1 n u) (ih2 n u)).
Defined.

Theorem substitute_in_closed : forall f:{f:DBT | is_function f}, forall u:DBT, closed (element f) ->  substitution f u = (element f).
Proof.
  move => f u.
  rewrite/element.
Qed.

Definition n_free_list : list DBT -> nat -> bool.
Proof.
  move => l n.
  elim:l.
  apply:true.
  
  move => t s ih.
  
  have test:bool.

  move/(_ t):n_free => h.
  case:h => f _.
  apply:f.
  apply:n.

  apply:(test&&ih).
Defined.

Definition list_from_list_of_pairs : list (nat*DBT) -> list DBT.
Proof.
  move => l.

  elim:l.

  apply:nil.

  move => pair s ih.
  case:pair => n t.
  apply:(t::ih).
Defined.

Definition substitute : DBT -> list (nat*DBT) -> DBT.
Proof.
  move => t l.
  elim:l.

  (* Empty list *)
  apply:t.

  (* Hérédité l = pair::s *)

  move => pair s ih.

  case:pair => i ui.
  apply:substitute_one ih i ui.
Defined.

Theorem substitute_nil: forall t:DBT, substitute t nil = t.
Proof.
  move => t.
  simpl.
  done.
Qed.

Definition pair_left: (nat*DBT) -> nat.
Proof.
  move => p.
  case:p => i t.
  apply:i.
Defined.

Definition pair_right: (nat*DBT) -> DBT.
Proof.
  move => p.
  case:p => i t.
  apply:t.
Defined.

Theorem substitute_one_elem : forall t x:DBT, forall i:nat, substitute t ((i,x)::nil) = substitute_one t i x.
Proof.
  move => t x i.
  simpl.
  done.
Defined.

Theorem substitute_rec : forall t x:DBT, forall s:(list (nat*DBT)), forall i:nat, n_free_list (list_from_list_of_pairs s) i -> substitute t ((i,x)::s) = substitute_one (substitute t s) i x.
Admitted.

End DeBruijnTerms.