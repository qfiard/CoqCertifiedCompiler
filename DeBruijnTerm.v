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
(*
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

<<<<<<< HEAD
Definition pair_left: (nat*DBT) -> nat.
=======
Definition substitution : {f:DBT | is_function f} -> DBT -> DBT.
Admitted.
(*
>>>>>>> origin/master
Proof.
  move => p.
<<<<<<< HEAD
  case:p => i t.
  apply:i.
Defined.
=======
  move/(_ f):function_arg => t.

  move/(_ t 0 u):replace => h.
  apply:h.
Defined.*)
>>>>>>> origin/master

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

(*
Fixpoint equals (a:DBT) (b:DBT) : Prop :=
match a,b with
|_, _ => False
end.
  move=> a b.
  elim a.
  elim b.

Defined.*)

Inductive reduces_in_one_step : DBT -> DBT -> Prop :=
| Lambda_reduction : forall t u, reduces_in_one_step (Appl (Fun t) u) (substitute_one t 0 u)
| Rep_Lambda : forall t u, reduces_in_one_step t u ->reduces_in_one_step (Fun t) (Fun u)
| Rep_Appl_left : forall t u v, reduces_in_one_step t u ->reduces_in_one_step (Appl t v) (Appl u v)
| Rep_Appl_right : forall t u v, reduces_in_one_step t u ->reduces_in_one_step (Appl v t) (Appl v u).

Inductive reduces_in_few_steps : DBT -> DBT -> Prop :=
| Reflexivity : forall t, reduces_in_few_steps t t
| Forward : forall t u v, reduces_in_few_steps t u -> reduces_in_one_step u v->reduces_in_few_steps t v.

Lemma context_closed_left: forall t u: DBT, reduces_in_few_steps t u -> forall v:DBT, reduces_in_few_steps (Appl t v) (Appl u v).
Proof.
  move => t u.
  elim.
  by move=>t0 v;apply Reflexivity.
  move=> {t u} t u v0 h0 h1 h2 v.
  have h3:reduces_in_one_step (Appl u v) (Appl v0 v).
  by apply Rep_Appl_left.
  move/(_ v):h1=>h1.
  move:h1 h3.
  by apply Forward.
Qed.

Lemma context_closed_right: forall t u: DBT, reduces_in_few_steps t u -> forall v:DBT, reduces_in_few_steps (Appl v t) (Appl v u).
Proof.
  move => t u.
  elim.
  by move=>t0 v;apply Reflexivity.
  move=> {t u} t u v0 h0 h1 h2 v.
  have h3:reduces_in_one_step (Appl v u) (Appl v v0).
  by apply Rep_Appl_right.
  move/(_ v):h1=>h1.
  move:h1 h3.
  by apply Forward.
Qed.

Lemma context_closed_Lambda: forall t u: DBT, reduces_in_few_steps t u -> reduces_in_few_steps (Fun t) (Fun u).
Proof.
  move => t u.
  elim.
  by move=>t0;apply Reflexivity.
  move=> {t u} t u u0 h0 h1 h2.
  have h3:reduces_in_one_step (Fun u) (Fun u0).
  by apply Rep_Lambda.
  move:h1 h3.
  by apply Forward.
Qed.
*)


Inductive instruction :Type :=
| Access : nat->instruction
| Grab : instruction
| Push : list instruction->instruction.

Definition code :Type :=
list instruction.

Inductive environment:Type :=
Node :list (code*environment)->environment.

Definition stack :Type :=
environment.

Inductive state:Type :=
| None : state
| State : code->environment->stack->state.

Definition execute_one:state->state.
Proof.
move=>st.
case st.
(*st:None*)
apply None.
(*st:State c e s*)
move=>c e s.
case c.
(**c:empty list*)
apply None.
(**c:hdc::tlc*)
move=>hdc tlc.
case hdc.
(***hdc:Access n*)
move=>n.
case e.
move=>le.
case le.
(****le:empty list*)
apply None.
(****le:hdle::tlle*)
move=>hdle tlle.
case n.
(*****n:0*)
case hdle.
move=>fsthdle sndhdle.
apply (State fsthdle sndhdle s).
(*****n!=0*)
move=>nn.
apply (State ((Access (nn-1))::tlc) (Node tlle) s).
(***hdc:Grab*)
case s.
move=>ls.
case ls.
(****ls:empty list*)
apply None.
(****ls:hdls::tlls*)
move=>hdls tlls.
case e.
move=>le.
apply (State tlc (Node (hdls::le)) (Node tlls)).
(***hdc:Push li*)
move=>li.
case s.
move=>ls.
apply (State tlc e (Node ((li,e)::ls))).
Qed.

Definition compile : DBT -> code.
Proof.
  move => t.
  elim:t.

  (* Variable *)
  move => x.
  apply:((Access x)::nil).

  (* Fonction *)
  move => t ih.
  apply:(Grab::ih).

  (* Application *)
  move => t iht u ihu.
  apply:((Push ihu)::iht).
Defined.

Definition execute :state->state.
Proof.
  move => s.
  case:s.
  apply None.
  move => c e s.
  case : c.
  apply : (State nil e s).
  move=>hdc tlc.
  (*cas : Access n*)
  case : hdc.
  move => n.
  elim n.
  (**cas : n=0*)
  case e.
move=>le.
case le.
apply None.
move=>z tlle.
case z.
move=>z1 z2.
elim (State z1 z2 s).
(***cas : None*)
apply None.
move=>

apply None.
move=>z tlle.
case z.
move=>z1 z2 hi.
apply 
  case : e.
  move=>le.
  case : le.
  apply None.
  move=>z tlle.
  case z.
  move=>z1 z2.
  apply : (execute (State z1 z2 s)).

st.c <- fst(hd(env_list(st.e)));
st.e <- snd(hd(env_list(st.e)));
execute st;

  match hdc with
  |Access n=>apply State nil e s
  |Grab=>apply State nil e s
  |Push=>apply State nil e s

move/(_ c e s  ).
move=>st.
rewrite/(_ state->u).
st.
