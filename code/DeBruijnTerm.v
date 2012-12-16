Require Import ssreflect ssrbool eqtype ssrnat Arith.
Require Import List ListSet.

Module DeBruijnTerms.

Section Declaration.

(*
 * Définition inductive des termes de De Bruijn (DBT)
 *)
Inductive DBT:Type :=
| Var : nat -> DBT
| Fun : DBT -> DBT
| Appl : DBT -> DBT -> DBT.

(*
 * Propriété que doit vérifier une fonction de deux variables pour être héréditaire par rapport à sa première variable
 *)
Definition heredity_n_k (f:nat -> nat -> Prop) : Prop := forall n k:nat, f n k -> f (n+1) k.

(*
 * Un lemme très simple, croissance de la relation inférieur
 *)
Lemma lt_succ : forall x y:nat, x<y -> x<y+1.
Proof.
  move => x y.
  move/(_ x y 1):ltn_addr.
  done.
Qed.

(*
 * n_k_free construit, étant donné un terme t, une fonction qui pour tout n, k, renvoie
 * true si et seulement si les variables libres de t sont < n, sachant que toutes les
 * variables < k sont liées.
 *
 * On prouve en parallèle l'hérédité de la fonction renvoyé, tel que défini précédemment
 *)
Definition n_k_free (t:DBT) : nat->nat->bool.
Proof.
  elim:t.

  (* Variable *)
  move => x n k.
  apply:((x<k)||(x<n)).

  (* Fonction *)
  move => t ih n k.
  apply:(ih n (k+1)).

  (* Application *)
  move => t iht u ihu n k.
  apply:((iht n k)&&(ihu n k)).
Defined.

Theorem n_k_free_heredity : forall t:DBT, heredity_n_k (n_k_free t).
Proof.
  move => t.
  rewrite /n_k_free.
  rewrite /heredity_n_k.
  elim t.

  (* Variable *)
  simpl.
  move => n p q.
  move/orP.
  move => h1.
  case:h1 => h1.
  move:h1 => -> //=.
  move/(_ n p):lt_succ => h2.
  have h3 : n<p+1.
  apply:h2.
  done.
  move:h3 => ->.
  rewrite orbT.
  done.

  (* Fonction *)
  simpl.
  move => d ih n k.
  move/(_ n (k+1)):ih => ih.
  apply:ih.

  (* Application *)
  simpl.
  move => u ihu v ihv n k h.
  move/andP:h => h.
  case:h => h1 h2.
  move/(_ n k):ihu => ihu.
  move/(_ n k):ihv => ihv.
  have left:DBT_rec (fun _ : DBT => nat -> nat -> bool)
     (fun x n0 k0 : nat => (x < k0) || (x < n0))
     (fun (_ : DBT) (ih : nat -> nat -> bool) (n0 k0 : nat) => ih n0 (k0 + 1))
     (fun (_ : DBT) (iht : nat -> nat -> bool) (_ : DBT)
        (ihu0 : nat -> nat -> bool) (n0 k0 : nat) => 
      iht n0 k0 && ihu0 n0 k0) u (n + 1) k.
  apply:ihu.
  apply:h1.
  have right:DBT_rec (fun _ : DBT => nat -> nat -> bool)
     (fun x n0 k0 : nat => (x < k0) || (x < n0))
     (fun (_ : DBT) (ih : nat -> nat -> bool) (n0 k0 : nat) => ih n0 (k0 + 1))
     (fun (_ : DBT) (iht : nat -> nat -> bool) (_ : DBT)
        (ihu0 : nat -> nat -> bool) (n0 k0 : nat) => 
      iht n0 k0 && ihu0 n0 k0) v (n + 1) k.
  apply:ihv.
  apply:h2.
  move:left => ->.
  move:right => ->.
  done.
Qed.

Theorem n_k_free_heredity2 : forall t:DBT, forall n k:nat, n_k_free t n k -> n_k_free t n (k+1).
Proof.
  move => t.
  rewrite /n_k_free.
  elim:t.

  (* Variable *)
  move => x n k.
  simpl.
  move/orP.
  move => h1.
  case:h1 => h1.
  move/(_ x k):lt_succ => h2.
  have h3:x<k+1.
  apply:h2.
  done.
  move:h3 => -> //=.
  move:h1 => ->.
  rewrite orbT.
  done.

  (* Function *)
  simpl.
  move => t ih n k.
  move/(_ n (k+1)):ih => ih.
  apply:ih.

  (* Application *)
  simpl.
  move => t iht u ihu n k.
  move/(_ n k):iht => iht.
  move/(_ n k):ihu => ihu.
  move/andP => h1.
  case:h1 => h1 h2.
  have h3:DBT_rec (fun _ : DBT => nat -> nat -> bool)
     (fun x n0 k0 : nat => (x < k0) || (x < n0))
     (fun (_ : DBT) (ih : nat -> nat -> bool) (n0 k0 : nat) => ih n0 (k0 + 1))
     (fun (_ : DBT) (iht0 : nat -> nat -> bool) (_ : DBT)
        (ihu0 : nat -> nat -> bool) (n0 k0 : nat) => 
      iht0 n0 k0 && ihu0 n0 k0) t n (k + 1).
  apply:iht.
  done.
  have h4:DBT_rec (fun _ : DBT => nat -> nat -> bool)
     (fun x n0 k0 : nat => (x < k0) || (x < n0))
     (fun (_ : DBT) (ih : nat -> nat -> bool) (n0 k0 : nat) => ih n0 (k0 + 1))
     (fun (_ : DBT) (iht0 : nat -> nat -> bool) (_ : DBT)
        (ihu0 : nat -> nat -> bool) (n0 k0 : nat) => 
      iht0 n0 k0 && ihu0 n0 k0) u n (k + 1).
  apply:ihu.
  done.
  rewrite h3.
  rewrite h4.
  done.
Qed.

(*
 * n_free t n renvoie true si et seulement si l'ensemble des variables libres de t
 * sont inférieurs strictement à n.
 *
 * Là encore, on démontre en parallèle l'hérédité de cette propriété
 *)
Definition n_free (t:DBT) : nat -> bool.
Proof.
  move => n.
  move/(_ t n O):n_k_free => h.
  done.
  (*
  move => n_k_free.
  rewrite/heredity_n_k.
  move => p.
  exists (fun n => (n_k_free n 0)).

  move => n.
  move/(_ n 0):p => p.
  done.
*)
Defined.

Theorem n_free_heredity : forall t:DBT, forall n:nat, n_free t n -> n_free t (n+1).
Proof.
  move => t n.
  rewrite /n_free.
  move/(_ t n 0):n_k_free_heredity => h1.
  done.
Qed.

(*
 * Un terme t est clos si et seulement si n_free t 0 = true
 *)
Definition closed : DBT -> bool.
Proof.
  move => t.
  move/(_ t 0):n_free => b.
  done.
Defined.

(*
 * Quelques tests élémentaires
 *)
Definition t1:DBT := Var 0.
Definition t2:DBT := Fun (Var 0).
Definition t3:DBT := Fun (Var 1).

Compute closed t1.
Compute closed t2.
Compute closed t3.

(*
(*
 * Quelques fonctions utiles dans le cas d'une fonction.
 *)
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
*)

(*
 * add_n_to_free_k t n k  ajoute une valeur constante n à toutes les variables libres
 * de t, sachant que toutes les variables < k sont liées 
 *)
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

(*
 * add_n_to_free t n ajoute n à toutes les variables libres de t
 *)
Definition add_n_to_free : DBT -> nat -> DBT.
Proof.
  move => t n.
  apply:add_n_to_free_k t n 0.
Defined.

Compute (add_n_to_free t2 10).
Compute (add_n_to_free t3 10).

(*
 * shift incrémente toutes les variables libres d'un DBT
 *)
Definition shift : DBT -> DBT.
Proof.
  move => t.
  apply:add_n_to_free t 1.
Defined.

Compute (shift t3).

(*
 * Substitution simple dans un DBT. Étant donné une variable libre et un terme, on substitue ce terme
 * à chaque occurence de la variable libre.
 *)
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

Lemma leq_neq : forall x n:nat, x<n -> (n==x)=false.
Admitted.

Lemma leq_1 : forall x n:nat, x<0+1 -> x<n+1.
Admitted.

Lemma n_k_free_arg1 : forall  t:DBT, forall n k:nat, n_k_free (Fun t) n k -> n_k_free t (n+1) (k+1).
Proof.
  move => t.
  elim:t.

  (* Variable *)
  simpl.
  move => x n k.
  move/orP.
  case => h1.
  
  rewrite h1.
  done.
  move/(_ x n):lt_succ => h2.
  have h3:x<n+1.
  apply:h2.
  done.
  rewrite h3.
  rewrite orbT.
  done.

  (* Fonction *)
  rewrite /n_k_free.
  simpl.

  move => t ih n k.
  move/(_ n (k+1)):ih => ih.
  apply:ih.

  (* Application *)
  move => t iht u ihu n k.
  move/(_ n k):iht => iht.
  move/(_ n k):ihu => ihu.
  simpl.
  move/andP.
  case => h1 h2.
  have h3:n_k_free t (n + 1) (k + 1).
  apply:iht.
  done.
  have h4:n_k_free u (n + 1) (k + 1).
  apply:ihu.
  done.
  rewrite h3.
  rewrite h4.
  done.
Qed.

Lemma n_free_arg1 : forall t:DBT, forall n k:nat, n_free (Fun t) n -> n_free t (n+1).
Admitted.

Lemma n_free_arg2 : forall t1 t2:DBT, forall n:nat, n_free (Appl t1 t2) n -> (n_free t1 n)/\(n_free t2 n).
Admitted.

Theorem substitute_with_free_variables_above : forall t u:DBT, forall n:nat, n_free t n -> substitute_one t n u = t.
Proof.
  move => t.
  elim:t.

  (* Variable *)
  rewrite /n_free.
  rewrite /n_k_free.
  rewrite /substitute_one.
  simpl.
  move => x u n h1.
  move/(_ x n):leq_neq => h2.
  have h3:(n==x)=false.
  apply:h2.
  done.
  rewrite h3.
  done.

  (* Fonction *)
  simpl.
  move => t ih u n.
  move/(_ t n):n_free_arg1 => h1.
  move/(_ (shift u) (n+1)):ih => ih.
  move => h3.
  have h4:substitute_one t (n + 1) (shift u) = t.
  apply:ih.
  apply:h1.
  done.
  done.
  rewrite h4.
  done.

  (* Application *)
  simpl.
  move => t1 iht1 t2 iht2 u n h1.
  move/(_ u n):iht1 => iht1.
  move/(_ u n):iht2 => iht2.
  move/(_ t1 t2 n):n_free_arg2 => h2.
  have h3:n_free t1 n /\ n_free t2 n.
  apply:h2.
  done.
  have h4: substitute_one t1 n u = t1.
  apply:iht1.
  case:h3 =>//.
  have h5: substitute_one t2 n u = t2.
  apply:iht2.
  case:h3 =>//.
  rewrite h4.
  rewrite h5.
  done.
Qed.

Theorem substitute_in_closed : forall t u:DBT, forall n:nat, closed t ->  substitute_one t n u = t.
Proof.
  move => t u n.
  rewrite /closed.
  move => h1.
  have h2: n_free t n.
  elim:n.
  done.

  move =>  n.
  move/(_ t n):n_free_heredity => h2.
  move/(_ n):addn1 => h3.
  rewrite -h3.
  done.

  move/(_ t u n):substitute_with_free_variables_above => h3.
  apply:h3.
  done.
Qed.

Definition n_free_list : list DBT -> nat -> bool.
Proof.
  move => l n.
  elim:l.
  apply:true.
  
  move => t s ih.
  
  have test:bool.

  move/(_ t):n_free => h.
  apply:h.
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

Definition substitute_in_nat_DBT_list : list (nat*DBT) -> nat -> DBT -> list (nat*DBT).
Proof.
  move => l.
  elim:l.
  
  (* Liste vide *)
  move => n u.
  apply:nil.

  (* Suite *)
  move => p s ih n u.
  case:p => x t.
  move/(_ n u):ih => ih.
  apply:((x,substitute_one t n u)::ih).
Defined.

Fixpoint reverse_aux (A:Type) (l1:list A) (l2:list A) : list A :=
  match l1 with
    | nil => l2
    | x::s => reverse_aux A s (x::l2)
  end.

Definition reverse  (A:Type) (l1:list A) : list A := reverse_aux A l1 nil.

Compute (reverse nat (1::2::3::nil)).

Definition substitute_aux (t:DBT) (l:list (nat*DBT)) : DBT.
Proof.
  elim:l.

  (* Empty list *)
  apply:t.

  (* Hérédité l = pair::s *)

  move => pair s ih.

  case:pair => i ui.
  apply:substitute_one ih i ui.
Defined.

(*
 * On commence par inverser la liste de substitution, puis on effectue les substitutions en tant que telles.
 *)

Definition substitute (t:DBT) (l:list (nat*DBT)) : DBT.
Proof.
  have l2:list (nat*DBT).
  apply:(reverse (nat*DBT) l).
  apply:(substitute_aux t l2).
Defined.

Theorem substitute_nil: forall t:DBT, substitute t nil = t.
Proof.
  done. (* La propriété est prouvé automatiquement par Coq *)
Qed.

Definition pair_left: (nat*DBT) -> nat.
Proof.
  move => p.
  case:p => i t.
  apply : i.
Defined.

Definition pair_right: (nat*DBT) -> DBT.
Proof.
  move => p.
  case:p => i t.
  apply:t.
Defined.

Theorem substitute_one_elem : forall t x:DBT, forall i:nat, substitute t ((i,x)::nil) = substitute_one t i x.
Proof.
  done. (* La propriété est prouvé automatiquement par Coq *)
Defined.

Theorem substitute_rec : forall t x:DBT, forall s:(list (nat*DBT)), forall i:nat, n_free_list (list_from_list_of_pairs s) i -> substitute t ((i,x)::s) = substitute_one (substitute t s) i x.
Admitted.

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

(*
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

*)