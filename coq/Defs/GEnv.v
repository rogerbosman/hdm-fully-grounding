(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Defs.List.
Require Import Defs.Set.

(*** List rels *)
(* Module Type AtomList_rel <: list_rel. *)
(*   Definition elt : Type := atom. *)
(* End AtomList_rel. *)

(* Module Type AtomList_subrel. *)
(*   Include AtomList_rel. *)
(*   Parameter R_empty : forall (l : list atom), R [] l. *)
(* End AtomList_subrel. *)

(*** GEnv_(rels) *)
Module Type GEnv.
  Parameter E : Type.
  Parameter S : Type.
  Parameter O : Type.

  Parameter Empty :                 E.
  Parameter Skol  : E -> atom ->      E.
  Parameter Aa    : E -> list atom -> E.
  Parameter Var   : E -> atom -> S ->  E.
  Parameter Obj   : E -> O ->         E.

  Parameter oneS : atom ->      E.
  Parameter oneA : list atom -> E.
  Parameter oneX : atom -> S ->  E.
  Parameter oneO : O ->         E.

  Parameter app : E -> E -> E.

  Parameter E_cons_one_s : forall (e : E) (skA : atom),
      Skol e skA = app e (oneS skA).
  Parameter E_cons_one_a : forall (e : E) (a : list atom),
      Aa e a = app e (oneA a).
  Parameter E_cons_one_x : forall (e : E) (x : atom) (s : S),
      Var e x s = app e (oneX x s).
  Parameter E_cons_one_o : forall (e : E) (o : O),
      Obj e o = app e (oneO o).

  Parameter E_app_nil_r : forall (e : E),
      app e Empty = e.
  Parameter E_app_nil_l : forall (e : E),
      app Empty e = e.
End GEnv.

Module Type GE_rel (L : atomlist_rel) (Import GE : GEnv).
  Parameter R : E -> E -> Prop.

  Parameter refl : Reflexive R.
  Parameter trans : Transitive R.

  Parameter proper : Proper (R ==> R ==> R) app.
  Parameter R_oneAa : forall (l1 l2 : list atom), L.R l1 l2 -> R (oneA l1) (oneA l2).
End GE_rel.

Module Type GE_subrel (L : atomlist_rel) (Import GE : GEnv).
  Include GE_rel L GE.
  Parameter R_empty : forall (e : E), R Empty e.
  Parameter R_emptyA : forall (e : E), R (oneA []) e.

  Parameter E_cons_anil : forall (ge : E),
      R ge (Aa ge []).
End GE_subrel.

Module Type GE_eqrel (L : atomlist_rel) (Import GE : GEnv).
  Include GE_rel L GE.
  Parameter symm : Symmetric R.
End GE_eqrel.

(*** GE facts *)
(** GE_subrel *)
Module GE_subrel_facts (L : atomlist_subrel) (Import GE : GEnv) (Import Rel : GE_subrel L GE).
  #[export] Hint Resolve refl : core.

  #[export] Instance GE_subrel_preorder : PreOrder R :=
    { PreOrder_Reflexive  := refl
    ; PreOrder_Transitive := trans
    }.

  #[export] Instance GE_subrel_cons_s_proper : Proper (R ==> eq ==> R) Skol.
  Proof. autounfold. intros. subst. do 2 rewrite E_cons_one_s. apply proper. assumption. reflexivity. Qed.
  #[export] Instance GE_subrel_cons_a_proper : Proper (R ==> L.R ==> R) Aa.
  Proof. autounfold. intros. subst. do 2 rewrite E_cons_one_a. apply proper. assumption. auto using R_oneAa. Qed.
  #[export] Instance GE_subrel_cons_x_proper : Proper (R ==> eq ==> eq ==> R) Var.
  Proof. autounfold. intros. subst. do 2 rewrite E_cons_one_x. apply proper. assumption. reflexivity. Qed.
  #[export] Instance GE_subrel_cons_o_proper : Proper (R ==> eq ==> R) Obj.
  Proof. autounfold. intros. subst. do 2 rewrite E_cons_one_o. apply proper. assumption. reflexivity. Qed.

  Theorem GE_subrel_app_r : forall (e1 e1' e2 : E),
      R e1 e1'
    -> R e1 (app e1' e2).
  Proof. intros. rewrite <- (E_app_nil_r e1). apply proper. assumption. apply R_empty. Qed.
  Theorem GE_subrel_app_l : forall (e1 e2 e2': E),
      R e2 e2'
    -> R e2 (app e1 e2').
  Proof. intros. rewrite <- (E_app_nil_l e2). apply proper. apply R_empty. assumption. Qed.
  #[export] Hint Resolve GE_subrel_app_r GE_subrel_app_l : core.

  Theorem GE_subrel_app_empty : forall (e1 e2 : E),
      R e1 e2
    -> R (Aa e1 []) e2.
  Proof. intros. rewrite <- (E_app_nil_r e2). rewrite E_cons_one_a. apply proper. assumption. apply R_emptyA. Qed.
  #[export] Hint Resolve GE_subrel_app_empty : core.

  Corollary GE_subrel_app_r' : forall (e1 e2 : E),
      R e1 (app e1 e2).
  Proof. intros. apply GE_subrel_app_r. reflexivity. Qed.
  Corollary GE_subrel_app_l' : forall (e1 e2 : E),
      R e2 (app e1 e2).
  Proof. intros. apply GE_subrel_app_l. reflexivity. Qed.
  #[export] Hint Resolve GE_subrel_app_r' GE_subrel_app_l' : core.

  Theorem GE_subrel_cons_s : forall (var : atom) (e e' : E),
      R e e'
    -> R e (Skol e' var).
  Proof. intros. rewrite E_cons_one_s. auto using GE_subrel_app_r. Qed.
  Theorem GE_subrel_cons_a : forall (e1 e2 : E) (l1 l2 : list atom),
      R e1 e2
    -> L.R l1 l2
    -> R (Aa e1 l1) (Aa e2 l2).
  Proof. intros. do 2 rewrite E_cons_one_a. assert (R (oneA l1) (oneA l2)). auto using R_oneAa. apply proper; assumption. Qed.
  Theorem GE_subrel_cons_x : forall (x : termvar) (s : S) (e e' : E),
      R e e'
    -> R e (Var e' x s).
  Proof. intros. rewrite E_cons_one_x. auto using GE_subrel_app_r. Qed.
  Theorem GE_subrel_cons_o : forall (o: O) (e e' : E),
      R e e'
    -> R e (Obj e' o).
  Proof. intros. rewrite E_cons_one_o. auto using GE_subrel_app_r. Qed.
  #[export] Hint Resolve GE_subrel_cons_s GE_subrel_cons_a GE_subrel_cons_x GE_subrel_cons_o : core.

  Corollary GE_subrel_cons_s' : forall (var : atom) (e : E),
      R e (Skol e var).
  Proof. intros. apply GE_subrel_cons_s. reflexivity. Qed.
  Corollary GE_subrel_cons_a' : forall (e : E) (l : list atom),
      R e (Aa e l).
  Proof. intros. rewrite E_cons_anil at 1. apply GE_subrel_cons_a. reflexivity. apply L.R_empty. Qed.
  Corollary GE_subrel_cons_x' : forall (x : termvar) (s : S) (e : E),
      R e (Var e x s).
  Proof. intros. apply GE_subrel_cons_x. reflexivity. Qed.
  Corollary GE_subrel_cons_o' : forall (o: O) (e : E),
      R e (Obj e o).
  Proof. intros. apply GE_subrel_cons_o. reflexivity. Qed.
  #[export] Hint Resolve GE_subrel_cons_s' GE_subrel_cons_a' GE_subrel_cons_x' GE_subrel_cons_o' : core.
End GE_subrel_facts.

(** GE_eqrel *)
Module GE_eqrel_facts (L : atomlist_rel) (Import GE : GEnv) (Import Rel : GE_eqrel L GE).
  #[export] Hint Resolve refl : core.
  #[export] Hint Resolve symm : core.

  #[export] Instance GE_eqrel_equivalence : Equivalence R :=
    { Equivalence_Reflexive  := refl
    ; Equivalence_Transitive := trans
    ; Equivalence_Symmetric  := symm
    }.

  #[export] Instance GE_eqrel_cons_s_proper : Proper (R ==> eq ==> R) Skol.
  Proof. autounfold. intros. subst. do 2 rewrite E_cons_one_s. apply proper. assumption. reflexivity. Qed.
  #[export] Instance GE_eqrel_cons_a_proper : Proper (R ==> L.R ==> R) Aa.
  Proof. autounfold. intros. subst. do 2 rewrite E_cons_one_a. apply proper. assumption. auto using R_oneAa. Qed.
  #[export] Instance GE_eqrel_cons_x_proper : Proper (R ==> eq ==> eq ==> R) Var.
  Proof. autounfold. intros. subst. do 2 rewrite E_cons_one_x. apply proper. assumption. reflexivity. Qed.
  #[export] Instance GE_eqrel_cons_o_proper : Proper (R ==> eq ==> R) Obj.
  Proof. autounfold. intros. subst. do 2 rewrite E_cons_one_o. apply proper. assumption. reflexivity. Qed.

  Theorem GE_eqrel_app : forall (e1 e1' e2 e2' : E),
      R e1 e1'
    -> R e2 e2'
    -> R (app e1 e2) (app e1' e2').
  Proof. intros. apply proper; assumption. Qed.
  #[export] Hint Resolve GE_eqrel_app : core.

  Corollary GE_eqrel_app_r : forall (e1 e1' e2 : E),
      R e1 e1'
    -> R (app e1 e2) (app e1' e2).
  Proof. intros. apply GE_eqrel_app. assumption. reflexivity. Qed.
  Corollary GE_eqrel_app_l : forall (e1 e2 e2' : E),
      R e2 e2'
    -> R (app e1 e2) (app e1 e2').
  Proof. intros. apply GE_eqrel_app. reflexivity. assumption. Qed.
  #[export] Hint Resolve GE_eqrel_app_r GE_eqrel_app_l : core.

  Theorem GE_eqrel_cons_s : forall (var : atom) (e e' : E),
      R e e'
    -> R (Skol e var) (Skol e' var).
  Proof. intros. do 2 rewrite E_cons_one_s. apply proper. assumption. reflexivity. Qed.
  Theorem GE_eqrel_cons_a : forall (e1 e2 : E) (l1 l2 : list atom),
      R e1 e2
    -> L.R l1 l2
    -> R (Aa e1 l1) (Aa e2 l2).
  Proof. intros. do 2 rewrite E_cons_one_a. apply proper. assumption. apply R_oneAa. assumption. Qed.
  Theorem GE_eqrel_cons_o : forall (o : O) (e e' : E),
      R e e'
    -> R (Obj e o) (Obj e' o).
  Proof. intros. do 2 rewrite E_cons_one_o. apply proper. assumption. reflexivity. Qed.
  Theorem GE_eqrel_cons_x : forall (x : termvar) (s : S) (e e' : E),
      R e e'
    -> R (Var e x s) (Var e' x s).
  Proof. intros. do 2 rewrite E_cons_one_x. apply proper. assumption. reflexivity. Qed.
  #[export] Hint Resolve GE_eqrel_cons_s GE_eqrel_cons_a GE_eqrel_cons_x GE_eqrel_cons_o : core.
End GE_eqrel_facts.
