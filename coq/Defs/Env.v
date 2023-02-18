(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Defs.GEnv.
Require Import Defs.List.
Require Export Defs.Obj.
Require Import Defs.Set.


(*** Notation, tactics etc*)
Notation "•" := Env_Empty (at level 1).

Notation "A ::s B"        := (Env_Skol A B)   (at level 50).
Notation "A ::a B"        := (Env_A    A B)   (at level 50).
Notation "A ::x B ':-' C" := (Env_Var  A B C) (at level 50).
Notation "A ::o B"        := (Env_Obj  A B)   (at level 50).

Notation "< B >s"      := (oneS B)   (at level 1, format "< B >s").
Notation "< B >a"      := (oneA B)   (at level 1, format "< B >a").
Notation "< B :- C >x" := (oneX B C) (at level 1, format "< B  :-  C >x").
Notation "< B >o"      := (oneO B)   (at level 1, format "< B >o").

Notation "A +++ B" := (Env_app A B) (at level 61, left associativity).

(*** Simplification *)
(** Associativity *)
Theorem Env_app_assoc (env1 env2 env3 : Env) : env1 +++ env2 +++ env3 = env1 +++ (env2 +++ env3).
Proof. induction env3; crush. Qed.
Theorem Env_app_assoc' (env1 env2 env3 : Env) : env1 +++ (env2 +++ env3) = env1 +++ env2 +++ env3.
Proof. symmetry. gen env1 env2 env3. exact Env_app_assoc. Qed.
#[export] Hint Rewrite Env_app_assoc' : core.

Ltac rep_Env_app_assoc := repeat (rewrite Env_app_assoc).
Tactic Notation "rep_Env_app_assoc" "in" hyp(H) := repeat (rewrite Env_app_assoc in H).
Tactic Notation "rep_Env_app_assoc*"    := repeat (rewrite Env_app_assoc in *).

(** app-empty simplifications *)
Theorem Env_app_nil_l env :
    • +++ env = env.
Proof. induction env; crush. Qed.
Theorem Env_app_nil_r env :
    env +++ • = env.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Env_app_nil_l Env_app_nil_r : core.

(** empty-to-one rewrites *)
Theorem Env_Empty_s (skA : skvar) :
    • ::s skA = <skA>s.
Proof. crush. Qed.
Theorem Env_Empty_a (a : A) :
    • ::a a = <a>a.
Proof. crush. Qed.
Theorem Env_Empty_x (x : termvar) (sch : Sch) :
    • ::x x :- sch = <x :- sch>x.
Proof. crush. Qed.
Theorem Env_Empty_o (obj : Obj) :
    • ::o obj = <obj>o.
Proof. crush. Qed.
#[export] Hint Rewrite Env_Empty_a Env_Empty_s Env_Empty_x Env_Empty_o : core.

(** app_cons rewrites *)
Theorem Env_app_cons_s : forall (env1 env2 : Env) (skA : skvar),
    env1 +++ env2 ::s skA = (env1 +++ env2) ::s skA.
Proof. crush. Qed.
Theorem Env_app_cons_a : forall (env1 env2 : Env) (a : A),
    env1 +++ env2 ::a a = (env1 +++ env2) ::a a.
Proof. crush. Qed.
Theorem Env_app_cons_x : forall (env1 env2 : Env) (x : termvar) (sch : Sch),
    env1 +++ env2 ::x x :- sch = (env1 +++ env2) ::x x :- sch.
Proof. crush. Qed.
Theorem Env_app_cons_o : forall (env1 env2 : Env) (obj : Obj),
    env1 +++ env2 ::o obj = (env1 +++ env2) ::o obj.
Proof. crush. Qed.
#[export] Hint Rewrite Env_app_cons_s Env_app_cons_a Env_app_cons_x Env_app_cons_o : core.

(** Cons-to-one rewrites (norm) *)
Theorem Env_cons_s_one (env : Env) (skA : skvar) :
    env ::s skA = env +++ <skA>s.
Proof. crush. Qed.
Theorem Env_cons_a_one (env : Env) (a : A) :
    env ::a a = env +++ <a>a.
Proof. crush. Qed.
Theorem Env_cons_x_one (env : Env) (x : termvar) (sch : Sch) :
    env ::x x :- sch = env +++ <x :- sch>x.
Proof. crush. Qed.
Theorem Env_cons_o_one (env : Env) (obj : Obj) :
    env ::o obj = env +++ <obj>o.
Proof. crush. Qed.
#[export] Hint Rewrite Env_cons_s_one Env_cons_a_one Env_cons_x_one Env_cons_o_one : norm.

(** Cons-to-app rewrites *)
Theorem Env_cons_app_s_one (env1 env2 : Env) (skA : skvar) :
    (env1 +++ env2) ::s skA = env1 +++ env2 ::s skA.
Proof. reflexivity. Qed.
Theorem Env_cons_app_a_one (env1 env2 : Env) (a : A) :
    (env1 +++ env2) ::a a = env1 +++ env2 ::a a.
Proof. reflexivity. Qed.
Theorem Env_cons_app_x_one (env1 env2 : Env) (x : termvar) (sch : Sch) :
    (env1 +++ env2) ::x x :- sch = env1 +++ env2 ::x x :- sch.
Proof. reflexivity. Qed.
Theorem Env_cons_app_o_one (env1 env2 : Env) (obj : Obj) :
    (env1 +++ env2) ::o obj = env1 +++ env2 ::o obj.
Proof. reflexivity. Qed.

(*** Membership conversions *)
Theorem Env_exvars_subset_Env_exvars : forall (env : Env),
    Env_exvars env [<=] Env_Obj_exvars env.
Proof. induction env; rewr; fsetdec. Qed.
#[export] Hint Rewrite Env_exvars_subset_Env_exvars : conv.

Theorem in_Env_exvars_impls_in_Env_exvars_Obj : forall (exA : exvar) (env : Env),
    exA \in Env_exvars env
  -> exA \in Env_Obj_exvars env.
Proof. intros. rewrite <- Env_exvars_subset_Env_exvars. assumption. Qed.
#[export] Hint Resolve in_Env_exvars_impls_in_Env_exvars_Obj : core.

Theorem notin_Env_exvars_Obj_impls_in_Env_exvars : forall (exA : exvar) (env : Env),
    exA \notin Env_Obj_exvars env
  -> exA \notin Env_exvars env.
Proof. intros. rewrite Env_exvars_subset_Env_exvars. assumption. Qed.
#[export] Hint Resolve notin_Env_exvars_Obj_impls_in_Env_exvars : core.

(*** GEnv instance *)
Module Env_E <: GEnv.
  Definition E : Type := Env.
  Definition S : Type := Sch.
  Definition O : Type := Obj.

  Definition Empty :                 E := Env_Empty.
  Definition Skol  : E -> atom ->      E := Env_Skol.
  Definition Aa    : E -> list atom -> E := Env_A.
  Definition Var   : E -> atom -> S ->  E := Env_Var.
  Definition Obj   : E -> O ->         E := Env_Obj.

  Definition oneS : atom ->      E := oneS.
  Definition oneA : list atom -> E := oneA.
  Definition oneX : atom -> S ->  E := oneX.
  Definition oneO : O ->         E := oneO.

  Definition app : E -> E -> E := Env_app.

  Definition E_cons_one_s : forall (e : E) (skA : atom),
      Skol e skA = app e (oneS skA) := Env_cons_s_one.
  Definition E_cons_one_a : forall (e : E) (a : list atom),
      Aa e a = app e (oneA a) := Env_cons_a_one.
  Definition E_cons_one_x : forall (e : E) (x : atom) (s : S),
      Var e x s = app e (oneX x s) := Env_cons_x_one.
  Definition E_cons_one_o : forall (e : E) (o : O),
      Obj e o = app e (oneO o) := Env_cons_o_one.

  Definition E_app_nil_r : forall (e : E),
      app e Empty = e := Env_app_nil_r.
  Definition E_app_nil_l : forall (e : E),
      app Empty e = e := Env_app_nil_l.
End Env_E.

(*** Bindings to schs *)
Theorem Env_bindings_Schs_Env : forall (sch : Sch) (env : Env),
    (exists (x : termvar), SchPSI.In (x, sch) (Env_bindings env)) <-> SchSI.In sch (Env_Schs env).
Proof.
  introv. induction env; rewr*.
  - crush.
  - split; intros; destr. apply IHenv. exists x. crush. forwards<: IHenv. eassumption. destr. exists x. crush.
  - split; intros; destr. apply IHenv. exists x. crush. forwards<: IHenv. eassumption. destr. exists x. crush.
  - split; intros; destr.
    + rewr in H. indestr in H. destr.
      * forwards>: IHenv. exists x0. assumption. fsetdec'.
      * fsetdec'.
    + indestr in H. destr.
      * forwards<: IHenv. eassumption. destr. exists x0. crush.
      * exists x. rewr. fsetdec.
  - split; intros; destr. apply IHenv. exists x. crush. forwards<: IHenv. eassumption. destr. exists x. crush.
Qed.

Corollary Env_bindings_Schs_Env1 : forall (sch : Sch) (env : Env) (x : termvar),
    SchPSI.In (x, sch) (Env_bindings env)
  -> SchSI.In sch (Env_Schs env).
Proof. intros. apply Env_bindings_Schs_Env. exists x. assumption. Qed.
#[export] Hint Resolve Env_bindings_Schs_Env1 : core.
(* (** Env_Schs_sub *) *)
(* (* Def *) *)
(* Definition Env_Schs_sub (env1 env2 : Env) := *)
(*     Env_Schs env1 ⟪<=⟫ Env_Schs env2. *)
(* #[export] Hint Unfold Env_Schs_sub : core. *)

(* Notation "A [<=]es B" := (Env_Schs_sub A B) (at level 65, format "A  [<=]es  B"). *)

(* (* Instance *) *)
(* Theorem Env_Schs_sub_refl : Reflexive Env_Schs_sub. *)
(* Proof. crush. Qed. *)
(* #[export] Hint Resolve Env_Schs_sub_refl : core. *)
(* Theorem Env_Schs_sub_trans : Transitive Env_Schs_sub. *)
(* Proof. unfold Transitive, Env_Schs_sub. crush. Qed. *)

(* Theorem Env_Schs_sub_app : forall (env1 env1' env2 env2' : Env), *)
(*     env1 [<=]es env1' *)
(*   -> env2 [<=]es env2' *)
(*   -> env1 +++ env2 [<=]es env1' +++ env2'. *)
(* Proof. autounfold. intros; rewr*. fsetdec'. Qed. *)
(* #[export] Hint Resolve Env_Schs_sub_app : core. *)
(* #[export] Instance Env_Schs_sub_app_proper : Proper (Env_Schs_sub ==> Env_Schs_sub ==> Env_Schs_sub) Env_app. *)
(* Proof. crush. Qed. *)

(* Module Env_Schs_sub_subrel <: GE_subrel list_sub_subrel Env_E. *)
(*   Definition R : Env -> Env -> Prop := Env_Schs_sub. *)

(*   Definition refl  : Reflexive  R := Env_Schs_sub_refl. *)
(*   Definition trans : Transitive R := Env_Schs_sub_trans. *)

(*   Theorem R_empty : forall (env : Env), R • env. unfold R, Env_Schs_sub. intros. fsetdec'. Qed. *)
(*   Theorem R_emptyA : forall (env : Env), R (oneA []) env. unfold R. unfold Env_Schs_sub. intros. rewr. fsetdec'. Qed. *)

(*   Definition proper : Proper (R ==> R ==> R) Env_app := Env_Schs_sub_app_proper. *)

(*   Theorem R_oneAa : forall (a1 a2 : DA), list_sub_subrel.R a1 a2 -> R (oneA a1) (oneA a2). *)
(*     unfold R, Env_Schs_sub, list_sub_subrel.R, Env_skvars. intros. rewr_Env_to_Set. rewr. fsetdec'. *)
(*   Qed. *)

(*   Definition E_cons_anil : forall (env : Env), *)
(*       R env (env ::a []). unfold R, Env_Schs_sub. crush. Qed. *)
(* End Env_Schs_sub_subrel. *)

(* Module Export Env_Schs_sub_subrel_facts := GE_subrel_facts list_sub_subrel Env_E Env_Schs_sub_subrel. *)
(* #[export] Hint Extern 1 (Env_Schs_sub _ _) => fold Env_Schs_sub_subrel.R : core. *)

(* (** Env_Schs_eq *) *)
(* (* Def *) *)
(* Definition Env_Schs_eq (env1 env2 : Env) := *)
(*     Env_Schs env1 ⟪=⟫ Env_Schs env2. *)
(* #[export] Hint Unfold Env_Schs_eq : core. *)

(* Notation "A [=]es B" := (Env_Schs_eq A B) (at level 65, format "A  [=]es  B"). *)

(* (* Instance *) *)
(* Theorem Env_Schs_eq_refl : Reflexive Env_Schs_eq. *)
(* Proof. crush. Qed. *)
(* #[export] Hint Resolve Env_Schs_eq_refl : core. *)
(* Theorem Env_Schs_eq_trans : Transitive Env_Schs_eq. *)
(* Proof. unfold Transitive, Env_Schs_eq. crush. Qed. *)
(* Theorem Env_Schs_eq_symm : Symmetric Env_Schs_eq. *)
(* Proof. unfold Symmetric, Env_Schs_eq. crush. Qed. *)

(* Theorem Env_Schs_eq_app : forall (env1 env1' env2 env2' : Env), *)
(*     env1 [=]es env1' *)
(*   -> env2 [=]es env2' *)
(*   -> env1 +++ env2 [=]es env1' +++ env2'. *)
(* Proof. autounfold. intros; rewr*. fsetdec'. Qed. *)
(* #[export] Hint Resolve Env_Schs_eq_app : core. *)
(* #[export] Instance Env_Schs_eq_app_proper : Proper (Env_Schs_eq ==> Env_Schs_eq ==> Env_Schs_eq) Env_app. *)
(* Proof. crush. Qed. *)

(* Module Env_Schs_eq_eqrel <: GE_eqrel list_eq_eqrel Env_E. *)
(*   Definition R : Env -> Env -> Prop := Env_Schs_eq. *)

(*   Definition refl  : Reflexive  R := Env_Schs_eq_refl. *)
(*   Definition trans : Transitive R := Env_Schs_eq_trans. *)
(*   Definition symm  : Symmetric  R := Env_Schs_eq_symm. *)

(*   Definition proper : Proper (R ==> R ==> R) Env_app := Env_Schs_eq_app_proper. *)

(*   Theorem R_oneAa : forall (a1 a2 : DA), list_eq_eqrel.R a1 a2 -> R (oneA a1) (oneA a2). *)
(*     unfold R, Env_Schs_eq, list_sub_subrel.R, Env_skvars. intros. rewr_Env_to_Set. rewr. fsetdec'. *)
(*   Qed. *)
(* End Env_Schs_eq_eqrel. *)

(* Module Export Env_Schs_eq_subrel_facts := GE_eqrel_facts list_eq_eqrel Env_E Env_Schs_eq_eqrel. *)
(* #[export] Hint Extern 1 (Env_Schs_eq _ _) => fold Env_Schs_eq_eqrel.R : core. *)

(* (* Conversions *) *)
(* Theorem Env_Schs_eq_sub : forall (env1 env2 : Env), *)
(*     env1 [=]es env2 *)
(*   -> env1 [<=]es env2. *)
(* Proof. autounfold. crush. Qed. *)
(* #[export] Hint Resolve Env_Schs_eq_sub : core. *)

(*** Env_(sub/eq) *)
(** Env_sub *)
(* Def *)
Definition Env_sub (env1 env2 : Env) :=
    (Env_skvars env1 [<=] Env_skvars env2)
  /\ (Env_exvars env1 [<=] Env_exvars env2).
#[export] Hint Unfold Env_sub : core.

Notation "A [<=]e B" := (Env_sub A B) (at level 65, format "A  [<=]e  B").

(* Instance *)
Theorem Env_sub_refl : Reflexive Env_sub.
Proof. crush. Qed.
#[export] Hint Resolve Env_sub_refl : core.
Theorem Env_sub_trans : Transitive Env_sub.
Proof. unfold Transitive, Env_sub. crush. Qed.

Theorem Env_sub_app : forall (env1 env1' env2 env2' : Env),
    env1 [<=]e env1'
  -> env2 [<=]e env2'
  -> env1 +++ env2 [<=]e env1' +++ env2'.
Proof. autounfold. split; intros; rewr; subst; fsetdec. Qed.
#[export] Hint Resolve Env_sub_app : core.
#[export] Instance Env_sub_app_proper : Proper (Env_sub ==> Env_sub ==> Env_sub) Env_app.
Proof. crush. Qed.

Module Env_sub_subrel <: GE_subrel list_sub_subrel Env_E.
  Definition R : Env -> Env -> Prop := Env_sub.

  Definition refl  : Reflexive  R := Env_sub_refl.
  Definition trans : Transitive R := Env_sub_trans.

  Theorem R_empty : forall (env : Env), R • env. unfold R. crush. Qed.
  Theorem R_emptyA : forall (env : Env), R (oneA []) env. unfold R. unfold Env_sub. crush. Qed.

  Definition proper : Proper (R ==> R ==> R) Env_app := Env_sub_app_proper.

  Theorem R_oneAa : forall (a1 a2 : DA), list_sub_subrel.R a1 a2 -> R (oneA a1) (oneA a2).
    unfold R, Env_sub, list_sub_subrel.R, Env_skvars. intros. rewr_Env_to_Set. rewr. crush.
  Qed.

  Definition E_cons_anil : forall (env : Env),
      R env (env ::a []). unfold R, Env_sub. crush. Qed.
End Env_sub_subrel.

Module Export Env_sub_subrel_facts := GE_subrel_facts list_sub_subrel Env_E Env_sub_subrel.
#[export] Hint Extern 1 (Env_sub _ _) => fold Env_sub_subrel.R : core.

(** Env_eq *)
(* Def *)
Definition Env_eq (env1 env2 : Env) :=
    (Env_skvars env1 [=] Env_skvars env2)
  /\ (Env_exvars env1 [=] Env_exvars env2).
#[export] Hint Unfold Env_eq : core.

Notation "A [=]e B" := (Env_eq A B) (at level 65, format "A  [=]e  B").

(* Instance *)
Theorem Env_eq_refl : Reflexive Env_eq.
Proof. crush. Qed.
#[export] Hint Resolve Env_eq_refl : core.
Theorem Env_eq_trans : Transitive Env_eq.
Proof. unfold Transitive, Env_eq. crush. Qed.
Theorem Env_eq_symm : Symmetric Env_eq.
Proof. unfold Symmetric, Env_eq. crush. Qed.

Theorem Env_eq_app : forall (env1 env1' env2 env2' : Env),
    env1 [=]e env1'
  -> env2 [=]e env2'
  -> env1 +++ env2 [=]e env1' +++ env2'.
Proof. autounfold. split; intros; rewr; subst; fsetdec. Qed.
#[export] Hint Resolve Env_eq_app : core.
#[export] Instance Env_eq_app_proper : Proper (Env_eq ==> Env_eq ==> Env_eq) Env_app.
Proof. crush. Qed.

Module Env_eq_eqrel <: GE_eqrel list_eq_eqrel Env_E.
  Definition R : Env -> Env -> Prop := Env_eq.

  Definition refl  : Reflexive  R := Env_eq_refl.
  Definition trans : Transitive R := Env_eq_trans.
  Definition symm  : Symmetric  R := Env_eq_symm.

  Definition proper : Proper (R ==> R ==> R) Env_app := Env_eq_app_proper.

  Theorem R_oneAa : forall (a1 a2 : DA), list_eq_eqrel.R a1 a2 -> R (oneA a1) (oneA a2).
    unfold R, Env_eq, list_eq_eqrel.R, Env_skvars. intros. rewr. crush.
  Qed.
End Env_eq_eqrel.

Module Export Env_eq_subrel_facts := GE_eqrel_facts list_eq_eqrel Env_E Env_eq_eqrel.
#[export] Hint Extern 1 (Env_eq _ _) => fold Env_eq_eqrel.R : core.

(* Conversions *)
Theorem Env_eq_sub : forall (env1 env2 : Env),
    env1 [=]e env2
  -> env1 [<=]e env2.
Proof. autounfold. crush. Qed.
#[export] Hint Resolve Env_eq_sub : core.

(*** Env_fr_(sub/eq) *)
(** Env_fr_sub *)
(* Def *)
Definition Env_fr_sub (env1 env2 : Env) :=
    (Env_skvars     env1 [<=] Env_skvars     env2)
  /\ (Env_Obj_exvars env1 [<=] Env_Obj_exvars env2).
#[export] Hint Unfold Env_fr_sub : core.

Notation "A [<=]e# B" := (Env_fr_sub A B) (at level 65, format "A  [<=]e#  B").

(* Instance *)
Theorem Env_fr_sub_refl : Reflexive Env_fr_sub.
Proof. crush. Qed.
#[export] Hint Resolve Env_fr_sub_refl : core.
Theorem Env_fr_sub_trans : Transitive Env_fr_sub.
Proof. unfold Transitive, Env_fr_sub. crush. Qed.

Theorem Env_fr_sub_app : forall (env1 env1' env2 env2' : Env),
    env1 [<=]e# env1'
  -> env2 [<=]e# env2'
  -> env1 +++ env2 [<=]e# env1' +++ env2'.
Proof. autounfold. split; intros; rewr; subst; fsetdec. Qed.
#[export] Hint Resolve Env_fr_sub_app : core.
#[export] Instance Env_fr_sub_app_proper : Proper (Env_fr_sub ==> Env_fr_sub ==> Env_fr_sub) Env_app.
Proof. crush. Qed.

Module Env_fr_sub_subrel <: GE_subrel list_sub_subrel Env_E.
  Definition R : Env -> Env -> Prop := Env_fr_sub.

  Definition refl  : Reflexive  R := Env_fr_sub_refl.
  Definition trans : Transitive R := Env_fr_sub_trans.

  Theorem R_empty : forall (env : Env), R • env. unfold R. crush. Qed.
  Theorem R_emptyA : forall (env : Env), R (oneA []) env. unfold R. unfold Env_fr_sub. crush. Qed.

  Definition proper : Proper (R ==> R ==> R) Env_app := Env_fr_sub_app_proper.

  Theorem R_oneAa : forall (a1 a2 : DA), list_sub_subrel.R a1 a2 -> R (oneA a1) (oneA a2).
    unfold R, Env_fr_sub, list_sub_subrel.R, Env_skvars. intros. rewr. crush.
  Qed.

  Definition E_cons_anil : forall (env : Env),
      R env (env ::a []). unfold R, Env_fr_sub. crush. Qed.
End Env_fr_sub_subrel.

Module Export Env_fr_sub_subrel_facts := GE_subrel_facts list_sub_subrel Env_E Env_fr_sub_subrel.
#[export] Hint Extern 1 (Env_fr_sub _ _) => fold Env_fr_sub_subrel.R : core.

(** Env_fr_eq *)
(* Def *)
Definition Env_fr_eq (env1 env2 : Env) :=
    (Env_skvars     env1 [=] Env_skvars     env2)
  /\ (Env_Obj_exvars env1 [=] Env_Obj_exvars env2).
#[export] Hint Unfold Env_fr_eq : core.

Notation "A [=]e# B" := (Env_fr_eq A B) (at level 65, format "A  [=]e#  B").

Theorem Env_fr_eq_refl : Reflexive Env_fr_eq.
Proof. crush. Qed.
Theorem Env_fr_eq_trans : Transitive Env_fr_eq.
Proof. unfold Transitive, Env_fr_eq. crush. Qed.
Theorem Env_fr_eq_symm : Symmetric Env_fr_eq.
Proof. unfold Symmetric, Env_fr_eq. crush. Qed.
#[export] Hint Resolve Env_fr_eq_refl Env_fr_eq_symm : core.

Theorem Env_fr_eq_app : forall (env1 env1' env2 env2' : Env),
    env1 [=]e# env1'
  -> env2 [=]e# env2'
  -> env1 +++ env2 [=]e# env1' +++ env2'.
Proof. autounfold. split; intros; rewr; subst; fsetdec. Qed.
#[export] Hint Resolve Env_fr_eq_app : core.
#[export] Instance Env_fr_eq_app_proper : Proper (Env_fr_eq ==> Env_fr_eq ==> Env_fr_eq) Env_app.
Proof. crush. Qed.

Module Env_fr_eq_eqrel <: GE_eqrel list_eq_eqrel Env_E.
  Definition R : Env -> Env -> Prop := Env_fr_eq.

  Definition refl  : Reflexive  R := Env_fr_eq_refl.
  Definition trans : Transitive R := Env_fr_eq_trans.
  Definition symm  : Symmetric  R := Env_fr_eq_symm.

  Definition proper : Proper (R ==> R ==> R) Env_app := Env_fr_eq_app_proper.

  Theorem R_oneAa : forall (a1 a2 : DA), list_eq_eqrel.R a1 a2 -> R (oneA a1) (oneA a2).
    unfold R, Env_fr_eq, list_eq_eqrel.R, Env_skvars. intros. rewr. crush.
  Qed.
End Env_fr_eq_eqrel.

Module Export Env_fr_eq_subrel_facts := GE_eqrel_facts list_eq_eqrel Env_E Env_fr_eq_eqrel.
#[export] Hint Extern 1 (Env_fr_eq _ _) => fold Env_fr_eq_eqrel.R : core.

(* Conversions *)
Theorem Env_fr_eq_sub : forall (env1 env2 : Env),
    env1 [=]e# env2
  -> env1 [<=]e# env2.
Proof. autounfold. crush. Qed.
#[export] Hint Resolve Env_fr_eq_sub : core.

(*** rewr_erel *)
Ltac unfold_erel :=
           ( (try unfold Env_fr_sub     ); (try unfold Env_sub     )
           ; (try unfold Env_fr_eq      ); (try unfold Env_eq      ) ).
Tactic Notation "unfold_erel" "in" hyp(H) :=
           ( (try unfold Env_fr_sub in H); (try unfold Env_sub in H)
           ; (try unfold Env_fr_eq  in H); (try unfold Env_eq  in H) ).
Tactic Notation "unfold_erel*" :=
           ( (try unfold Env_fr_sub in *); (try unfold Env_sub in *)
           ; (try unfold Env_fr_eq  in *); (try unfold Env_eq  in *) ).

Ltac   fold_erel :=
           ( (try   fold Env_fr_sub     ); (try   fold Env_sub     )
           ; (try   fold Env_fr_eq      ); (try   fold Env_eq      ) ).
Tactic Notation "  fold_erel" "in" hyp(H) :=
           ( (try   fold Env_fr_sub in H); (try   fold Env_sub in H)
           ; (try   fold Env_fr_eq  in H); (try   fold Env_eq  in H) ).
Tactic Notation "  fold_erel*" :=
           ( (try   fold Env_fr_sub in *); (try   fold Env_sub in *)
           ; (try   fold Env_fr_eq  in *); (try   fold Env_eq  in *) ).

Ltac rewr_erel := unfold_erel; progress rewr; fold_erel.
Tactic Notation "rewr_erel" "in" hyp(H) :=
  unfold_erel in H; progress (rewr in H); fold_erel in H.
Tactic Notation "rewr_erel*" :=
  unfold_erel*    ; progress (rewr*    ); fold_erel*    .
