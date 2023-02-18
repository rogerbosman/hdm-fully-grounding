(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Coq.FSets.FSetProperties.

Require Import Defs.Env.
Require Import Defs.List.
Require Import Defs.Obj.
Require Import Defs.Set.

(*** Notation, tactics etc*)
Theorem FrA_app_split : forall (a1 a2 : A) (env : Env),
    FrA (a2 ++ a1) env
  <-> (FrA a2 (env ::a a1) /\ FrA a1 env).
Proof.
  introv. split; induction a2; rewr. 1,3:crush.
  - split; inverts H. 2:{ apply IHa2. assumption. }
    constructor. crush. rewr*. intros. apply FR. fsetdec.
  - intros. destr. inverts H. destr. constructor. eauto.
    rewr*. intros. apply FR. fsetdec.
Qed.

Ltac inv_FrA_ :=
  let H := fresh "H" in
  let FR1 := fresh "FR" in
  let FR2 := fresh "FR" in
  match goal with
    | [ H  : FrA nil _ |- _ ] => clear H
    | [ H  : FrA (cons _ _) _ |- _ ] => inverts H
    | [ H  : FrA ([_]) _ |- _ ] => inverts H
    (* | [ H  : FrA (?a2 ++ ?a1) ?env |- _ ] => assert (H' := H); apply FrA_app_split in H'; destruct H' as [FR1 FR2] *)
    | [ H  : FrA (?a2 ++ ?a1) ?env |- _ ] => apply FrA_app_split in H; destruct H as [FR1 FR2]
  end.
Ltac inv_FrA := repeat inv_FrA_.

(*** Inversion *)
Theorem FrA_inv : forall (exA : var) (a : A) (env : Env),
    FrA (exA :: a) env
  -> FrA a env
  /\ exA \notin Env_Obj_exvars (env ::a a).
Proof. inversion 1. jauto. Qed.
Corollary FrA_inv__proj1 : forall (exA : var) (a : A) (env : Env),
    FrA (exA :: a) env
  -> FrA        a  env.
Proof. apply FrA_inv. Qed.
Corollary FrA_inv__proj2 : forall (exA : var) (a : A) (env : Env),
    FrA (exA :: a) env
  -> exA \notin Env_Obj_exvars (env ::a a).
Proof. apply FrA_inv. Qed.
#[export] Hint Resolve FrA_inv__proj1 FrA_inv__proj2 : core.

Ltac indestr := rewr*; autorewrite with in_disj in *; destr.
Tactic Notation "indestr" "in" hyp(H) := rewr in H; autorewrite with in_disj in H.

Theorem FrA_in_inv : forall (exA : var) (a : A) (env : Env),
    FrA a env
  -> exA \in varl a
  -> exA \notin Env_Obj_exvars env.
Proof.
  induction a. crush. intros. indestr. eauto. rewr*. subst.
  forwards: FrA_inv__proj2. eassumption. unfold not in *. crush.
Qed.

(* (*** Things for in list *) *)
(* #[export] Hint Constructors NoDup'. *)

(* Theorem list_to_varl : forall (exA : exvar) (a : A), *)
(*     In exA a <-> exA \in varl a. *)
(* Proof. *)
(*   intros. induction a. crush. *)
(*   destruct (a == exA). *)
(*   - crush. *)
(*   - crush. right. apply H0. fsetdec. *)
(* Qed. *)
(* Corollary list_to_varl1 : forall (exA : exvar) (a : A), *)
(*     In exA a -> exA \in varl a. *)
(* Proof. apply list_to_varl. Qed. *)
(* Corollary list_to_varl2 : forall (exA : exvar) (a : A), *)
(*     exA \in varl a -> In exA a. *)
(* Proof. apply list_to_varl. Qed. *)
(* #[export] Hint Resolve list_to_varl1 list_to_varl2 : core. *)

(* Theorem incl_list_sub : forall (a1 a2 : A), *)
(*     incl a1 a2 *)
(*   -> a1 [<=]l a2. *)
(* Proof. intros. autounfold. unfold AtomSetImpl.Subset. crush. Qed. *)
(* #[export] Hint Resolve incl_list_sub : core. *)

(* Lemma Nodup_incl: forall (a1 a2 : A) (env1 : Env), *)
(*     NoDup' a1 *)
(*   -> incl a2 a1 *)
(*   -> NoDup' a2. *)
(* OK this doesn't work we need proper sublists *)

(*** For in Env *)
(* Lemma Env_sub__proj1 : forall (env1 env2 : Env), *)
(*     env1 [<=]e env2 *)
(*   -> Env_skvars env1 [<=] Env_skvars env2. *)
(* Proof. autounfold. intros. jauto. Qed. *)
(* #[export] Hint Resolve Env_sub__proj1 : core. *)
(* Lemma Env_sub__proj2 : forall (env1 env2 : Env), *)
(*     env1 [<=]e env2 *)
(*   -> Env_exvars env1 [<=] Env_exvars env2. *)
(* Proof. autounfold. intros. jauto. Qed. *)
(* #[export] Hint Resolve Env_sub__proj2 : core. *)

(* Lemma Env_eq_proj1 : forall (env1 env2 : Env), *)
(*     env1 [=]e env2 *)
(*   -> Env_skvars env1 [=] Env_skvars env2. *)
(* Proof. autounfold. intros. jauto. Qed. *)
(* #[export] Hint Resolve Env_eq_proj1 : core. *)
(* Lemma Env_eq_proj2 : forall (env1 env2 : Env), *)
(*     env1 [=]e env2 *)
(*   -> Env_exvars env1 [=] Env_exvars env2. *)
(* Proof. autounfold. intros. jauto. Qed. *)
(* #[export] Hint Resolve Env_eq_proj2 : core. *)

(* Lemma Env_fr_sub_proj1 : forall (env1 env2 : Env), *)
(*     env1 [<=]e# env2 *)
(*   -> Env_skvars env1 [<=] Env_skvars env2. *)
(* Proof. autounfold. intros. jauto. Qed. *)
(* #[export] Hint Resolve Env_fr_sub_proj1 : core. *)
(* Lemma Env_fr_sub_proj2 : forall (env1 env2 : Env), *)
(*     env1 [<=]e# env2 *)
(*   -> Env_Obj_exvars env1 [<=] Env_Obj_exvars env2. *)
(* Proof. autounfold. intros. jauto. Qed. *)
(* #[export] Hint Resolve Env_fr_sub_proj2 : core. *)

(* Lemma Env_fr_eq_proj1 : forall (env1 env2 : Env), *)
(*     env1 [=]e# env2 *)
(*   -> Env_skvars env1 [=] Env_skvars env2. *)
(* Proof. autounfold. intros. jauto. Qed. *)
(* #[export] Hint Resolve Env_fr_eq_proj1 : core. *)
(* Lemma Env_fr_eq_proj2 : forall (env1 env2 : Env), *)
(*     env1 [=]e# env2 *)
(*   -> Env_Obj_exvars env1 [=] Env_Obj_exvars env2. *)
(* Proof. autounfold. intros. jauto. Qed. *)
(* #[export] Hint Resolve Env_fr_eq_proj2 : core. *)

(*** Props *)
Theorem FrA_props : forall (a : A) (env : Env),
    FrA a env
  <-> varl a [><] Env_Obj_exvars env
  /\ NoDup' a.
Proof.
  intros. split.
  - induction 1. crush. destr. split.
    + rewr. apply disjoint_extend'. crush. eassumption.
    + constructor. crush. assumption.
  - intros [? ND]. induction ND. crush.
    constructor. rewr in H.
    apply IHND. assert (SUB: varl a [<=] varl a \u singleton exA). fsetdec.
    rewrite SUB. eassumption.
    rewr. intros. indestr. eauto using in_disjoint_impl. crush.
Qed.
Corollary FrA_props1 : forall (a : A) (env : Env),
    FrA a env
  -> varl a [><] Env_Obj_exvars env
  /\ NoDup' a.
Proof. apply FrA_props. Qed.
Corollary FrA_props2 : forall (a : A) (env : Env),
    varl a [><] Env_Obj_exvars env
  -> NoDup' a
  -> FrA a env.
Proof. intros. apply FrA_props. crush. Qed.
Corollary FrA_props3 : forall (a : A) (env : Env),
    FrA a env
  -> varl a [><] Env_Obj_exvars env.
Proof. apply FrA_props. Qed.
Corollary FrA_props4 : forall (a : A) (env : Env),
    FrA a env
  -> NoDup' a.
Proof. apply FrA_props. Qed.

(*** Rewriting *)
Theorem FrA_rewr : forall (a1 a2 : A) (env1 env2 : Env),
    FrA a1 env1
  -> a2 [<=]lu a1
  -> env2 [<=]e# env1
  -> FrA a2 env2.
Proof.
  introv FRA SUB__l SUB__e. rewrite FrA_props in *.
  split.
  - applys disj_subset_proper. 3:jauto. crush. rewr. conv. unfold Env_fr_sub in SUB__e. jauto.
  - jauto.
Qed.
#[export] Hint Resolve FrA_rewr : core.

#[export] Instance FrA_rewr_proper : Proper (flip list_uni_sub ==> flip Env_fr_sub ==> impl) FrA.
Proof. unfold Proper, respectful, impl, flip. intros. eauto. Qed.

Corollary FrA_Env_sub : forall (env1 env2 : Env) (a : A),
    FrA a env1
  -> env2 [<=]e# env1
  -> FrA a env2.
Proof. eauto. Qed.
Corollary FrA_sublist : forall (a1 a2 : A) (env : Env),
    FrA a1 env
  -> a2 [<=]lu a1
  -> FrA a2 env.
Proof. eauto. Qed.

(*** Unsorted *)
Theorem FrA_Obj : forall (env : Env) (a1 a2 : A) (sch : Sch),
    FrA a2 (env ::o ⟦⟨a1⟩ sch⟧)
  <-> FrA a2 (env ::a a1).
Proof. split; introv FR; eapply FrA_rewr; try apply FR; try reflexivity; eauto. rewr.
       unfold Env_fr_sub. crush.
       unfold Env_fr_sub. crush.
Qed.

Lemma FrA_cons_shift: forall (exA : exvar) (a : list exvar) (env : Env),
    FrA (exA :: a) env
  -> FrA a (env ::a [exA]).
Proof.
  introv FR. listind a. crush. constructor. apply IHa.
  constructor. eauto. inv_FrA. intros. apply FR0. rewr*. fsetdec.
  inv_FrA. intros. indestr in H. destr. apply FR. rewr. fsetdec. rewr in H. crush. apply FR. rewr. fsetdec.
Qed.
