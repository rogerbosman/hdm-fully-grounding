(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Defs.Env.
Require Import Defs.List.
Require Import Defs.Obj.
Require Import Defs.Set.
Require Import Defs.Substs.

Require Import Defs.FrA.
Require Import Defs.WfTy.

(*** Notation, tactics etc*)
Notation "wf( A )" := (WfEnv A) (at level 50, format "wf( A )") : type_scope.

Ltac inv_Wf_ :=
  match goal with
    | [ H : wf(_ ::s _)  |- _ ] => inverts H
    | [ H : wf(_ ::a _)  |- _ ] => inverts H
    | [ H : wf(_ ::x _ :- _)  |- _ ] => inverts H
    | [ H : wf(_ ::o _)  |- _ ] => inverts H
  end.
Ltac inv_Wf := repeat inv_Wf_.
Ltac inv_Wf' := repeat (inv_Wf; inv_FrA).

(*** Weakening *)
Theorem WfEnv_weak_app : forall (env1 env2 : Env),
    wf(env1 +++ env2)
  -> wf(env1).
Proof. introv WF. induction env2; inverts WF; crush. Qed.
#[export] Hint Resolve WfEnv_weak_app : core.

Theorem WfEnv_weak_cons_s : forall (skA : skvar) (env : Env),
    wf(env ::s skA)
  -> False.
Proof. introv WF. inverts WF. Qed.
#[export] Hint Resolve WfEnv_weak_cons_s : core.

Theorem WfEnv_weak_cons_a : forall (a : A) (env : Env),
    wf(env ::a a)
  -> wf(env).
Proof. introv WF. norm*. eauto. Qed.
#[export] Hint Resolve WfEnv_weak_cons_a : core.

Theorem WfEnv_weak_cons_a_cons : forall (exA : exvar) (a : A) (env : Env),
    wf(env ::a (exA :: a))
  -> wf(env ::a a).
Proof. introv WF. inverts WF. constructor. assumption. eauto. Qed.
#[export] Hint Resolve WfEnv_weak_cons_a_cons : core.

Theorem WfEnv_weak_cons_a_app : forall (a1 a2 : A) (env : Env),
    wf(env ::a (a2 ++ a1))
  -> wf(env ::a a1).
Proof. introv WF. inverts WF. constructor. assumption. eauto 6. Qed.
#[export] Hint Resolve WfEnv_weak_cons_a_app : core.

Theorem WfEnv_weak_cons_x : forall (x : termvar) (sch : Sch) (env : Env),
    wf(env ::x x :- sch)
  -> wf(env).
Proof. introv WF. norm*. eauto. Qed.
#[export] Hint Resolve WfEnv_weak_cons_x : core.

Theorem WfEnv_weak_cons_o : forall (obj : Obj) (env : Env),
    wf(env ::o obj)
  -> wf(env).
Proof. introv WF. norm*. eauto. Qed.
#[export] Hint Resolve WfEnv_weak_cons_o : core.

Theorem WfEnv_weak_app_onea_cons : forall (exA : exvar) (a : A) (env : Env),
    wf(env +++ <exA :: a>a)
  -> wf(env +++ <      a>a).
Proof. introv WF. inverts WF. constructor; eauto. Qed.
#[export] Hint Resolve WfEnv_weak_app_onea_cons : core.

Theorem WfEnv_weak_app_onea_app : forall (a1 a2 : A) (env : Env),
    wf(env +++ <a2 ++ a1>a)
  -> wf(env +++ <      a1>a).
Proof. introv WF. inverts WF. constructor; eauto 6. Qed.
#[export] Hint Resolve WfEnv_weak_app_onea_app : core.

(*** Inversion *)
Theorem WfEnv_inv_app_onea : forall (a : A) (env : Env),
    wf(env +++ <a>a)
  -> FrA a env.
Proof. inversion 1. trivial. Qed.
#[export] Hint Resolve WfEnv_inv_app_onea : core.

Theorem WfEnv_inv_cons_a : forall (a : A) (env : Env),
    wf(env ::a a)
  -> FrA a env.
Proof. intros. norm*. eauto. Qed.
#[export] Hint Resolve WfEnv_inv_cons_a : core.

Theorem WfEnv_inv_cons_x : forall (x : termvar) (sch : Sch) (env : Env),
    wf(env ::x x :- sch)
  -> env |=ty sch.
Proof. intros. inv_Wf. assumption. Qed.
#[export] Hint Resolve WfEnv_inv_cons_x : core.

Theorem wf_Env_inv_o : forall (env : Env) (a : A) (sch : Sch),
    wf(env ::o ⟦⟨a⟩ sch⟧)
  -> env ::a a |=ty sch.
Proof. inversion 1; assumption. Qed.
#[export] Hint Resolve wf_Env_inv_o : core.


(*** Wf-ness of objects*)
Theorem wf_Env_Obj_x : forall (env : Env) (sch : Sch) (x : termvar) (a : A),
    wf(env ::o ⟦⟨a⟩ sch⟧)
  <-> wf(env ::a a ::x x :- sch).
Proof. split; intros; inv_Wf; crush. Qed.
Corollary wf_Env_Obj_x1 : forall (env : Env) (sch : Sch) (x : termvar) (a : A),
    wf(env ::o ⟦⟨a⟩ sch⟧)
  -> wf(env ::a a ::x x :- sch).
Proof. apply wf_Env_Obj_x. Qed.
Corollary wf_Env_Obj_x2 : forall (env : Env) (sch : Sch) (x : termvar) (a : A),
    wf(env ::a a ::x x :- sch)
  -> wf(env ::o ⟦⟨a⟩ sch⟧).
Proof. apply wf_Env_Obj_x. Qed.
#[export] Hint Resolve wf_Env_Obj_x1 wf_Env_Obj_x2 : slow.

Theorem wf_Env_Obj_noa_x : forall (env : Env) (sch : Sch) (x : termvar),
    wf(env ::o ⟦sch⟧)
  <-> wf(env ::x x :- sch).
Proof. split; intros; inv_Wf. constructor. auto. eapply WfTy_Env_sub. eassumption. auto. eauto. Qed.

Corollary wf_Env_Obj_noa_x1 : forall (env : Env) (sch : Sch) (x : termvar),
    wf(env ::o ⟦sch⟧)
  -> wf(env ::x x :- sch).
Proof. apply wf_Env_Obj_noa_x. Qed.
Corollary wf_Env_Obj_noa_x2 : forall (env : Env) (sch : Sch) (x : termvar),
    wf(env ::x x :- sch)
  -> wf(env ::o ⟦sch⟧).
Proof. apply wf_Env_Obj_noa_x. Qed.
#[export] Hint Resolve wf_Env_Obj_noa_x1 wf_Env_Obj_noa_x2 : slow.

Corollary wf_Env_Obj_move_a1 : forall (env : Env) (sch : Sch) (a : A),
    wf(env ::a a ::o ⟦sch⟧)
  -> wf(env ::o ⟦⟨a⟩ sch⟧).
Proof. intros. fresh_atom' empty. apply (wf_Env_Obj_x _ _ x). auto using wf_Env_Obj_noa_x1. Qed.
Corollary wf_Env_Obj_move_a2 : forall (env : Env) (sch : Sch) (a : A),
    wf(env ::o ⟦⟨a⟩ sch⟧)
  -> wf(env ::a a ::o ⟦sch⟧).
Proof. intros. fresh_atom' empty. apply (wf_Env_Obj_noa_x _ _ x). eauto using wf_Env_Obj_x1. Qed.


(*** Unsorted *)
Theorem in_wf_env_impls_wf : forall (sch : Sch) (env : Env),
    SchSI.In sch (Env_Schs env)
  -> wf(env)
  -> env |=ty sch.
Proof.
  introv IN WF. induction WF; rewr in IN. crush. 1,3:eauto.
  indestr. eauto. rewr*. subst. eauto.
Qed.

Theorem fv_sch_in_wfenv_subset : forall (sch : Sch) (env : Env),
    SchSI.In sch (Env_Obj_Schs env)
  -> wf(env)
  -> free_exvars_Sch sch [<=] Env_Obj_exvars env.
Proof.
  introv IN WF. induction WF; rewr in IN.
  - crush.
  - crush.
  - indestr. eauto. rewr*. subst.
    transitivity (Env_exvars Env5). auto using fv_sch_wfty_subset. conv. reflexivity.
  - indestr. rewr. crush. rewr*. subst.
    transitivity (Env_exvars (Env5 ::a A5)). auto using fv_sch_wfty_subset. rewr. conv. crush.
Qed.

Theorem wf_Env_exvar_disj : forall (env1 env2 : Env),
    wf(env1 +++ env2)
  -> Env_Obj_exvars env1 [><] Env_Obj_exvars env2.
Proof.
  introv WF. induction env2.
  - crush.
  - inverts WF.
  - inverts WF. forwards IH: IHenv2. assumption.
    symmetry. rewr. apply disjoint_extend''.
    forwards [? ?]: FrA_props1. eassumption. rewr*. eapply disj_equiv_proper. reflexivity. 2:eassumption. crush.
    crush.
  - inverts WF. rewr. crush.
  - inverts WF. forwards IH: IHenv2. assumption.
    symmetry. rewr. apply disjoint_extend''.
    forwards [? ?]: FrA_props1. eassumption. rewr*. eapply disj_equiv_proper. reflexivity. 2:eassumption. crush.
    crush.
Qed.

Theorem subst_exvar_Env_notin_Env_idempotent : forall (env : Env) (ty : Ty) (exA : exvar),
    exA \notin Env_Obj_exvars env
  -> wf(env)
  -> subst_exvar_Env ty exA env = env.
Proof.
  introv NIE WF. induction WF.
  - crush.
  - crush.
  - simpl. rewr in NIE. rewrite IHWF; auto.
    forwards: fv_sch_wfty_subset. eassumption.
    rewrite subst_exvar_Sch_not_in_Sch_idempotent; auto.
  - simpl. rewr*. rewrite IHWF; auto.
    forwards: fv_sch_wfty_subset. eassumption.
    rewrite subst_exvar_Sch_not_in_Sch_idempotent. reflexivity.
    unfold not. intros. indestr. apply NIE. rewrite H in H0. indestr'.
Qed.

Theorem subst_exvar_Env_notinenv : forall (ty : Ty) (exA : exvar) (env : Env),
    exA \notin Env_Obj_exvars env
  -> wf(env)
  -> subst_exvar_Env ty exA env = env.
Proof.
   introv NIE WF. induction WF.
   - crush.
   - crush.
   - simpl in *. rewrite subst_exvar_Sch_not_in_Sch_idempotent. crush.
     forwards: WfTy_impls_free_exvar_sub. eassumption. rewr in NIE. fsetdec.
   - simpl in *. rewrite subst_exvar_Sch_not_in_Sch_idempotent. crush.
     unfold not. intros IS.
     forwards SUB: WfTy_impls_free_exvar_sub. eassumption. rewrite SUB in IS.
     apply NIE. rewr*. indestr'.
Qed.
