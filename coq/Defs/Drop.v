(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Defs.Env.

Require Import Defs.List.
Require Import Defs.FrA.
Require Import Defs.WfEnv.

(*** Notation, tactics etc*)
Lemma Env_drop_distr : forall (n : nat) (env1 env2 : Env),
    Env_drop n (env1 +++ env2) = (Env_drop (n - (Env_length env2)) env1) +++ (Env_drop n env2).
Proof. introv. gen n. induction env2; destruct n; crush. Qed.
#[export] Hint Rewrite Env_drop_distr : dropdistr.

Ltac dropdistr := autorewrite with core dropistr.
Tactic Notation "dropdistr*" := autorewrite with core dropdistr in *.

(*** Distr and comm *)
Lemma Env_drop_distr' : forall (n : nat) (env1 env2 : Env),
    env1 +++ (Env_drop n env2) = Env_drop (min n (Env_length env2)) (env1 +++ env2).
Proof. introv. gen n. induction env2; destruct n; crush. Qed.

Lemma nat_minus_greater : forall (n1 n2 : nat),
    n1 <= n2
  -> n1 - n2 = 0.
Proof. crush. Qed.

Theorem Env_drop_subst_exvar_Env_comm : forall (n : nat) (ty : Ty) (exA : exvar) (env : Env),
    Env_drop n (subst_exvar_Env ty exA env) = subst_exvar_Env ty exA (Env_drop n env).
Proof. introv. gen n. induction env; destruct n; crush. Qed.

Theorem Env_drop_zero : forall (env : Env),
    Env_drop 0 env = env.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Env_drop_zero : core.

(*** Judgments maintained under drop *)
Lemma wf_Env_drop_geq : forall (n1 n2 : nat) (env : Env),
    wf(Env_drop n1 env)
  -> n2 >= n1
  -> wf(Env_drop n2 env).
Proof.
  intros n1 n2 Env WF GEQ. gen n1 n2. induction Env; crush; destruct GEQ; try assumption.
  - destruct n1. crush. inverts WF. eauto.
  - destruct n1.
    + crush. inverts WF.
    + crush. eapply IHEnv. eassumption. crush.
  - destruct n1.
    + crush. inverts WF. eapply (IHEnv 0). auto. auto.
    + crush. eapply IHEnv. eassumption. crush.
  - destruct n1.
    + crush. inverts WF. eapply (IHEnv 0). auto. auto.
    + crush. eapply IHEnv. eassumption. crush.
  - destruct n1.
    + crush. inverts WF. eapply (IHEnv 0). auto. auto.
    + crush. eapply IHEnv. eassumption. crush.
Qed.

Corollary wf_Env_drop : forall (n : nat) (env : Env),
    wf(env)
  -> wf(Env_drop n env).
Proof. intros. eapply (wf_Env_drop_geq 0 n); crush. Qed.
#[export] Hint Resolve wf_Env_drop : core.

Theorem Env_drop_sub : forall (n : nat) (env : Env),
    Env_drop n env [<=]e# env.
Proof. introv. gen n. induction env; destruct n; eauto; transitivity env; eauto. Qed.

Theorem Env_drop_Env_exvars_Obj : forall (n : nat) (env : Env),
    Env_Obj_exvars (Env_drop n env) [<=] Env_Obj_exvars env.
Proof. introv. forwards: Env_drop_sub n env. unfold Env_fr_sub in *. jauto. Qed.

Theorem FrA_drop : forall (n : nat) (a : A) (env : Env),
    FrA a env
  -> FrA a (Env_drop n env).
Proof. introv FR. eapply FrA_rewr. eassumption. auto. auto using Env_drop_sub. Qed.


(*** Unsorted *)
Lemma Env_drop_greater : forall (n : nat) (env : Env),
    n >= Env_length env
  -> Env_drop n env = Env_Empty.
Proof. introv. gen n. induction env; destruct n; crush; unfold const in *; crush. Qed.

Lemma nat_greater_decompose : forall (n1 n2 : nat),
    n1 > n2
  -> exists n2', n1 = plus n2' n2.
Proof.
  intros n1 n2 H. induction H.
  - exists (S O). crush.
  - destruct IHle. exists (S x). crush.
Qed.
