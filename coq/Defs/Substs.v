(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Defs.Env.
(* Require Import Defs.Embed. *)
(* Require Import Defs.Lc. *)
Require Import Defs.List.
Require Import Defs.OpenClose.
Require Import Defs.Obj.
Require Import Defs.Set.

(*** Notation, tactics etc*)

(*** subst_(d)skvar_(D)Ty/(D)Sch *)
(** Some idempotent sub applications *)
Theorem subst_dskvar_DTy_not_in_DTy_idempotent : forall (dty dty__in : DTy) (dskA : skvar),
    dskA \notin free_dskvars_DTy dty
  -> subst_dskvar_DTy dty__in dskA dty = dty.
Proof. introv NIS. induction dty; crush. ifdec; crush. Qed.

Theorem subst_dskvar_DSch_not_in_DSch_idempotent : forall (dsch : DSch) (dty__in : DTy) (dskA : skvar),
    dskA \notin free_dskvars_DSch dsch
  -> subst_dskvar_DSch dty__in dskA dsch = dsch.
Proof. introv NIS. induction dsch; crush. rewrite subst_dskvar_DTy_not_in_DTy_idempotent; auto. Qed.

Theorem subst_skvar_Ty_not_in_Ty_idempotent : forall (ty ty__in : Ty) (skA : skvar),
    skA \notin free_skvars_Ty ty
  -> subst_skvar_Ty ty__in skA ty = ty.
Proof. introv NIS. induction ty; crush. ifdec; crush. Qed.

Theorem subst_skvar_Sch_not_in_Sch_idempotent : forall (sch : Sch) (ty__in : Ty) (skA : skvar),
    skA \notin free_skvars_Sch sch
  -> subst_skvar_Sch ty__in skA sch = sch.
Proof. introv NIS. induction sch; crush. rewrite subst_skvar_Ty_not_in_Ty_idempotent; auto. Qed.

(*** subst_exvar_Ty/Sch *)
(** Simpl-based hints *)
Theorem subst_exvar_Ty_T_SkVar_b : forall (n : nat) (ty__in: Ty) (exA : exvar),
    subst_exvar_Ty ty__in exA (T_SkVar_b n) = T_SkVar_b n.
Proof. reflexivity. Qed.
#[export] Hint Rewrite subst_exvar_Ty_T_SkVar_b : core.

Theorem subst_exvar_Ty_T_SkVar_f : forall (skA : skvar) (ty__in: Ty) (exA : exvar),
    subst_exvar_Ty ty__in exA (T_SkVar_f skA) = T_SkVar_f skA.
Proof. reflexivity. Qed.
#[export] Hint Rewrite subst_exvar_Ty_T_SkVar_f : core.

Theorem subst_exvar_Ty_T_ExVar : forall (ty__in: Ty) (exA : exvar),
    subst_exvar_Ty ty__in exA (T_ExVar exA) = ty__in.
Proof. intros. simpl. if_taut. Qed.
#[export] Hint Rewrite subst_exvar_Ty_T_ExVar : core.

Theorem subst_exvar_Ty_T_Unit : forall (ty__in: Ty) (exA : exvar),
    subst_exvar_Ty ty__in exA (T_Unit) = T_Unit.
Proof. reflexivity. Qed.
#[export] Hint Rewrite subst_exvar_Ty_T_Unit : core.

Theorem subst_exvar_Ty_T_Fun : forall (ty1 ty2 : Ty) (ty__in: Ty) (exA : exvar),
    subst_exvar_Ty ty__in exA (T_Fun ty1 ty2) = T_Fun (subst_exvar_Ty ty__in exA ty1) (subst_exvar_Ty ty__in exA ty2).
Proof. reflexivity. Qed.
#[export] Hint Rewrite subst_exvar_Ty_T_Fun : core.

Theorem subst_exvar_Sch_mono : forall (ty ty__in: Ty) (exA : exvar),
    subst_exvar_Sch ty__in exA (S_Mono ty) = S_Mono (subst_exvar_Ty ty__in exA ty).
Proof. reflexivity. Qed.
#[export] Hint Rewrite subst_exvar_Sch_mono : core.

(** Some idempotent sub applications *)
Theorem subst_exvar_Ty_not_in_Ty_idempotent : forall (ty ty__in : Ty) (exA : exvar),
    exA \notin free_exvars_Ty ty
  -> subst_exvar_Ty ty__in exA ty = ty.
Proof. introv NIT. induction ty; crush. ifdec; crush. Qed.

Theorem subst_exvar_Sch_not_in_Sch_idempotent : forall (sch : Sch) (ty__in : Ty) (exA : exvar),
    exA \notin free_exvars_Sch sch
  -> subst_exvar_Sch ty__in exA sch = sch.
Proof. introv NIS. induction sch; crush. rewrite subst_exvar_Ty_not_in_Ty_idempotent; auto. Qed.

Theorem subst_exvar_Sch_subst_skvar_Sch : forall ty exA skA sch,
    exA \notin free_exvars_Sch sch
  -> subst_exvar_Sch ty exA (subst_skvar_Sch (T_ExVar exA) skA sch) = subst_skvar_Sch ty skA sch.
Proof. intros. Sch_Ty_ind sch; crush. ifdec; crush. if_taut. ifdec; crush. Qed.

(*** subst_(ex/sk)var_env *)
(** subst_exvar_env *)
Theorem subst_exvar_Env_app_distr : forall (env1 env2 : Env) (ty : Ty) (exA : exvar),
    subst_exvar_Env ty exA (env1 +++ env2) = (subst_exvar_Env ty exA env1) +++ (subst_exvar_Env ty exA env2).
Proof. induction env2; crush. Qed.
#[export] Hint Rewrite subst_exvar_Env_app_distr : core.

Theorem subst_exvar_Env_onea : forall (a : A) (ty : Ty) (exA : exvar),
    subst_exvar_Env ty exA <a>a = <a>a.
Proof. reflexivity. Qed.
#[export] Hint Rewrite subst_exvar_Env_onea : core.

Theorem subst_exvar_Env_consa : forall (env : Env) (a : A) (ty : Ty) (exA : exvar),
    subst_exvar_Env ty exA (env ::a a) = subst_exvar_Env ty exA env ::a a.
Proof. intros. norm. reflexivity. Qed.
#[export] Hint Rewrite subst_exvar_Env_consa : core.

Theorem subst_exvar_Env_subset : forall (ty : Ty) (exA : exvar) (env : Env),
    subst_exvar_Env ty exA env [<=]e# env.
Proof. introv. induction env; try destruct Obj5; crush. Qed.
#[export] Hint Resolve subst_exvar_Env_subset : core.

Theorem Env_exvars_subst_exvar_Env : forall (ty : Ty) (exA : exvar) (env : Env),
    Env_exvars (subst_exvar_Env ty exA env) = Env_exvars env.
Proof. induction env; crush. Qed.
#[export] Hint Rewrite Env_exvars_subst_exvar_Env : core.

Theorem Env_exvars_Obj_subst_exvar_Env : forall (ty : Ty) (exA : exvar) (env : Env),
    Env_Obj_exvars (subst_exvar_Env ty exA env) = Env_Obj_exvars env.
Proof. induction env; try destruct Obj5; crush. Qed.
#[export] Hint Rewrite Env_exvars_Obj_subst_exvar_Env : core.

Theorem subst_exvar_Env_s : forall (ty : Ty) (exA : exvar) (skA : skvar) (env : Env),
    subst_exvar_Env ty exA (env ::s skA) = (subst_exvar_Env ty exA env) ::s skA.
Proof. reflexivity. Qed.
Theorem subst_exvar_Env_a : forall (ty : Ty) (exA : exvar) (a : A) (env : Env),
    subst_exvar_Env ty exA (env ::a a) = (subst_exvar_Env ty exA env) ::a a.
Proof. reflexivity. Qed.
Theorem subst_exvar_Env_x : forall (ty : Ty) (exA : exvar) (x : termvar) (sch : Sch) (env : Env),
    subst_exvar_Env ty exA (env ::x x :- sch) = (subst_exvar_Env ty exA env) ::x x :- (subst_exvar_Sch ty exA sch).
Proof. reflexivity. Qed.
Theorem subst_exvar_Env_o : forall (ty : Ty) (exA : exvar) (a : A) (sch : Sch) (env : Env),
    subst_exvar_Env ty exA (env ::o ⟦⟨a⟩ sch⟧) = subst_exvar_Env ty exA env ::o ⟦⟨a⟩ subst_exvar_Sch ty exA sch⟧.
Proof. reflexivity. Qed.
#[export] Hint Rewrite subst_exvar_Env_s subst_exvar_Env_a subst_exvar_Env_x subst_exvar_Env_o : core.

(** subst_skvar_env *)
Theorem Env_skvars_subst_exvar_Env : forall (ty : Ty) (exA : exvar) (env : Env),
    Env_skvars (subst_exvar_Env ty exA env) = Env_skvars env.
Proof. induction env; crush. Qed.
#[export] Hint Rewrite Env_skvars_subst_exvar_Env : core.

(*** subst/open *)
Theorem subst_exvar_Sch_open_Sch_wrt_Ty_rec : forall (sch : Sch) (ty1 ty2 : Ty) (skA : skvar) (n : nat),
    lc_Ty ty1
  -> subst_exvar_Sch ty1 skA (open_Sch_wrt_Ty_rec n ty2 sch) = open_Sch_wrt_Ty_rec n (subst_exvar_Ty ty1 skA ty2) (subst_exvar_Sch ty1 skA sch).
Proof.
  introv LC.
  gen n. Sch_Ty_ind sch; intros.
  - simpl. destruct (lt_eq_lt_dec n n0); crush.
  - crush.
  - simpl. ifdec'; erewrite open_Ty_wrt_Ty_lc_Ty_rec; auto.
  - crush.
  - simpl.
    forwards IH1: IHTy1 n. inverts IH1.
    forwards IH2: IHTy2 n. inverts IH2.
    reflexivity.
  - crush.
Qed.

Theorem subst_exvar_Sch_open_Sch_wrt_Ty : forall (sch : Sch) (ty1 ty2 : Ty) (skA : skvar),
    lc_Ty ty1
  -> subst_exvar_Sch ty1 skA (open_Sch_wrt_Ty sch ty2) = open_Sch_wrt_Ty (subst_exvar_Sch ty1 skA sch) (subst_exvar_Ty ty1 skA ty2).
Proof. eauto using subst_exvar_Sch_open_Sch_wrt_Ty_rec. Qed.

