(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Defs.OpenClose.
Require Import Defs.Set.
Require Import Defs.Substs.

(*** Notation, tactics etc*)

(*** Simplification *)
(** free_dskvars*)
Theorem free_dskvars_DSch_Mono : forall (dty : DTy),
    free_dskvars_DSch (DS_Mono dty) = free_dskvars_DTy dty.
Proof. reflexivity. Qed.
#[export] Hint Rewrite free_dskvars_DSch_Mono : core.

Theorem free_dskvars_DTy_Fun : forall (dty1 dty2 : DTy),
    free_dskvars_DTy (DT_Fun dty1 dty2) = free_dskvars_DTy dty1 \u free_dskvars_DTy dty2.
Proof. reflexivity. Qed.
#[export] Hint Rewrite free_dskvars_DTy_Fun : core.

(** free_skvars *)
Theorem free_skvars_Sch_Mono : forall (ty : Ty),
    free_skvars_Sch (S_Mono ty) = free_skvars_Ty ty.
Proof. reflexivity. Qed.
#[export] Hint Rewrite free_skvars_Sch_Mono : core.

Theorem free_skvars_Ty_Fun : forall (dty1 dty2 : Ty),
    free_skvars_Ty (T_Fun dty1 dty2) = free_skvars_Ty dty1 \u free_skvars_Ty dty2.
Proof. reflexivity. Qed.
#[export] Hint Rewrite free_skvars_Ty_Fun : core.

Theorem free_skvars_skvar : forall skA,
    free_skvars_Ty (T_SkVar_f skA) = singleton skA.
Proof. reflexivity. Qed.
#[export] Hint Rewrite free_skvars_skvar : core.

(** free_exvars *)
Theorem free_exvars_Sch_Mono : forall (ty : Ty),
    free_exvars_Sch (S_Mono ty) = free_exvars_Ty ty.
Proof. reflexivity. Qed.
#[export] Hint Rewrite free_exvars_Sch_Mono : core.

Theorem free_exvars_Ty_Fun : forall (dty1 dty2 : Ty),
    free_exvars_Ty (T_Fun dty1 dty2) = free_exvars_Ty dty1 \u free_exvars_Ty dty2.
Proof. reflexivity. Qed.
#[export] Hint Rewrite free_exvars_Ty_Fun : core.

Theorem free_exvars_exvar : forall exA,
    free_exvars_Ty (T_ExVar exA) = singleton exA.
Proof. reflexivity. Qed.
#[export] Hint Rewrite free_exvars_exvar : core.

(*** Free_exvars + open *)
(** free_exvars *)
Theorem free_exvars_Ty_open_Ty_wrt_Ty_rec_lower : forall (n : nat) (ty1 ty2  : Ty),
  free_exvars_Ty ty1 [<=] free_exvars_Ty (open_Ty_wrt_Ty_rec n ty2 ty1).
Proof. intros. induction ty1; crush. Qed.
#[export] Hint Resolve free_exvars_Ty_open_Ty_wrt_Ty_rec_lower : core.

Theorem free_exvars_Sch_open_Sch_wrt_Ty_lower : forall (sch : Sch) (ty : Ty),
  free_exvars_Sch sch [<=] free_exvars_Sch (open_Sch_wrt_Ty sch ty).
Proof.
  intros. unfold open_Sch_wrt_Ty. generalize 0.
  induction sch; intros.
  - rewr*. eauto using free_exvars_Ty_open_Ty_wrt_Ty_rec_lower.
  - crush.
Qed.
#[export] Hint Resolve free_exvars_Sch_open_Sch_wrt_Ty_lower : core.

Theorem free_exvars_Ty_open_Ty_wrt_Ty_rec_upper : forall (n : nat) (ty1 ty2 : Ty),
  free_exvars_Ty (open_Ty_wrt_Ty_rec n ty2 ty1) [<=] union (free_exvars_Ty ty1) (free_exvars_Ty ty2).
Proof.
  intros. induction ty1. 2,3,4: crush. all: simpl in *.
  - ltdec. ifdec; crush. crush.
  - rewrite IHty1_1. rewrite IHty1_2. fsetdec.
Qed.

Theorem free_exvars_Sch_open_Sch_wrt_Ty_upper : forall (sch : Sch) (ty : Ty),
  free_exvars_Sch (open_Sch_wrt_Ty sch ty) [<=] free_exvars_Ty ty \u free_exvars_Sch sch.
Proof.
  intros. unfold open_Sch_wrt_Ty. generalize 0. induction sch; intros.
  - simpl. rewrite free_exvars_Ty_open_Ty_wrt_Ty_rec_upper. fsetdec.
  - crush.
Qed.

Theorem free_exvars_Ty_subst_exvar_Ty_upper_in_fv : forall (ty1 ty2 : Ty) (exA : exvar),
    exA \in free_exvars_Ty ty1
  -> free_skvars_Ty (subst_exvar_Ty ty2 exA ty1) [=] free_skvars_Ty ty2 \u free_skvars_Ty ty1.
Proof.
  introv NIT. induction ty1.
  - simpl. fsetdec.
  - simpl. fsetdec.
  - simpl in *. ifdec; fsetdec.
  - simpl. fsetdec.
  - simpl in *. apply union_iff in NIT. destr.
    + forwards IH1: IHty1_1. assumption. rewrite IH1.
      dec_In exA (free_exvars_Ty ty1_2).
      * forwards IH2: IHty1_2. assumption. rewrite IH2. fsetdec.
      * rewrite subst_exvar_Ty_not_in_Ty_idempotent. 2:assumption. fsetdec.
    (*Mirror of previous case*)
    + forwards IH2: IHty1_2. assumption. rewrite IH2.
      dec_In exA (free_exvars_Ty ty1_1).
      * forwards IH1: IHty1_1. assumption. rewrite IH1. fsetdec.
      * rewrite subst_exvar_Ty_not_in_Ty_idempotent. 2:assumption. fsetdec.
Qed.

Theorem free_skvars_Sch_subst_exvar_Sch_in_fv : forall (sch : Sch) (ty : Ty) (exA : exvar),
    exA \in free_exvars_Sch sch
  -> free_skvars_Sch (subst_exvar_Sch ty exA sch) [=] free_skvars_Ty ty \u free_skvars_Sch sch.
Proof.
  introv NIS. induction sch.
  - simpl. rewrite free_exvars_Ty_subst_exvar_Ty_upper_in_fv; crush.
  - simpl. rewrite IHsch; crush.
Qed.

(*** Free exvars + close *)
Theorem free_exvars_Sch_close_Sch_wrt_Ty : forall (skA : skvar) (sch : Sch),
    free_exvars_Sch (close_Sch_wrt_Ty skA sch) = free_exvars_Sch sch.
Proof.
  introv. unfold close_Sch_wrt_Ty. generalize 0. Sch_Ty_ind sch; intros. 3,4,5,6:crush.
  - simpl. ltdec; crush.
  - simpl. ifdec; crush.
Qed.

(*** Free exvars + subst *)
Theorem free_exvars_Sch_subst_skvar_Sch_upper : forall ty sch skA,
  free_exvars_Sch (subst_skvar_Sch ty skA sch) [<=] free_exvars_Sch sch \u free_exvars_Ty ty.
Proof.
  introv. Sch_Ty_ind sch. 1,3,4,6: crush. all: simpl.
  - ifdec; crush.
  - rewrite IHTy1. rewrite IHTy2. fsetdec.
Qed.

Theorem free_exvars_Ty_subst_exvar_Ty_upper : forall (ty ty__in : Ty) (exA : exvar),
    free_exvars_Ty (subst_exvar_Ty ty__in exA ty) [<=] free_exvars_Ty ty__in \u (Metatheory.remove exA (free_exvars_Ty ty)).
Proof.
  introv. induction ty. 1,2,4: crush.
  - simpl. ifdec. crush. rewr. fsetdec.
  - simpl. rewrite IHty1. rewrite IHty2. fsetdec.
Qed.

Theorem free_exvars_Sch_subst_exvar_Sch_upper : forall (sch : Sch) (ty : Ty) (exA : exvar),
    free_exvars_Sch (subst_exvar_Sch ty exA sch) [<=] free_exvars_Ty ty \u (Metatheory.remove exA (free_exvars_Sch sch)).
Proof.
  introv. induction sch.
  - simpl. eauto using free_exvars_Ty_subst_exvar_Ty_upper.
  - simpl. rewrite IHsch; crush.
Qed.

(*** Free skvars + subst *)
Theorem free_skvars_Ty_subst_exvar_Ty_upper : forall (ty ty__in : Ty) (exA : exvar),
    free_skvars_Ty (subst_exvar_Ty ty__in exA ty) [<=] free_skvars_Ty ty__in \u free_skvars_Ty ty.
Proof. introv. induction ty; crush. ifdec; crush. Qed.

Theorem free_skvars_Sch_subst_exvar_Sch_upper : forall (sch : Sch) (ty : Ty) (exA : exvar),
    free_skvars_Sch (subst_exvar_Sch ty exA sch) [<=] free_skvars_Ty ty \u free_skvars_Sch sch.
Proof.
  introv. induction sch.
  - simpl. eauto using free_skvars_Ty_subst_exvar_Ty_upper.
  - simpl. rewrite IHsch; crush.
Qed.

Theorem remove_free_skvars_Sch_subst_exvar_Sch : forall (skA : skvar) (exA : exvar) (sch : Sch),
    skA \notin free_skvars_Sch sch
  -> Metatheory.remove skA (free_skvars_Sch (subst_exvar_Sch (T_SkVar_f skA) exA sch)) [=] free_skvars_Sch sch.
Proof.
  introv NIS.
  dec_In exA (free_exvars_Sch sch).
  - rewrite free_skvars_Sch_subst_exvar_Sch_in_fv. simpl. fsetdec. assumption.
  - rewrite subst_exvar_Sch_not_in_Sch_idempotent. 2: assumption. fsetdec.
Qed.

Theorem free_exvars_Sch_subst_exvar_Sch_skA : forall (skA : skvar) (exA : exvar) (sch : Sch),
    free_exvars_Sch (subst_exvar_Sch (T_SkVar_f skA) exA sch) [=] Metatheory.remove exA (free_exvars_Sch sch).
Proof.
  introv. Sch_Ty_ind sch. 1,2,4,6:crush. all:simpl in *.
  - ifdec; simpl; fsetdec.
  - rewrite IHTy1. rewrite IHTy2. fsetdec.
Qed.
