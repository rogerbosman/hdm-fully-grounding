(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Defs.DEnv.
(* Require Import Defs.List. *)
(* Require Import Defs.DObj. *)
(* Require Import Defs.Set. *)
(* Require Import Defs.Substs. *)

(* Require Import Defs.FrA. *)
(* Require Import Defs.WfTy. *)

(*** Notation, tactics etc*)
Notation "wfd( A )" := (WfDEnv A) (at level 50, format "wfd( A )") : type_scope.

(* Ltac inv_Wf_ := *)
(*   match goal with *)
(*     | [ H : wfd(_ :::s _)  |- _ ] => inverts H *)
(*     | [ H : wfd(_ :::a _)  |- _ ] => inverts H *)
(*     | [ H : wfd(_ :::x _ :- _)  |- _ ] => inverts H *)
(*     | [ H : wfd(_ :::o _)  |- _ ] => inverts H *)
(*   end. *)
(* Ltac inv_Wf := repeat inv_Wf_. *)
(* Ltac inv_Wf' := repeat (inv_Wf; inv_FrA). *)

(*** Weakening *)
Theorem WfDEnv_weak_app : forall (denv1 denv2 : DEnv),
    wfd(denv1 ++++ denv2)
  -> wfd(denv1).
Proof. introv WF. induction denv2; inverts WF; crush. Qed.
#[export] Hint Resolve WfDEnv_weak_app : core.

Theorem WfDEnv_weak_cons_s : forall (dskA : dskvar) (denv : DEnv),
    wfd(denv :::s dskA)
  -> wfd(denv).
Proof. introv WF. inverts WF. auto. Qed.
#[export] Hint Resolve WfDEnv_weak_cons_s : core.

Theorem WfDEnv_weak_cons_a : forall (da : DA) (denv : DEnv),
    wfd(denv :::a da)
  -> wfd(denv).
Proof. introv WF. induction da. crush. inverts WF. eauto. Qed.
#[export] Hint Resolve WfDEnv_weak_cons_a : core.

Theorem WfDEnv_weak_cons_x : forall (x : termvar) (dsch : DSch) (denv : DEnv),
    wfd(denv :::x x :- dsch)
  -> wfd(denv).
Proof. introv WF. norm*. eauto. Qed.
#[export] Hint Resolve WfDEnv_weak_cons_x : core.

Theorem WfDEnv_weak_cons_o : forall (dobj : DObj) (denv : DEnv),
    wfd(denv :::o dobj)
  -> wfd(denv).
Proof. introv WF. norm*. eauto. Qed.
#[export] Hint Resolve WfDEnv_weak_cons_o : core.

Theorem WfDEnv_oneDA : forall denv da,
    wfd(denv ++++ <da>da)
  <-> wfd(denv) /\ DFrA da denv.
Proof.
  intros. induction da. crush. split.
  - introv WFD. inverts WFD. split. eauto.
    forwards: IHda. constructor. apply H. eauto. rewr. rewr in FR. fsetdec.
  - intros. destr. inverts H0.
    forwards<: IHda. jauto.
    simpl. constructor. eauto. rewr. rewr in DFR. fsetdec.
Qed.

(* Theorem WfDEnv_weak_app_onea_cons : forall (exA : exvar) (a : A) (denv : DEnv), *)
(*     wfd(denv ++++ <exA ::: a>a) *)
(*   -> wfd(denv ++++ <      a>a). *)
(* Proof. introv WF. inverts WF. constructor; eauto. Qed. *)
(* #[export] Hint Resolve WfDEnv_weak_app_onea_cons : core. *)

(* Theorem WfDEnv_weak_app_onea_app : forall (a1 a2 : A) (denv : DEnv), *)
(*     wfd(denv ++++ <a2 ++ a1>a) *)
(*   -> wfd(denv ++++ <      a1>a). *)
(* Proof. introv WF. inverts WF. constructor; eauto 6. Qed. *)
(* #[export] Hint Resolve WfDEnv_weak_app_onea_app : core. *)

(* (*** Inversion *) *)
(* Theorem WfDEnv_inv_app_onea : forall (a : A) (denv : DEnv), *)
(*     wfd(denv ++++ <a>a) *)
(*   -> FrA a denv. *)
(* Proof. inversion 1. trivial. Qed. *)
(* #[export] Hint Resolve WfDEnv_inv_app_onea : core. *)

(* Theorem WfDEnv_inv_cons_a : forall (a : A) (denv : DEnv), *)
(*     wfd(denv :::a a) *)
(*   -> FrA a denv. *)
(* Proof. intros. norm*. eauto. Qed. *)
(* #[export] Hint Resolve WfDEnv_inv_cons_a : core. *)

(* Theorem WfDEnv_inv_cons_x : forall (x : termvar) (dsch : DSch) (denv : DEnv), *)
(*     wfd(denv :::x x :- dsch) *)
(*   -> denv |=ty dsch. *)
(* Proof. intros. inv_Wf. assumption. Qed. *)
(* #[export] Hint Resolve WfDEnv_inv_cons_x : core. *)

(* Theorem wf_Env_inv_o : forall (denv : DEnv) (a : A) (dsch : DSch), *)
(*     wfd(denv :::o ⟦⟨a⟩ dsch⟧) *)
(*   -> denv :::a a |=ty dsch. *)
(* Proof. inversion 1; assumption. Qed. *)
(* #[export] Hint Resolve wf_Env_inv_o : core. *)


(* (*** Wf-ness of objects*) *)
(* Theorem wf_Env_Obj_x : forall (denv : DEnv) (dsch : DSch) (x : termvar) (a : A), *)
(*     wfd(denv :::o ⟦⟨a⟩ dsch⟧) *)
(*   <-> wfd(denv :::a a :::x x :- dsch). *)
(* Proof. split; intros; inv_Wf; crush. Qed. *)
(* Corollary wf_Env_Obj_x1 : forall (denv : DEnv) (dsch : DSch) (x : termvar) (a : A), *)
(*     wfd(denv :::o ⟦⟨a⟩ dsch⟧) *)
(*   -> wfd(denv :::a a :::x x :- dsch). *)
(* Proof. apply wf_Env_Obj_x. Qed. *)
(* Corollary wf_Env_Obj_x2 : forall (denv : DEnv) (dsch : DSch) (x : termvar) (a : A), *)
(*     wfd(denv :::a a :::x x :- dsch) *)
(*   -> wfd(denv :::o ⟦⟨a⟩ dsch⟧). *)
(* Proof. apply wf_Env_Obj_x. Qed. *)
(* #[export] Hint Resolve wf_Env_Obj_x1 wf_Env_Obj_x2 : slow. *)

(* Theorem wf_Env_Obj_noa_x : forall (denv : DEnv) (dsch : DSch) (x : termvar), *)
(*     wfd(denv :::o ⟦dsch⟧) *)
(*   <-> wfd(denv :::x x :- dsch). *)
(* Proof. split; intros; inv_Wf. constructor. auto. eapply WfTy_Env_sub. eassumption. auto. eauto. Qed. *)

(* Corollary wf_Env_Obj_noa_x1 : forall (denv : DEnv) (dsch : DSch) (x : termvar), *)
(*     wfd(denv :::o ⟦dsch⟧) *)
(*   -> wfd(denv :::x x :- dsch). *)
(* Proof. apply wf_Env_Obj_noa_x. Qed. *)
(* Corollary wf_Env_Obj_noa_x2 : forall (denv : DEnv) (dsch : DSch) (x : termvar), *)
(*     wfd(denv :::x x :- dsch) *)
(*   -> wfd(denv :::o ⟦dsch⟧). *)
(* Proof. apply wf_Env_Obj_noa_x. Qed. *)
(* #[export] Hint Resolve wf_Env_Obj_noa_x1 wf_Env_Obj_noa_x2 : slow. *)

(* Corollary wf_Env_Obj_move_a1 : forall (denv : DEnv) (dsch : DSch) (a : A), *)
(*     wfd(denv :::a a :::o ⟦dsch⟧) *)
(*   -> wfd(denv :::o ⟦⟨a⟩ dsch⟧). *)
(* Proof. intros. fresh_atom' empty. apply (wf_Env_Obj_x _ _ x). auto using wf_Env_Obj_noa_x1. Qed. *)
(* Corollary wf_Env_Obj_move_a2 : forall (denv : DEnv) (dsch : DSch) (a : A), *)
(*     wfd(denv :::o ⟦⟨a⟩ dsch⟧) *)
(*   -> wfd(denv :::a a :::o ⟦dsch⟧). *)
(* Proof. intros. fresh_atom' empty. apply (wf_Env_Obj_noa_x _ _ x). eauto using wf_Env_Obj_x1. Qed. *)


(* (*** Unsorted *) *)
(* Theorem in_wf_env_impls_wf : forall (dsch : DSch) (denv : DEnv), *)
(*     SchSI.In dsch (Env_Schs denv) *)
(*   -> wfd(denv) *)
(*   -> denv |=ty dsch. *)
(* Proof. *)
(*   introv IN WF. induction WF; rewr in IN. crush. 1,3:eauto. *)
(*   indestr. eauto. rewr*. subst. eauto. *)
(* Qed. *)

(* Theorem fv_sch_in_wfenv_subset : forall (dsch : DSch) (denv : DEnv), *)
(*     SchSI.In dsch (Env_Obj_Schs denv) *)
(*   -> wfd(denv) *)
(*   -> free_exvars_Sch dsch [<=] Env_Obj_exvars denv. *)
(* Proof. *)
(*   introv IN WF. induction WF; rewr in IN. *)
(*   - crush. *)
(*   - crush. *)
(*   - indestr. eauto. rewr*. subst. *)
(*     transitivity (Env_exvars Env5). auto using fv_sch_wfty_subset. conv. reflexivity. *)
(*   - indestr. rewr. crush. rewr*. subst. *)
(*     transitivity (Env_exvars (Env5 :::a A5)). auto using fv_sch_wfty_subset. rewr. conv. crush. *)
(* Qed. *)

(* Theorem wf_Env_exvar_disj : forall (denv1 denv2 : DEnv), *)
(*     wfd(denv1 ++++ denv2) *)
(*   -> Env_Obj_exvars denv1 [><] Env_Obj_exvars denv2. *)
(* Proof. *)
(*   introv WF. induction denv2. *)
(*   - crush. *)
(*   - inverts WF. *)
(*   - inverts WF. forwards IH: IHenv2. assumption. *)
(*     symmetry. rewr. apply disjoint_extend''. *)
(*     forwards [? ?]: FrA_props1. eassumption. rewr*. eapply disj_equiv_proper. reflexivity. 2:eassumption. crush. *)
(*     crush. *)
(*   - inverts WF. rewr. crush. *)
(*   - inverts WF. forwards IH: IHenv2. assumption. *)
(*     symmetry. rewr. apply disjoint_extend''. *)
(*     forwards [? ?]: FrA_props1. eassumption. rewr*. eapply disj_equiv_proper. reflexivity. 2:eassumption. crush. *)
(*     crush. *)
(* Qed. *)

(* Theorem subst_exvar_Env_notin_Env_idempotent : forall (denv : DEnv) (ty : Ty) (exA : exvar), *)
(*     exA \notin Env_Obj_exvars denv *)
(*   -> wfd(denv) *)
(*   -> subst_exvar_Env ty exA denv = denv. *)
(* Proof. *)
(*   introv NIE WF. induction WF. *)
(*   - crush. *)
(*   - crush. *)
(*   - simpl. rewr in NIE. rewrite IHWF; auto. *)
(*     forwards: fv_sch_wfty_subset. eassumption. *)
(*     rewrite subst_exvar_Sch_not_in_Sch_idempotent; auto. *)
(*   - simpl. rewr*. rewrite IHWF; auto. *)
(*     forwards: fv_sch_wfty_subset. eassumption. *)
(*     rewrite subst_exvar_Sch_not_in_Sch_idempotent. reflexivity. *)
(*     unfold not. intros. indestr. apply NIE. rewrite H in H0. indestr'. *)
(* Qed. *)

(* Theorem subst_exvar_Env_notinenv : forall (ty : Ty) (exA : exvar) (denv : DEnv), *)
(*     exA \notin Env_Obj_exvars denv *)
(*   -> wfd(denv) *)
(*   -> subst_exvar_Env ty exA denv = denv. *)
(* Proof. *)
(*    introv NIE WF. induction WF. *)
(*    - crush. *)
(*    - crush. *)
(*    - simpl in *. rewrite subst_exvar_Sch_not_in_Sch_idempotent. crush. *)
(*      forwards: WfTy_impls_free_exvar_sub. eassumption. rewr in NIE. fsetdec. *)
(*    - simpl in *. rewrite subst_exvar_Sch_not_in_Sch_idempotent. crush. *)
(*      unfold not. intros IS. *)
(*      forwards SUB: WfTy_impls_free_exvar_sub. eassumption. rewrite SUB in IS. *)
(*      apply NIE. rewr*. indestr'. *)
(* Qed. *)
