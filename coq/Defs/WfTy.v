(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Defs.Env.
Require Import Defs.Freevars.
Require Import Defs.Lc.
Require Import Defs.Set.
Require Import Defs.Substs.

(*** Notation, tactics etc*)
Notation "A |=ty B" := (WfTy  A B) (at level 50)                   : type_scope.

Ltac inv_WfTy_ :=
  (* let H := fresh "H" in *)
  match goal with
    | [ H  : _ |=ty S_Mono (T_Fun _ _) |- _ ] => inverts H
  end.
Ltac inv_WfTy := repeat inv_WfTy_.

(*** Props *)
Theorem WfTy_props : forall (env : Env) (sch : Sch),
    env |=ty sch
  <-> ( free_skvars_Sch sch [<=] Env_skvars env
    /\ free_exvars_Sch sch [<=] Env_exvars env
    /\ lc_Sch sch ).
Proof.
  introv; split.
  - induction 1.
    + simpl. splits; fsetdec.
    + simpl. splits; fsetdec.
    + simpl. splits; fsetdec.
    + simpl. splits. 1,2:fsetdec. rewr*. jauto.
    + simpl. splits.
      * unfold AtomSetImpl.Subset. intros skA NIS.
        fresh_atom' (L \u singleton skA).
        forwards IH: H x. fsetdec. apply proj1 in IH. rewr in IH.
        rewrite <- free_skvars_Sch_open_Sch_wrt_Ty_lower in IH.
        rewrite IH in NIS. fsetdec.
      * fresh_atom. forwards IH: H x. eassumption. apply proj2 in IH. apply proj1 in IH. rewr in IH.
        transitivity (free_exvars_Sch (open_Sch_wrt_Ty Sch5 (T_SkVar_f x))); auto.
      * constructor. intros.
        fresh_atom' (L \u free_skvars_Sch Sch5).
        forwards [SUB__sk [SUB__ex LC]]: H x. fsetdec.
        eapply (subst_skvar_Sch_lc_Sch _ (T_SkVar_f skA) x) in LC. 2:{ auto. }
        rewrite subst_skvar_Sch_open_Sch_wrt_Ty in LC. 2: auto. simpl in LC. if_taut.
        rewrite subst_skvar_Sch_not_in_Sch_idempotent in LC; auto.
  - intros [SUB__sk [SUB__ex LC]]. gen env. LC_ind LC; intros; inv_LC.
    + crush.
    + crush.
    + crush.
    + rewr*. constructor.
      eapply IHLC__ty1. assumption. fsetdec. fsetdec.
      eapply IHLC__ty2. assumption. fsetdec. fsetdec.
   + econstructor. instantiate (1 := {}). intros.
     apply H0.
     * unfold AtomSetImpl.Subset. intros skB IN.
       rewrite free_skvars_Sch_open_Sch_wrt_Ty_upper in IN. indestr; crush.
     * unfold AtomSetImpl.Subset. intros skB IN.
       rewrite free_exvars_Sch_open_Sch_wrt_Ty_upper in IN. indestr; crush.
Qed.

Corollary WfTy_Sch_impls_lc : forall (env : Env) (sch : Sch),
    env |=ty sch
  -> lc_Sch sch.
Proof. apply WfTy_props. Qed.
Corollary WfTy_Ty_impls_lc : forall (env : Env) (ty : Ty),
    env |=ty S_Mono ty
  -> lc_Ty ty.
Proof. introv WFTY. apply WfTy_props in WFTY. rewr*. jauto. Qed.
#[export] Hint Resolve WfTy_Sch_impls_lc WfTy_Ty_impls_lc : core.

Corollary WfTy_impls_free_exvar_sub : forall (env : Env) (sch : Sch),
    env |=ty sch
  -> free_exvars_Sch sch [<=] Env_exvars env.
Proof. apply WfTy_props. Qed.

Corollary WfTy_props_mono : forall (env : Env) (ty : Ty),
    env |=ty (S_Mono ty)
  <-> ( free_skvars_Ty ty [<=] Env_skvars env
    /\ free_exvars_Ty ty [<=] Env_exvars env
    /\ lc_Ty ty ).
Proof. split. introv WFTY. apply WfTy_props in WFTY. crush. intros. apply WfTy_props. crush. Qed.
Corollary WfTy_props_mono1 : forall (env : Env) (ty : Ty),
    env |=ty (S_Mono ty)
  -> ( free_skvars_Ty ty [<=] Env_skvars env
    /\ free_exvars_Ty ty [<=] Env_exvars env
    /\ lc_Ty ty ).
Proof. apply WfTy_props_mono. Qed.
Corollary WfTy_props_mono2 : forall (env : Env) (ty : Ty),
    ( free_skvars_Ty ty [<=] Env_skvars env
    /\ free_exvars_Ty ty [<=] Env_exvars env
    /\ lc_Ty ty )
  -> env |=ty (S_Mono ty).
Proof. apply WfTy_props_mono. Qed.

(*** Rewriting *)
Theorem WfTy_Env_sub : forall (env1 env2 : Env) (sch : Sch),
    env1 |=ty sch
  -> env1 [<=]e env2
  -> env2 |=ty sch.
Proof. intros. rewrite WfTy_props in *. autounfold in *. destr. crush. Qed.
#[export] Hint Resolve WfTy_Env_sub : core.

#[export] Instance WfTy_Env_sub_inst : Proper (Env_sub ==> eq ==> impl) WfTy.
Proof. autounfold. intros. subst. eauto. Qed.

Theorem fv_sch_wfty_subset : forall (sch : Sch) (env : Env),
    env |=ty sch
  -> free_exvars_Sch sch [<=] Env_exvars env.
Proof.
  introv WFTY. induction WFTY; crush. fsetdec.
  fresh_atom.
  forwards: H. eassumption. rewr in H0.
  forwards REWR: free_exvars_Sch_open_Sch_wrt_Ty_lower. erewrite REWR. eassumption.
Qed.

Theorem WfTy_Env_eq : forall (env1 env2 : Env) (sch : Sch),
    env1 |=ty sch
  -> env1 [=]e env2
  -> env2 |=ty sch.
Proof. eauto. Qed.
#[export] Hint Resolve WfTy_Env_eq : core.

#[export] Instance WfTy_Env_eq_inst : Proper (Env_eq ==> eq ==> impl) WfTy.
Proof. autounfold. intros. subst. eauto. Qed.

(*** Inversion *)
Theorem WfTy_fun : forall (env : Env) (ty1 ty2 : Ty),
    env |=ty S_Mono (T_Fun ty1 ty2)
  -> env |=ty S_Mono ty1
  /\ env |=ty S_Mono ty2.
Proof. inversion 1. crush. Qed.
Corollary WfTy_fun1 : forall (env : Env) (ty1 ty2 : Ty),
    env |=ty S_Mono (T_Fun ty1 ty2)
  -> env |=ty S_Mono ty1.
Proof. apply WfTy_fun. Qed.
Corollary WfTy_fun2 : forall (env : Env) (ty1 ty2 : Ty),
    env |=ty S_Mono (T_Fun ty1 ty2)
  -> env |=ty S_Mono ty2.
Proof. apply WfTy_fun. Qed.
#[export] Hint Resolve WfTy_fun1 WfTy_fun2 : core.

(*** Unsorted *)
Theorem WfTy_subst : forall (env2 env1 : Env) (sch : Sch) (ty : Ty) (exA : exvar),
    env1 |=ty sch
  -> Metatheory.remove exA (Env_exvars env1) [<=] Env_exvars env2
  -> Env_skvars env1 [<=] Env_skvars env2
  -> env2 |=ty S_Mono ty
  -> env2 |=ty subst_exvar_Sch ty exA sch.
Proof.
  introv WFTY__sch SUB__ex SUB__sk WFTY__ty.
  apply WfTy_props in WFTY__sch. destruct WFTY__sch as [FVSK__sch [FVEX__sch LC__sch]].
  apply WfTy_props in WFTY__ty.  destruct WFTY__ty  as [FVSK__ty  [FVEX__ty  LC__ty ]].
  apply WfTy_props. splits.
  + rewrite free_skvars_Sch_subst_exvar_Sch_upper.
    rewrite FVSK__sch. rewrite FVSK__ty. fsetdec.
  + rewrite free_exvars_Sch_subst_exvar_Sch_upper.
    rewrite FVEX__sch. rewrite FVEX__ty. fsetdec.
  + auto using lc_Sch_subst_exvar_Sch'.
Qed.
