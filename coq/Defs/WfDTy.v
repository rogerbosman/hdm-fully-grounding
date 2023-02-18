(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Defs.DEnv.
Require Import Defs.Freevars.
Require Import Defs.Lc.
Require Import Defs.Set.
Require Import Defs.Substs.

(*** Notation, tactics etc*)
Notation "A |=dty B" := (WfDTy  A B) (at level 50)                   : type_scope.

(*** Props *)
Theorem WfDTy_props : forall (denv : DEnv) (dsch : DSch),
    denv |=dty dsch
  <-> ( free_dskvars_DSch dsch [<=] DEnv_dskvars denv
    /\ lc_DSch dsch ).
Proof.
  introv; split.
  - induction 1.
    + simpl. split. fsetdec. auto.
    + simpl. split. fsetdec. auto.
    + simpl. split. fsetdec. rewr*. jauto.
    + simpl. split.
      * unfold AtomSetImpl.Subset. intros dskA NIS.
        fresh_atom' (L \u singleton dskA).
        forwards IH: H x. fsetdec.
        rewrite <- free_dskvars_DSch_open_DSch_wrt_DTy_lower in IH.
        unfold AtomSetImpl.Subset in IH. apply IH in NIS.
        indestr. fsetdec. fsetdec.
      * constructor. intros.
        fresh_atom' (L \u free_dskvars_DSch DSch5).
        forwards [SUB LC]: H x. fsetdec.
        eapply (subst_dskvar_DSch_lc_DSch _ (DT_SkVar_f dskA) x) in LC. 2:{ auto. }
        rewrite subst_dskvar_DSch_open_DSch_wrt_DTy in LC. 2: auto. simpl in LC. if_taut.
        rewrite subst_dskvar_DSch_not_in_DSch_idempotent in LC; auto.
 - intros [SUB LC]. gen denv. LC_ind LC; intros; inv_LC.
   + crush.
   + crush.
   + constructor.
     apply IHLC__ty1. assumption. rewr*. fsetdec.
     apply IHLC__ty2. assumption. rewr*. fsetdec.
   + econstructor. instantiate (1 := {}). intros.
     apply H0. unfold AtomSetImpl.Subset. intros dskB IN.
     rewrite free_dskvars_DSch_open_DSch_wrt_DTy_upper in IN. indestr; crush.
Qed.

Corollary WfDTy_DSch_impls_dskvar_subset : forall (denv : DEnv) (dsch : DSch),
    denv |=dty dsch
  -> free_dskvars_DSch dsch [<=] DEnv_dskvars denv.
Proof. apply WfDTy_props. Qed.
Corollary WfDTy_DTy_impls_dskvar_subset : forall (denv : DEnv) (dty : DTy),
    denv |=dty (DS_Mono dty)
    -> free_dskvars_DTy dty [<=] DEnv_dskvars denv.
Proof. introv WFDTY. apply WfDTy_props in WFDTY. jauto. Qed.
#[export] Hint Resolve WfDTy_DSch_impls_dskvar_subset WfDTy_DTy_impls_dskvar_subset : core.

Corollary WfDTy_DSch_impls_lc : forall (denv : DEnv) (dsch : DSch),
    denv |=dty dsch
  -> lc_DSch dsch.
Proof. apply WfDTy_props. Qed.
Corollary WfDTy_DTy_impls_lc : forall (denv : DEnv) (dty : DTy),
    denv |=dty (DS_Mono dty)
  -> lc_DTy dty.
Proof. introv WFDTY. apply WfDTy_props in WFDTY. crush. Qed.
#[export] Hint Resolve WfDTy_DSch_impls_lc WfDTy_DTy_impls_lc : core.

(*** Rewriting *)
Theorem WfDTy_DEnv_sub : forall (denv1 denv2 : DEnv) (dsch : DSch),
    WfDTy denv1 dsch
  -> denv1 [<=]de denv2
  -> WfDTy denv2 dsch.
Proof. introv WFDTY SUB. rewrite WfDTy_props in *. crush. Qed.
#[export] Hint Resolve WfDTy_DEnv_sub : core.

#[export] Instance DEnv_sub_cons_a_proper : Proper (DEnv_sub ==> eq ==> impl) WfDTy.
Proof. autounfold. intros. subst. eauto. Qed.
