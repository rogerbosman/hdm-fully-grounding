(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Defs.DEnv.
Require Import Defs.Lc.
Require Import Defs.Set.
Require Import Defs.Substs.
Require Import Defs.WfDTy.

Notation "A |= B <= C" := (SubSump A B C) (at level 50) : type_scope.

Theorem SubSump_DEnv_sub : forall denv1 denv2 sch1 sch2,
    SubSump denv1 sch1 sch2
  -> denv1 [<=]de denv2
  -> SubSump denv2 sch1 sch2.
Proof.
  introv SS SUB. gen denv2. induction SS; intros.
  - auto.
  - econstructor. intros. apply H. eassumption. crush.
  - econstructor. intros. eapply WfDTy_DEnv_sub. 1,2:eassumption.
    eauto.
Qed.
#[export] Hint Resolve SubSump_DEnv_sub : core.

#[export] Instance SubSump_DEnv_sub_proper : Proper (DEnv_sub ==> eq ==> eq ==> impl) SubSump.
Proof. autounfold. intros. subst. eauto. Qed.

Lemma SubSump_weaken_subst : forall dskA dty denv2 denv1 sch1 sch2,
    SubSump denv1 sch1 sch2
  -> denv2 |=dty DS_Mono dty
  -> DEnv_dskvars denv1 [<=] DEnv_dskvars denv2 \u singleton dskA
  -> SubSump denv2 (subst_dskvar_DSch dty dskA sch1) (subst_dskvar_DSch dty dskA sch2).
Proof.
  introv SS WFDTY SUB. gen denv2. induction SS; intros.
  - crush.
  - eapply (SubSumpSkol (L \u singleton dskA)). fold subst_dskvar_DSch. intros.
    forwards: H dskA0. fsetdec. instantiate (1 := (denv2 :::s dskA0)). eauto. rewr. fsetdec.
    rewrite subst_dskvar_DSch_open_DSch_wrt_DTy_var. eassumption. fsetdec. eauto.
  - rename dty into dty1. rename DTy1 into dty2.
    eapply (SubSumpInst (L \u free_dskvars_DSch (subst_dskvar_DSch dty1 dskA DSch5) \u free_dskvars_DSch (subst_dskvar_DSch dty1 dskA DSch5) \u singleton dskA \u free_dskvars_DTy dty1) _ ).
    instantiate (1 := (subst_dskvar_DTy dty1 dskA dty2)).
    apply WfDTy_props. apply WfDTy_props in WFDTY. apply WfDTy_props in WFDTY0.
    destr. split. simpl.
    rewrite free_dskvars_DTy_subst_dskvar_DTy_upper. rewrite H0. fsetdec.
    constructor. crush.
    intros dskB NI__dskB. fold subst_dskvar_DSch.
    forwards IH: H. instantiate (1 := dskB). fsetdec. eassumption. eassumption. simpl in IH.
    rewrite subst_dskvar_DSch_open_DSch_wrt_DTy in IH. 2:eauto. simpl in IH. if_taut.
    rewrite subst_dskvar_DSch_open_DSch_wrt_DTy in IH. 2:eauto.
    rewrite subst_dskvar_DSch_subst_dskvar_DSch in IH. 2,3:fsetdec.
    rewrite subst_dskvar_DSch_open_DSch_wrt_DTy. simpl. if_taut.
    apply subst_dskvar_DTy_lc_DTy; eauto.
Qed.

Theorem SubSump_transitive (denv : DEnv) : Transitive (SubSump denv).
Proof.
  unfold Transitive. intros dsch1 dsch2 dsch3 SS1 SS2.
  gen dsch1 SS1. induction SS2.
  - intros. induction SS1; eauto.
  - eauto using SubSump_DEnv_sub.
  - intros dsch1 SS1.
    inverts SS1.
    forwards [dskA NI__dskA]: atom_fresh (L \u L0 \u free_dskvars_DSch dsch1).
    eapply (H dskA). fsetdec. forwards: SS0 dskA. fsetdec.
    apply (SubSump_weaken_subst dskA DTy1 DEnv5) in H0.
    rewrite subst_dskvar_DSch_not_in_DSch_idempotent in H0. eassumption. fsetdec. eassumption. rewr. fsetdec.
Qed.
