(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.
Require Import Defs.Defs.
Require Import Wf.Wf.

Lemma subst_exvar_Sch_close_Sch_wrt_Ty : forall sch ty__in exA skA,
    skA \notin free_skvars_Ty ty__in
  -> lc_Ty ty__in
  -> subst_exvar_Sch ty__in exA (close_Sch_wrt_Ty skA sch) = close_Sch_wrt_Ty skA (subst_exvar_Sch ty__in exA sch).
Proof.
  introv NIT LC. unfold close_Sch_wrt_Ty. generalize 0. Sch_Ty_ind sch; intros.
  - simpl. ifdec; reflexivity.
  - unfold close_Sch_wrt_Ty. crush. ifdec; crush.
  - crush. if_taut. unfold close_Sch_wrt_Ty. simpl. rewrite close_Ty_wrt_Ty_rec_involuntive; crush. crush.
  - crush.
  - forwards: IHTy1 n. forwards: IHTy2 n.
    unfold close_Sch_wrt_Ty in *. rewr*. crush.
  - unfold close_Sch_wrt_Ty. simpl. rewrite IHsch. reflexivity.
Qed.

(*** Overrides*)
Theorem DSub_app_close_Sch_wrt_Ty : forall (dsub : DSub) (skA : skvar) (sch : Sch),
    skA \notin DSub_codom_dskvars dsub
  -> DSub_lc dsub
  -> DSub_app (close_Sch_wrt_Ty skA sch) dsub = close_Sch_wrt_Ty skA (DSub_app sch dsub).
Proof.
  introv NID LC. DSub_ind dsub. crush. subdist.
  rewrite IHdsub0. rewrite subst_exvar_Sch_close_Sch_wrt_Ty. crush.
  rewrite free_skvars_Ty_DSub_codom_dskvars. eauto. rewr. fsetdec. rewrite emb_Ty_lc. apply LC. rewr. fsetdec.
  rewr in NID. fsetdec. eauto.
Qed.

Lemma Gen_complete__helper : forall dty__exA exA skA sch dsub,
    skA \notin free_skvars_Sch sch
  -> skA \notin DSub_codom_dskvars dsub
  -> DSub_unique ([(exA, dty__exA)] ++ dsub)
  -> subst_skvar_Sch (emb_Ty dty__exA) skA (DSub_app (subst_exvar_Sch (T_SkVar_f skA) exA sch) dsub) = DSub_app sch ([(exA, dty__exA)] ++ dsub).
Proof.
  introv NIT NIS UNI. Sch_Ty_ind sch; rewr.
  - crush.
  - crush. if_taut.
  - destruct (exA0 == exA).
    + subst. simpl. if_taut. rewr. simpl. if_taut.
      do_DSub_exA_decide dsub exA.
      * rewrite INV. rewr. reflexivity.
      * assert (dty = dty__exA). unfold DSub_unique in UNI. applys UNI exA. crush. crush.
        subst. rewrite EMB. rewr. reflexivity.
    + simpl. if_taut. rewr.
      do_DSub_exA_decide dsub exA0.
      * rewrite INV. simpl. if_taut.
      * rewrite EMB. rewr.
        rewrite subst_skvar_Ty_not_in_Ty_idempotent. reflexivity. eauto.
        rewrite free_skvars_Ty_DSub_codom_dskvars. eauto. eauto.
  - crush.
  - crush.
  - simpl. rewrite IHsch. reflexivity. crush.
Qed.

Theorem Gen_complete : forall ty dty dsub dsub__a denv dsch,
    DSub_app_t ty (dsub__a ++ dsub) = emb_Ty dty
  -> DSub_app (generalize_Sch (S_Mono ty) (DSub_to_A dsub__a) empty) dsub = emb_Sch dsch
  -> DSub_WfDTy denv (dsub__a ++ dsub)
  -> DSub_unique (dsub__a ++ dsub)
  -> SubSump denv dsch (DS_Mono dty).
Proof.
  introv EMB1 EMB2 WF UNI. gen dsub dsch denv. induction dsub__a as [|[exA dty__exA] dsub__a]; intros.
  - simpl in EMB2. rewr*. emb_auto''. rewrite EMB in EMB1. apply emb_Ty_inj in EMB1. crush.
  - rewrite (generalize_Sch_l_irrelevance (DSub_codom_dskvars dsub)) in EMB2.
    simpl in EMB2.
    remember (proj1_sig (atom_fresh (union (free_skvars_Sch (generalize_Sch (S_Mono ty) (DSub_to_A dsub__a) (DSub_codom_dskvars dsub))) (DSub_codom_dskvars dsub)))) as skA.
    emb_auto''.
    remember (proj1_sig (atom_fresh (union (free_skvars_Sch (generalize_Sch (S_Mono ty) (DSub_to_A dsub__a) (DSub_codom_dskvars dsub))) (DSub_codom_dskvars dsub)))) as skA.
    eapply (SubSumpInst (free_dskvars_DSch dsch0) _ _ _ dty__exA). apply WF. rewr. fsetdec. intros.
    rewrite <- subst_dskvar_DSch_intro. applys IHdsub__a ([(exA, dty__exA)] ++ dsub).
    rewrite app_assoc. rewrite DSub_app_t_app_distr. rewrite DSub_app_t_app_symm.
    subdist. subdist in EMB1. assumption. norm in UNI. eauto using DSub_unique_app_symm.
    eapply DSub_unique_rewr. eassumption. rewr_dsrel. fsetdec'.
    rewrite (generalize_Sch_l_irrelevance (DSub_codom_dskvars dsub)).
    remember (generalize_Sch (S_Mono ty) (DSub_to_A dsub__a) (DSub_codom_dskvars dsub)) as dsch__gen.
    rewrite embed_Sch_open_comm. rewrite <- EMB. rewrite DSub_app_close_Sch_wrt_Ty. rewrite <- subst_skvar_Sch_spec.
    rewrite Gen_complete__helper. reflexivity.
    1,2,4: subst; fresh_assert; fsetdec. eapply DSub_unique_rewr. eassumption. rewr_dsrel. fsetdec'. eauto.
    eapply DSub_WfDTy_rewr. eassumption. auto. rewr_dsrel. fsetdec'. assumption.
Qed.

Theorem subst_dskvar_DSch_generalize_DSch : forall dskA da dty sch,
     dskA \notin varl da
  -> varl da [><] free_dskvars_DTy dty
  -> lc_DTy dty
  -> subst_dskvar_DSch dty dskA (generalize_DSch sch da)
  = generalize_DSch (subst_dskvar_DSch dty dskA sch) da.
Proof.
  introv NID DISJ LC. da_ind da.
  - crush.
  - simpl. forwards: IHda.
    rewr in NID. fsetdec. rewr in DISJ. eapply disj_subset_proper; rewr. 3:eassumption. fsetdec. crush.
    rewrite <- H.
    rewrite subst_dskvar_DSch_close_DSch_wrt_DTy. reflexivity. assumption.
    destruct (dskA == dskA0). 2:assumption. subst. false. apply NID. rewr. fsetdec.
    eapply in_disjoint_impl_notin2.  eassumption. rewr. fsetdec.
Qed.

Definition subst_dskvar_DSub (dskA dskB : dskvar) : DSub -> DSub := map (fun pair => (fst pair, subst_dskvar_DTy (DT_SkVar_f dskA) dskB (snd pair))).

Theorem subst_dskvar_DSub_to_A : forall dsub dskA dskB,
    DSub_to_A (subst_dskvar_DSub dskB dskA dsub) = DSub_to_A dsub.
Proof. intros. induction dsub; crush. Qed.

Theorem subst_dskvar_DSub_app : forall dskA dskB dsub1 dsub2,
    subst_dskvar_DSub dskA dskB (dsub1 ++ dsub2)
  = subst_dskvar_DSub dskA dskB dsub1 ++ subst_dskvar_DSub dskA dskB dsub2.
Proof. induction dsub1; crush. Qed.
#[local] Hint Rewrite subst_dskvar_DSub_app : core.

Lemma DSub_app_t_exA_subst_dskvar_DSub : forall exA dskA dskB dsub dty,
    DSub_app_t (T_ExVar exA) dsub = emb_Ty dty
  -> DSub_app_t (T_ExVar exA) (subst_dskvar_DSub dskA dskB dsub) = emb_Ty (subst_dskvar_DTy (DT_SkVar_f dskA) dskB dty).
Proof.
  introv EMB. rev_DSub_ind dsub.
  - rewr in EMB. emb_auto''. contradiction.
  - rewr. simpl. rewr. subdist. simpl.
    ifdec.
    + subst. rewr. subdist in EMB. apply emb_Ty_inj in EMB. crush.
    + apply IHdsub0. rewr in EMB. subdist in EMB. simpl in EMB.
      if_taut.
Qed.

Lemma DGen_complete__helper : forall dsub__a ty dsub dty dskB dskA,
    DSub_app_t ty (dsub__a ++ dsub) = emb_Ty dty
  -> dskB \notin DSub_codom_dskvars dsub
  -> dskB \notin free_skvars_Ty ty
  -> DSub_app_t ty ((subst_dskvar_DSub dskA dskB dsub__a) ++ dsub)
  = emb_Ty (subst_dskvar_DTy (DT_SkVar_f dskA) dskB dty).
Proof.
  introv EMB NID NIT. gen dty. induction ty; intros; emb_auto''.
  - subdist. simpl. reflexivity.
  - subdist. simpl. ifdec. false. apply NIT. rewr. fsetdec. crush.
  - do_DSub_exA_decide dsub exA.
    + subdist*. rewrite INV in *.
      do_DSub_exA_decide dsub__a exA.
      * rewrite INV0 in EMB. emb_auto''. contradiction.
      * eauto using DSub_app_t_exA_subst_dskvar_DSub.
    + subdist. rewrite EMB0. rewr. subdist in EMB. rewrite EMB0 in EMB. rewr in EMB. apply emb_Ty_inj in EMB. subst.
      rewrite subst_dskvar_DTy_not_in_DTy_idempotent. reflexivity.
      rewrite <- free_skvars_Ty_embed_Ty.
      rewrite free_skvars_Ty_DSub_codom_dskvars. 2:eauto. eassumption.
  - crush.
  - subdist.
    forwards IH1: IHty1. rewr in NIT. fsetdec. eassumption. subdist in IH1. rewrite IH1.
    forwards IH2: IHty2. rewr in NIT. fsetdec. eassumption. subdist in IH2. rewrite IH2.
    simpl. reflexivity.
Qed.

Theorem subst_dskvar_DSub_lookup : forall exA dty dsub dskA dskB,
    DTyPSI.In (exA, dty) (DSub_bindings (subst_dskvar_DSub dskB dskA dsub))
  -> exists dty', subst_dskvar_DTy (DT_SkVar_f dskB) dskA dty' = dty /\ DTyPSI.In (exA, dty') (DSub_bindings dsub).
Proof.
  intros. DSub_ind dsub.
  - crush.
  - simpl in H. rewr in H. indestr.
    + rewr in H. destr. exists. crush.
    + forwards: IHdsub0. eassumption. destr. exists. crush.
Qed.

Theorem DSub_unique_subst_dskvar_DSub : forall dsub dskA dskB,
    DSub_unique dsub
  -> DSub_unique (subst_dskvar_DSub dskB dskA dsub).
Proof.
  introv UNI. unfold DSub_unique. intros.
  apply subst_dskvar_DSub_lookup in H. apply subst_dskvar_DSub_lookup in H0. destr.
  forwards: UNI. apply H1. apply H2. crush.
Qed.

Theorem DSub_WfDTy_subst : forall denv1 denv2 dsub dskA dskB,
    DSub_WfDTy denv1 dsub
  -> Metatheory.remove dskA (DEnv_dskvars denv1) \u singleton dskB [<=] DEnv_dskvars denv2
  -> DSub_WfDTy denv2 (subst_dskvar_DSub dskB dskA dsub).
Proof.
  introv WF SUB. induction dsub.
  - crush.
  - unfold DSub_WfDTy. intros. rewr in H. indestr.
    + destruct a as [exA dty']. rewr in H. subst.
      assert (denv1 |=dty DS_Mono dty'). apply WF. rewr. fsetdec.
      apply WfDTy_props in H. apply WfDTy_props. split. 2:crush.
      simpl. rewrite free_dskvars_DTy_subst_dskvar_DTy_upper. rewrite <- SUB.
      destr. simpl in H. rewrite H. simpl. fsetdec.
    + apply IHdsub. eauto. assumption.
Qed.

Theorem subst_dskvar_DSub_notincodom_involuntive : forall dskA dskB dsub,
    dskA \notin DSub_codom_dskvars dsub
  -> subst_dskvar_DSub dskB dskA dsub = dsub.
Proof.
  intros. DSub_ind dsub. crush.
  simpl.
  asserts_rewrite (subst_dskvar_DTy (DT_SkVar_f dskB) dskA dty = dty).
    assert (dskA \notin free_dskvars_DTy dty).
    rewrite <- free_skvars_Ty_embed_Ty. rewrite free_skvars_Ty_DSub_codom_dskvars. eassumption.
    rewr. fsetdec'. crush.
  rewrite IHdsub0. reflexivity. rewr in H. fsetdec.
Qed.


Theorem DGen_complete : forall da ty dty dsub dsub__a denv dsch,
    DSub_app_t ty (dsub__a ++ dsub) = emb_Ty dty
  -> DSub_app (generalize_Sch (S_Mono ty) (DSub_to_A dsub__a) empty) dsub = emb_Sch dsch
  -> DSub_WfDTy  denv          dsub
  -> DSub_WfDTy (denv :::a da) dsub__a
  -> DSub_unique (dsub__a ++ dsub)
  -> varl da [><] DSub_codom_dskvars dsub
  -> varl da [><] free_skvars_Ty ty
  -> NoDup' da
  -> SubSump denv dsch (generalize_DSch (DS_Mono dty) da).
Proof.
  introv EMB1 EMB2 WF1 WF2 UNI DISJ1 DISJ2 ND. gen dsub__a dty dsch denv. da_ind da; intros.
  - simpl in WF2.
    assert (DSub_WfDTy denv (dsub__a ++ dsub)). apply DSub_WfDTy_app; assumption.
    eapply Gen_complete; eassumption.
  - intros. simpl. eapply (SubSumpSkol (varl da)). intros dskB NI__dskB. rewrite <- subst_dskvar_DSch_spec.
    rewrite subst_dskvar_DSch_generalize_DSch. simpl. applys IHda (subst_dskvar_DSub dskB dskA dsub__a).
    + eapply disj_subset_proper. 3:apply DISJ1. rewr. crush. crush.
    + eapply disj_subset_proper. 3:apply DISJ2. rewr. crush. crush.
    + inverts ND. eassumption.
    + forwards: subst_dskvar_DSub_notincodom_involuntive dskA dskB dsub.
      eapply in_disjoint_impl_notin2. eassumption. rewr. fsetdec.
      rewrite <- H. rewrite <- subst_dskvar_DSub_app. auto using DSub_unique_subst_dskvar_DSub.
    + apply DGen_complete__helper. eassumption.
      eapply in_disjoint_impl_notin2. eassumption. rewr. crush.
      eapply in_disjoint_impl_notin2. eassumption. rewr. crush.
    + rewrite subst_dskvar_DSub_to_A in *. eassumption.
    + eauto.
    + eapply DSub_WfDTy_subst. eassumption. rewr_derel. fsetdec.
    + inverts ND. eassumption.
    + unfold AtomSetImpl.disjoint. simpl. fsetdec.
    + auto.
Qed.

Theorem free_dskvars_DSch_generalize_DSch : forall dsch da,
    free_dskvars_DSch (generalize_DSch dsch da) [<=] free_dskvars_DSch dsch.
Proof.
  intros. induction da. crush.
  simpl. simpl. rewrite free_dskvars_DSch_close_DSch_wrt_DTy. rewrite IHda. crush.
Qed.

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

Theorem DGen_complete' : forall da ty dty dsub dsub__a denv dsch da__disj,
    DSub_app_t ty (dsub__a ++ dsub) = emb_Ty dty
  -> DSub_app (generalize_Sch (S_Mono ty) (DSub_to_A dsub__a) empty) dsub = emb_Sch dsch
  -> DSub_WfDTy denv dsub
  -> DSub_WfDTy (denv :::a da) dsub__a
  -> DSub_unique (dsub__a ++ dsub)
  -> varl da     [><] DSub_codom_dskvars dsub
  -> varl da     [><] free_skvars_Ty ty
  -> varl da__disj [><] free_dskvars_DTy dty
  -> NoDup' da
  -> SubSump denv dsch (generalize_DSch (generalize_DSch (DS_Mono dty) da) da__disj).
Proof.
  intros. induction da__disj.
  - simpl. eapply DGen_complete; eassumption.
  - simpl. apply (SubSumpSkol empty). intros.
    rewrite <- subst_dskvar_DSch_spec. rewrite subst_dskvar_DSch_not_in_DSch_idempotent.
    eapply SubSump_DEnv_sub. apply IHda__disj. eapply disj_subset_proper. 3:eassumption. rewr. crush. crush. crush.
    do 2 rewrite free_dskvars_DSch_generalize_DSch. eapply in_disjoint_impl_notin2. eassumption. rewr. crush.
Qed.

Theorem generalize_DSch_app : forall da1 da2 sch,
    generalize_DSch sch (da2 ++ da1) = generalize_DSch (generalize_DSch sch da1) da2.
Proof. induction da2; crush. Qed.
