(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.
Require Import Defs.Defs.
Require Import Wf.Wf.

Require Import Complete.InfGenComplete.
Require Import Complete.SameShape.
Require Import Complete.InfGenRename.
Require Import Complete.Unification.

Require Import Complete.DEnvComplRel.
Require Import Complete.Sch_or_Obj.

Require Import Complete.Generalisation.

(*** Lemmas *)

Lemma complete_var__helper : forall denv dsch dty dsub sch env,
    SubSump denv dsch (DS_Mono dty)
  -> DSub_app sch dsub = emb_Sch dsch
  -> DSub_wf denv dsub
  -> exists ty dsub',
      env |= sch ≤ ⟨DSub_to_A dsub'⟩ ty
    /\ DSub_app_t ty (dsub' ++ dsub) = emb_Ty dty
    /\ DSub_wf denv (dsub' ++ dsub).
Proof.
  introv SS EMB WF__sub. gen sch env dsub. dependent induction SS; intros.
  - destruct sch; crush.
    exists Ty5 (nil:DSub). crush.
  - emb_auto.
    forwards [exA NIl]: atom_fresh (Env_Obj_exvars env \u DSub_dom dsub \u free_exvars_Sch sch0).
    forwards [dskA NIl']: atom_fresh (L \u free_skvars_Sch sch0 \u DSub_codom_dskvars dsub).
    (** forwards with a generated dskA here, because we don't get access to the
    "actual" dskA until we call the Inst constructor but then we won't have the
    result available in the other branches of the conjunction conclusion *)
    forwards [ty [dsub' [SS' [EMB WF__sub']]]]:
      H dskA (subst_skvar_Sch (T_ExVar exA) dskA (open_Sch_wrt_Ty sch0 (T_SkVar_f dskA))) (env ::a [exA]) (dsub ++ [(exA, DTy1)]).
      fsetdec. reflexivity. subdist.
      rewrite subst_exvar_Sch_subst_skvar_Sch. 2:{ rewrite free_exvars_Sch_open_Sch_wrt_Ty_upper. rewr. fsetdec. }
      rewrite subst_skvar_Sch_open_Sch_wrt_Ty. 2:eauto.
      rewrite subst_dskvar_DSch_open_DSch_wrt_DTy. 2:eauto. simpl. if_taut.
      rewrite DSub_app_open_comm. 2:eauto. 2:eauto.
      rewrite embed_Sch_open_comm. rewr.
      rewrite DSub_app_susbst_skvar_Sch. 2:fsetdec.
      rewr. rewrite EMB0. rewrite embed_Sch_subst_dskvar_DSch. reflexivity.
      apply DSub_wf_snoc. eassumption. fsetdec. eassumption.
    exists ty (dsub' ++ [(exA, DTy1)]). splits.
    + rewr. applys InstPoly (free_skvars_Sch sch0). simpl. fsetdec. intros dskB NIL''. rewr.
      (** repeat the trick of getting rid of the dskvar (dskB here) to apply the forwards IH*)
      rewrite subst_skvar_Sch_open_Sch_wrt_Ty in *. 2,3:eauto. simpl. simpl in SS'. if_taut.
      rewrite subst_skvar_Sch_not_in_Sch_idempotent in *. 2,3:fsetdec. eassumption.
    + rewr. rewrite DSub_app_t_app_distr in *. rewrite DSub_app_t_app_symm in EMB. eassumption.
      eauto.
    + eapply DSub_wf_rewr. eassumption. crush. rewr_dsrel. fsetdec'.
Qed.

(*** Trash to be moved *)


(*** Acutal theorem *)

Theorem Inf_Gen_complete : Inf_complete__def /\ Gen_complete__def.
Proof.
  forwards: (Mon_DGen_mut Inf_complete__prop Gen_complete__prop)
  ; unfold Inf_complete__prop in *; unfold Gen_complete__prop in *
  .
  7:{ jauto. }

  (*var*)
  - introv IN SS [dsub INST] SUB__denv WF SOO NN. rename env__in into env.
    (**)
    forwards IN': DEnvComplRel_lookup. eassumption. eassumption. destruct IN' as [dsch' [IN' SS']].
    (**)
    assert (DEnv5 [<=]de denv__obj). eauto. rewrite H in SS. clear H.
    (**)
    forwards SS'': (SubSump_transitive denv__obj). apply SS'. eassumption.
    (**)
    assert (exists sch, SchPSI.In (x, sch) (Env_bindings env) /\ DSub_app sch dsub = emb_Sch dsch').
      EInst_props__base. eassumption.
      forwards [sch [EMB IN'']]: IN__dsch.
      eassumption. exists sch. rewr in IN''. rewr in EMB.
      eauto.
    destr.
    (**)
    inv_EInst.
    forwards WF__sub: EInst_props__wf. apply INST0. auto. auto. crush. rewr in WF__sub.
    (**)
    (** Strengthening embedding of sch *)
    assert (EMB__sch: DSub_app sch DSub1 = emb_Sch dsch').
    { forwards: EInst_WfTy_impl_emb. apply INST0. apply in_wf_env_impls_wf. eauto. auto.
      destr. subdist in H0. rewrite H1 in H0. rewr in H0. apply emb_Sch_inj in H0. crush.
    }
    clear H0.
    (**)
    (** helper here*)
    (* forwards [a [ty [dsub' [Inst [EMB__ty WF__dsub]]]]]: complete_var__helper'. *)
    forwards [ty [dsub' [Inst [EMB__ty WF__dsub]]]]: complete_var__helper.
    apply SS''. eassumption. eauto.
    (**)
    (** Now there is a split depending on if dsub' is empty or not*)
    destruct (list_rev_destr dsub'); destr.
    + exists. splits.
      * econstructor. eassumption. eassumption.
      * forwards: AInst_NN_create. apply NN. destr.
        exists. constructor. econstructor. econstructor. eassumption. simpl. auto. auto. rewr. rewr in EMB__ty. crush.
        rewr. eassumption.
      * simpl. reflexivity.
    + destruct x0 as [exA dty]. rename xs' into dsub'. exists. splits.
      * econstructor. eassumption. eassumption.
      * forwards: AInst_trivial. destr.
        exists. constructor. econstructor. econstructor. eassumption.
        rewr. instantiate (1 := dsub' ++ [(exA, dty)]). instantiate (1 := DA5).
        applys_eq AInst_merge. instantiate (2 := []). reflexivity.
        simpl. rewr. applys_eq AInstCons. instnil. crush. rewr. apply WF__dsub. rewr_dsrel. fsetdec.
        auto. apply AInst_DSub_wf. eauto. auto. rewr. crush. eassumption.
      * crush.

  (*unit*)
  - introv _ [dsub INST] _ _ _ _. rename env__in into env.
    inv_EInst'. rewr in INSTA.
    (**)
    exists. splits. auto. exists. constructor. econstructor. constructor. eassumption. auto. auto. rewr. crush. rewr. eauto using AInst_init_DEnv_sub. crush.

  (*lam*)
  - introv WFDTY DMON IH [dsub__in INST__in] SUB__denv WF__in SOO NN.
    (**)
    forwards [exA NI__exA]: atom_fresh (L \u Env_Obj_exvars env__in \u DSub_dom dsub__in).
    forwards [x NI__x]: atom_fresh (L \u free_xs_e e5 \u Env_boundvars (env__in ::a [exA])).
    assert (WF__in': wf((env__in ::a [exA]) ::x x :- S_Mono (T_ExVar exA))).
      constructor. constructor. assumption. constructor. auto. rewr. fsetdec. constructor. rewr. fsetdec.
    inv_EInst'.
    forwards IH1: IH x (DEnv_5 :::a DA5 :::x x :- DS_Mono DTy1) (env__in ::a [exA] ::x x :- S_Mono (T_ExVar exA)) a__in. fsetdec.
      forwards: AInst_trivial a__in. destr.
      exists. applys_eq EInstA. instnil. reflexivity. constructor. constructor. eassumption.
      applys_eq AInstCons. instnil. rewr. reflexivity. rewr. eapply WfDTy_DEnv_sub. eassumption. eauto.
      auto. rewr. subdist. rewrite DSub_app_t_exA_notinsub. rewr. reflexivity. rewr in NI__exA. fsetdec. eassumption.
      rewr. apply DEnvComplRel__consvar. eassumption. auto.
      assumption.  SOO_auto. assumption.
    clear IH. destruct IH1 as [env__out [a [ty [denv__obj' [da' [MON [[dsub__out INST__out] EQ]]]]]]].
    (**)
    forwards WF__out: Inf_Wf. eassumption. assumption. clear WF__in WF__in'.
    (**)
    destruct da'. 2:inverts EQ. simpl in *. subst. forwards: Inf_SameShape. eassumption. inv_SS.
    (**)
    inv_EInst'. clear H. rewr*.
    destruct DA0. 2:inverts H5. simpl in H5. inverts H5.
    destruct DA2. 2:inverts H0. simpl in H0. inverts H0.
    emb_auto''.
    (**)
    exists. splits.
    + applys InfAbs empty exA. fsetdec. intros y NI__y.
      rewr. forwards: Inf_rename_binding' y. apply MON. rewr. fsetdec.
      rewrite subst_tm_e_open_e_wrt_e in H. simpl in H. if_taut.
      assert (subst_tm_e (e_Var_f y) x e5 = e5). crush. rewrite H0 in H. eassumption. auto.
    + forwards: AInst_trivial a__in. destr.
      exists. constructor. econstructor. econstructor. eassumption. rewr. apply AInst_merge. eassumption.
      rewr. eapply AInst_init_DEnv_sub. eassumption. rewr_derel. fsetdec. auto.
      rewr. subdist. subdist in EMB. subdist in EMB1. rewrite EMB. rewrite EMB1. crush.
      rewr. eassumption.
    + rewr. reflexivity.

  (*app*)
  - introv MON__e1 IH__e1 MON__e2 IH__e2 INST SUB__denv WF__in SOO NN.
    (**)
    forwards IH1: IH__e1; eauto. clear INST. clear IH__e1.
    destruct IH1 as [env1 [a1 [ty [denv__obj' [da' [INF__e1 [[dsub INST1] EQ]]]]]]]. subst.
    inv_EInst'. clear H. emb_auto''.
    forwards: DSODO_cons_DA' H4. 1,2:SOO_auto. clear H4. destr. inverts H.
    rewr in EMB0. rewr in INSTA. rename DSub2 into dsub__ain.
    rename DEnv_5 into denv. rename DSub0 into dsub__e1.
    rewr in INSTA1. rename DA1 into da1. rename DSub3 into dsub__a1.
    (**)
    forwards WF1: Inf_Wf; eauto. clear WF__in.
    (**)
    forwards IH2: IH__e2 (denv :::o ⟦⟨da1⟩ DS_Mono (DT_Fun DTy1 DTy2)⟧d :::a (da' ++ da1)) (env1 ::o ⟦⟨a1⟩ S_Mono ty⟧) (a__in ++ a1).
      exists. econstructor. econstructor. eassumption. rewr. eassumption. crush.
      rewr. eapply AInst_merge; eapply AInst_init_DEnv_sub. eassumption. crush. apply INSTA. rewr_derel. reflexivity.
      norm in SUB__denv.
      forwards: DEnvComplRel__apphelper denv (oneDA (da' ++ da1)) DEnv5. norm. eassumption.
      norm. norm in H. eassumption.
      eauto. SOO_auto. destruct (a__in ++ a1 == []). destruct a__in. contradiction. inverts e. auto.
    clear IH__e2 INSTA INST. destruct IH2 as [env2' [a2 [ty1 [denv__obj [da [INF__e2 [[dsub INST2] EQ]]]]]]]. subst.
    (**)
    forwards: Inf_SameShape. eassumption. inv_SS. clear H2. rename a3 into a1'. rename ty2 into ty'.
    forwards WF2: Inf_Wf. eassumption. eauto. clear WF1.
    eapply DSODO_cons_DA in EQ. 2:SOO_auto. destr. rename H into EQ.
    (**)
    inv_EInst'. rewr*. emb_auto''. clear H.
    apply DSODO_cons_DA' in H4. 2,3:SOO_auto. destr. inverts H.
    apply DSODO_cons_DA' in H1. 2,3:SOO_auto. destr. inverts H.
    rename da2 into da__in. rename dsub0 into dsub__in.
    rename da1' into da2. rename DSub3 into dsub__a2.
    rename da1 into da1'. rename DSub'0 into dsub__a1'.
    rename dsub__a1 into dsub__a1old. rename da0 into da1. rename dsub into dsub__a1.
    (**)
    forwards [exB NI__exB]: atom_fresh (Env_Obj_exvars (env2 ::a (a2 ++ a1')) \u DSub_dom (dsub__a1' ++ dsub__a2 ++ DSub0)).
    assert (UNI: DSub_unique ([(exB, DTy1)] ++ dsub__a1' ++ dsub__a2 ++ DSub0)).
      simpl. apply DSub_unique_cons. 2:fsetdec.
      forwards WF__dsub: EInst_props__wf. apply EInstA. apply EInstA. apply INST0. rewr. eassumption.
      eapply AInst_init_DEnv_sub'. apply INSTA2. rewr_derel. fsetdec.
      inv_Wf. constructor. constructor. eauto. eauto. eauto. apply FrA_Obj in FR. assumption. auto. crush.
      eapply DSub_unique_rewr. apply WF__dsub. rewr_dsrel. fsetdec'.
    assert (EMB__ty': DSub_app_t ty'           ([(exB, DTy2)] ++ dsub__a1' ++ dsub__a2 ++ DSub0) = emb_Ty (DT_Fun DTy1 DTy2)).
      rewrite DSub_app_t_app_distr. rewrite app_assoc. rewrite DSub_app_t_app_distr. rewrite DSub_app_t_app_symm.
      subdist. subdist in EMB2. rewrite EMB2. rewr. reflexivity. eauto.
    assert (EMB__ty1: DSub_app_t ty1           ([(exB, DTy2)] ++ dsub__a1' ++ dsub__a2 ++ DSub0) = emb_Ty         DTy1      ).
      subdist. subdist in EMB1. rewrite EMB1. rewr. reflexivity.
    assert (EMB__exB: DSub_app_t (T_ExVar exB) ([(exB, DTy2)] ++ dsub__a1' ++ dsub__a2 ++ DSub0) = emb_Ty              DTy2 ).
      rewrite DSub_app_t_app_distr. rewrite DSub_app_t_exA_notinsub. simpl. rewr. reflexivity. fsetdec.
    (**)
    assert (WFDTY__dty2:  denv :::a da1' |=dty DS_Mono DTy2).
      EInst_props__base. apply EInstA. apply INST0. rewr. eassumption. rewr in SUB__wfdty.
      inv_Wf.
      assert (denv :::a da1' |=dty DS_Mono (DT_Fun DTy1 DTy2)). eapply embed_Ty_WfDTy. eassumption. eassumption.
      rewrite <- SUB__sk. apply WfTy_props in WFTY0. jauto. eauto.
      apply WfDTy_props. apply WfDTy_props in H. destr. split. rewrite <- H. rewr. fsetdec.
      inv_LC. eauto.
    (**)
    forwards U__out: make_unification ((env2 ::a ((exB :: a2) ++ a1')) ::o ⟦⟨[]⟩ S_Mono (T_ExVar exB)⟧).
      (*sub*)
      applys DSub_app_t_Sub_app_t
              ([(exB, DTy2)] ++ dsub__a1' ++ dsub__a2 ++ DSub0)
              ty'
              (T_Fun ty1 (T_ExVar exB)).
        rewr. rewrite EMB__ty'. rewrite EMB__ty1. rewrite EMB__exB. reflexivity.
      (*inst*)
      forwards AINST__triv: AInst_trivial' a2. destruct AINST__triv as [dsub__triv [? AINST__triv]]. subst a2.
      exists. instantiate (2 := denv :::a da1' :::o ⟦⟨[]⟩ DS_Mono DTy2⟧d).
      econstructor. econstructor. eassumption. rewr. applys_eq AInst_merge.
      3:apply INSTA3. norm. rewrite app_assoc. reflexivity. instnil. reflexivity.
      applys_eq AInst_merge. 2:eassumption. rewr. reflexivity. applys_eq AInstCons.
      instnil. rewr. reflexivity. rewr. eapply WfDTy_DEnv_sub. eassumption. rewr_derel. reflexivity.
      auto. auto. rewr.
      rewrite DSub_app_t_app_distr. rewrite DSub_app_t_exA_notinsub. simpl. rewr. reflexivity.
      rewr in NI__exB. rewr. fsetdec.
    destruct U__out as [env__out [U__out [dsub__out INST__out]]].
    (**)
    forwards: U_SameShape. eassumption. inv_SS. rename env4 into env__out. rename a3 into a__out. rename ty2 into ty__out.
    (**)
    exists. splits.
    + applys InfApp exB. 2,3,4:rewr; eassumption. fsetdec.
    + forwards: AInst_NN_create a__in. assumption. destr.
      exists. constructor. eassumption. eassumption.
    + rewrite <- DEnv_cons_da_app_split. norm.
      reflexivity.

  (*let*)
  - introv POL IH__pol MON IH__mon INST__in SUB__denv WF__in SOO__in NN.
    (**)
    forwards IH1: IH__pol. eassumption. eassumption. eassumption. eassumption. eassumption.
      clear IH__pol. destruct IH1 as [env [sch [dsch' [denv__obj' [da' [GEN [INST [SS EQ]]]]]]]]. subst.
    (**)
    forwards WF: Gen_Wf. eassumption. eassumption. clear WF__in.
    (**)
    forwards [x NI__x]: atom_fresh (L \u free_xs_e e2 \u Env_boundvars env).
    forwards IH2: IH__mon x (denv__obj' :::x x :- dsch' :::a da') (env ::x x :- sch) a__in.
      fsetdec.
      destruct INST. inv_EInst'. forwards: DSODO_cons_DA'. apply H5. 1,2:SOO_auto. destr. clear H5. inverts H0.
      rewr*. exists. constructor. constructor. eassumption. rewr. rewr in EMB. eassumption. rewr.
      eapply AInst_init_DEnv_sub. eassumption. crush.
      eauto using DEnvComplRel__lethelper. inv_Wf. eauto. unfold Sch_or_Obj. SOO_auto. eassumption.
    clear IH__mon.
    destruct IH2 as [env__out' [a [ty [denv__obj'' [da'' [INF [[dsub__out INST__out] EQ]]]]]]].
    forwards: Inf_SameShape. eassumption. inv_SS. clear H4.
    (**)
    inv_EInst'. clear H.
    forwards: DSODO_cons_DA'. apply H4. 1,2:SOO_auto. destr. inverts H.
    clear H4.
    rewrite <- DEnv_cons_da_app_split in EQ.
    forwards: DSODO_cons_DA'. apply EQ. 1,2:SOO_auto. destr. inverts H.
    rewr*. emb_auto''.
    (**)
    exists. splits.
    + applys InfLet empty. eassumption. intros y NI__y.
      forwards: Inf_rename_binding' y. eassumption. fsetdec.
      rewrite subst_tm_e_open_e_wrt_e in H. simpl in H. if_taut.
      assert (subst_tm_e (e_Var_f y) x e2 = e2). crush. rewrite H0 in H. eassumption. eauto.
    + forwards: AInst_NN_create a__in. eassumption. destr.
      exists. constructor. econstructor. econstructor. eassumption. rewr.
      eapply AInst_init_DEnv_sub. eassumption. rewr_derel. fsetdec. auto. rewr. crush.
      instantiate (2 := da''). eassumption.
    + norm. reflexivity.

  (* Gen *)
  - introv DFR MON IH__e DGEN SUB__denv [dsub INST] WF__in SOO__in NN. rename DA5 into da__gen. rename DTy5 into dty.
    eapply DFra_DEnv_sup_rem in DFR. 2:eassumption. forwards> [DFR__disj DFR__nodup]: DFrA_props. eassumption.
    (**)
    inv_EInst.
    rename DEnv_5 into denv__obj. rename DA5 into da__in. rewr in INSTA.
    (**)
    forwards IH: IH__e (denv__obj :::a (da__gen ++ da__in)) env__in a__in.
      exists. constructor. eassumption. rewr. apply AInst_NN_extend'. eassumption. assumption.
      rewrite DEnv_cons_da_app_split. eapply DEnvComplRel__genhelper. eassumption.
      assumption. eassumption. eassumption.
    destruct IH as [env__out [a [ty [denv__obj'' [da__in' [INF [[dsub INST] EQ]]]]]]].
    (**)
    forwards WF__out: Inf_Wf. eassumption. auto. clear WF__in.
    (**)
    forwards SOO__out: SOO_Inf. eassumption. assumption. clear SOO__in.
    inv_EInst'. rewr*. clear H. emb_auto''.
    forwards: DSODO_cons_DA' H4. 1,2:SOO_auto. clear H4. destr. inverts H.
    rename DEnv_5 into denv__obj'. rename DSub4 into dsub__obj'.
    rename DA1 into da. rename DSub5 into dsub__a.
    rename DSub3 into dsub__in'.
    (**)
    forwards: SOO_cons_DA. apply INST1. eassumption. symmetry in EQ. rewrite <- DEnv_cons_da_app_split in EQ. apply EQ.
      destruct H as [da' [EQ__das ?]]. symmetry in EQ__das. subst. rewr in EQ__das.
    (**)
    assert (PROPS: DSub_WfDTy (denv__obj' :::a da) (dsub__a ++ dsub__obj') /\ Env_skvars (env__out ::a a) [<=] DEnv_dskvars (denv__obj' :::a da)).
      EInst_props__base. apply EInstA. apply INST1. rewr. eassumption. rewr in SUB__wfdty. jauto.
      destruct PROPS as [SUB__wfdty EQ__ex].
    forwards WFDTY: embed_Ty_WfDTy. apply SUB__wfdty. eassumption. rewrite <- EQ__ex.
      inv_Wf. apply WfTy_props in WFTY. destr. simpl in H. rewr in H. rewrite H. rewr_erel. fsetdec. inv_Wf. eauto.
    (**)
    assert (EMB__gen: exists dsch, DSub_app (generalize_Sch (S_Mono ty) a empty) dsub__obj' = emb_Sch dsch).
    { forwards: AInst_props__base. apply INSTA2. destr. apply DSub_fullb_emb.
      unfold DSub_full. forwards<: DSub_full_t_emb. exists. eassumption. unfold DSub_full_t in H1.
      rewrite free_exvars_Sch_generalize_Sch. rewrite H1. rewr_dsrel. fsetdec.
    } destr.
    assert (SubSump ((denv__obj' :::a da') :::a da__in) dsch (generalize_DSch (DS_Mono dty) da__gen)).
    { forwards: AInst_props__base. apply INSTA2. destr.
      forwards INST: EInstA. apply INST1. rewr. eassumption.
      forwards WF__sub: EInst_props__base3. apply INST. rewr in WF__sub.
      assert (exists da__useless da__gen', da__gen = da__useless ++ da__gen'
                                /\ DSub_WfDTy (((denv__obj' :::a da') :::a da__in) :::a da__gen') (dsub__a ++ dsub__obj')
                                /\ varl da__gen' [><] DSub_codom_dskvars dsub__obj'
                                /\ varl da__gen' [><] free_skvars_Ty ty
                                /\ varl da__useless [><] free_dskvars_DTy dty).
      { assert (SPLIT: (exists da__inrest, da__in' = da__gen ++ da__inrest) \/ (exists da__gen1 da__gen2, da__gen = da__gen1 ++ da__gen2 /\ da__in' = da__gen1)).
        { forwards: list_app_eq_share_head. apply EQ__das. destr. right. exists. crush. left. exists. crush. }
        destr.
        - rewr in EQ__das. apply app_inv_head in EQ__das. exists da__gen ([]:DA). rewr. splits.
          + auto.
          + simpl. rewrite <- DEnv_cons_da_app_split. rewrite EQ__das. eauto.
          + crush.
          + crush.
          + assert (DISJ: (varl da__gen [><] DEnv_dskvars (denv__obj' :::a da' :::a da__in))).
              rewr. rewr in DFR__disj. eassumption.
            apply WfDTy_props in WFDTY. destr.
            simpl in H1. rewrite H1. eapply disj_subset_proper. 3:apply DISJ. crush.
            rewrite <- DEnv_cons_da_app_split. rewrite EQ__das. rewr.
            rewrite (fold_right_varl (da__inrest ++ da)). rewr. fsetdec.
        - rewr in EQ__das. apply app_inv_head in EQ__das. subst.
          assert (DISJ: varl da__gen2 [><] DEnv_dskvars denv__obj').
            eapply disj_subset_proper. 3:eassumption.
            rewr. fsetdec. rewr. fsetdec.
          exists. splits.
          + reflexivity.
          + norm. norm in WF__sub. eauto.
          + rewrite (DSub_WfDTy_codom_in_DEnv denv__obj'). 2:{ forwards WF__sub': EInst_props__base3. apply INST1. rewr in WF__sub'. assumption. }
            assumption.
          + inv_Wf. apply WfTy_props in WFTY. destr. rewr in H1. rewrite H1.
            forwards: EInst_props__base2. apply INST1. rewrite H4. assumption.
          + apply WfDTy_props in WFDTY. destr. simpl in H1. rewrite H1.
            apply DFrA_app_shift in DFR. apply DFrA_props in DFR. destr.
            eapply disj_subset_proper. 3:apply H3. rewr. fsetdec. rewr.
            rewrite <- (fold_right_varl da__gen2).
            rewrite <- (fold_right_varl da__in).
            rewrite <- (fold_right_varl da'). fsetdec.
      }
      (**)
      destr. rewrite generalize_DSch_app. eapply DGen_complete'; try eassumption.
      - forwards: EInst_props__base3. apply INST1. rewr in H1. norm. eauto.
      - forwards: EInst_props__base3. apply INST. rewr in H1. eauto.
      - forwards: EInst_props__wf. apply INST. inv_Wf. constructor; eauto. auto. crush. rewr in H1. eauto.
      - eauto.
    }
    exists. splits.
    + econstructor. eassumption. reflexivity.
    + instantiate (3 := denv__obj').
      forwards: AInst_NN_create a__in. assumption. destr.
      exists. constructor. econstructor. eassumption. auto. rewr. eassumption.
      instantiate (2 := (da__in ++ da')). eassumption.
    + eassumption.
    + norm. reflexivity.
Qed.

Theorem Completeness__mono : forall (e : e) (dty : DTy),
    ▪ |=m e ▸ dty
  -> exists a ty,
      • |= e ▸ ⟨a⟩ ty =| •
    /\ FullEInst (<a>a ::o ⟦S_Mono ty⟧) <⟦DS_Mono dty⟧d>do.
Proof.
  introv MON. forwards [exA NI__exA]: atom_fresh empty.
  forwards: proj1 Inf_Gen_complete. unfold Inf_complete__def in H.
  forwards IH: H ▪ ▪ • ([exA]). apply MON.
  - exists. applys_eq EInstA. 2:auto. instnil. reflexivity.
    applys_eq AInstCons. instnil. rewr. reflexivity. auto. auto.
  - unfold DEnvComplRel. split; crush.
  - auto.
  - SOO_auto.
  - unfold NonNil. destruct ([exA] == []). inverts e0. assumption.
  - destruct IH as [env [a [ty [denv__obj [da [INF [[dsub INST] EQ]]]]]]].
    exists a ty.
    forwards: Inf_SameShape. eassumption. inverts H0. split.
    + eassumption.
    + inv_EInst'. destruct da. 2:inverts EQ. simpl in EQ. subst.
      simpl in H5. destruct DA5. 2:inverts H5. simpl in H5. inverts H5.
      destruct DA1. 2:inverts H2. simpl in H2. subst.
      exists. econstructor. applys_eq EInstA. 3:eassumption. reflexivity. auto. auto.
      rewr. rewr in EMB. eassumption.
Qed.

Theorem Completeness__poly : forall (e : e) (dsch : DSch),
    ▪ |=p e ▸ dsch
  -> exists sch dsch',
      • |= e ▸ sch =| •
    /\ FullEInst (<⟦sch⟧>o) <⟦dsch'⟧d>do
    /\ SubSump ▪ dsch' dsch.
Proof.
  introv DGEN. forwards [exA NI__exA]: atom_fresh empty.
  forwards: proj2 Inf_Gen_complete. unfold Gen_complete__def in H.
  forwards IH: H ▪ ▪ • ([exA]). apply DGEN.
  - unfold DEnvComplRel. split; crush.
  - exists. applys_eq EInstA. 2:auto. instnil. reflexivity.
    applys_eq AInstCons. instnil. rewr. reflexivity. auto. auto.
  - auto.
  - SOO_auto.
  - unfold NonNil. destruct ([exA] == []). inverts e0. assumption.
  - destruct IH as [env [sch [dsch' [denv__obj [da [GEN [[dsub INST] [SS EQ]]]]]]]].
    exists sch dsch'. forwards: Gen_SameShape. eassumption. inverts H0.
    splits. 1,3:assumption.
    inv_EInst'. exists. econstructor. auto. auto. rewr.
    destruct da. 2:inverts EQ. simpl in EQ. subst.
    simpl in H5. destruct DA5. 2:inverts H5. simpl in H5. inverts H5. inverts INST.
    rewr in EMB. assumption.
Qed.
