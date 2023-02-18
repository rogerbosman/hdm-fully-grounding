(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.
Require Import Defs.Defs.

Require Import Wf.Wf.

(*** Umi_split *)
Lemma umi_split_head_helper : forall (denv__in : DEnv) (dsub__in dsub : DSub) (exA exA1 exA2 : exvar) (a1 : A) (da : DA),
    {denv__in, dsub__in}a |= exA2 :: exA1 :: a1 ~> {da, dsub}
  -> exists dt1 dt2 dsub',
      dsub = (exA2, dt2) :: (exA1, dt1) :: dsub'
    /\ {denv__in, dsub__in}a |= exA :: a1 ~> {da, (exA, DT_Fun dt1 dt2) :: dsub'}.
Proof.
  introv INST. inv_AInst. do 3 eexists. split. auto.
  rep_app_assoc. constructor; try assumption.
  constructor; rewr; eauto.
Qed.

Lemma umi_split_head: forall (exA exA1 exA2 : exvar) (env1 : Env) (a1 a2 : A) (denv : DEnv) (dsub : DSub),
    {▪, []}|= env1 ::a (a2 ++ exA2 :: exA1 :: a1) ~> {denv, dsub}
  -> exists (dt1 dt2 : DTy) (dsub1 dsub2 : DSub),
      dsub = dsub2 ++ (exA2, dt2) :: (exA1, dt1) :: dsub1
    /\ Env_exvars (env1 ::a a1) [=] DSub_dom dsub1
    /\ {▪, []}|= env1 ::a (a2 ++ exA :: a1) ~> {denv, dsub2 ++ (exA, DT_Fun dt1 dt2) :: dsub1}.
  Proof.
    introv INST. inverts INST.
    AInst_split_destr. eassumption.
    forwards [dt1 [dt2 [dsub' [?EQ__dsub INSTA']]]]: umi_split_head_helper exA. eassumption.
    rewr*.
    forwards INST'': EInstA. eassumption. apply AInst_merge. rewr. apply INSTA'. eapply AInst_swap_subinit. rewr. eassumption.
    inverts INSTA'.
    forwards: EInst_props__base1 (env1 ::a a1). econstructor. eassumption. rewr. eassumption.
    subst. rewr*.
    do 4 eexists. splits. 3:{ apply INST''. } reflexivity. auto. rewr. fsetdec.
Qed.

Lemma umi_split_tail : forall (dsub__mid dsub__mid' : DSub) (denv__init : DEnv) (env : Env) (denv : DEnv) (dsub1 dsub2 dsub3 : DSub) (ty : Ty) (exA : exvar),
    {denv__init, dsub2 ++ dsub__mid ++ dsub1}|= subst_exvar_Env ty exA env ~> {denv, dsub3}
  -> (forall sch, SchSI.In sch (Env_Obj_Schs env)
            -> DSub_app (subst_exvar_Sch ty exA sch) (dsub__mid  ++ dsub1)
            = DSub_app sch (dsub__mid' ++ dsub1))
  -> {denv__init, dsub2 ++ dsub__mid' ++ dsub1}|= env ~> {denv, dsub3}.
Proof.
  introv INST EQ__sub. gen denv dsub3. dependent induction env; intros.
  - inverts INST. auto.
  - inverts INST.
  - inverts INST. econstructor; rewr; eauto using AInst_swap_subinit. eapply IHenv.
    intros. apply EQ__sub. rewr. assumption. assumption.
  - inverts INST. econstructor.
    eapply IHenv. intros. eapply EQ__sub. rewr. fsetdec'. assumption.
    forwards: EQ__sub Sch5. rewr. fsetdec.
    subdist*. crush.
  - inverts INST. destruct Obj5. simpl in H3. inverts H3.
    econstructor.
    eapply IHenv. intros. eapply EQ__sub. rewr. fsetdec'. eauto. eauto using AInst_swap_subinit.
    forwards: EQ__sub Sch0. rewr. fsetdec.
    subdist*. crush.
Qed.

Lemma umi_split_substr : forall (exA exA1 exA2 : exvar) (dsub : DSub) (dt1 dt2 : DTy) (sch : Sch),
    exA1 \notin free_exvars_Sch sch
  -> exA2 \notin free_exvars_Sch sch
  -> exA1 <> exA2
  -> exA \notin DSub_dom dsub
  -> exA1 \notin DSub_dom dsub
  -> exA2 \notin DSub_dom dsub
  -> DSub_app (subst_exvar_Sch (T_Fun (T_ExVar exA1) (T_ExVar exA2)) exA sch) (([(exA2, dt2)] ++ [(exA1, dt1)]) ++ dsub)
  = DSub_app sch ([(exA, DT_Fun dt1 dt2)] ++ dsub).
  Proof.
    intros.
    subdist. Sch_Ty_ind sch; rewr; auto.
    - simpl. DSub_exA_decide.
      + ifdec.
        * rewr.
          do_DSub_exA_decide dsub exA1. 2:{ assert (exA1 \in DSub_dom dsub). eauto. fsetdec. }
          do_DSub_exA_decide dsub exA2. 2:{ assert (exA2 \in DSub_dom dsub). eauto. fsetdec. }
          crush. ifdec; crush. if_taut.
        * rewrite INV. simpl.
          destruct (exA0 == exA). crush.
          destruct (exA0 == exA1). crush. simpl.
          destruct (exA0 == exA2). crush. reflexivity.
      + ifdec. subst.
        assert (exA \in DSub_dom dsub). eauto. fsetdec. crush.
    - crush.
    - crush.
Qed.

(** split main *)
Theorem umi_split : forall (denv : DEnv) (exA exA1 exA2 : exvar) (env1 : Env) (a1 a2 : A) (env2 : Env),
    FullEInst (subst_exvar_Env (T_Fun (T_ExVar exA1) (T_ExVar exA2)) exA (env1 ::a (a2 ++ (exA2 :: exA1 :: a1)) +++ env2)) denv
  -> wf(subst_exvar_Env (T_Fun (T_ExVar exA1) (T_ExVar exA2)) exA (env1 ::a (a2 ++ (exA2 :: exA1 :: a1)) +++ env2))
  -> wf(env1 ::a (a2 ++ [exA] ++ a1) +++ env2)
  -> FrA [exA2; exA1] (env1 ::a (a2 ++ [exA] ++ a1) +++ env2)
  -> FullEInst (                                                           env1 ::a (a2 ++ (exA  ::        a1)) +++ env2 ) denv.
Proof.
  introv INST WF1 WF2 FR. destr. rewr*.
  assert (exA `notin` Env_Obj_exvars env1).
  { forwards DISJ: wf_Env_exvar_disj env1. norm in WF2. rep_Env_app_assoc in WF2. apply WF2.
    eapply in_disjoint_impl_notin1. eassumption. rewr. fsetdec. }
  rewrite subst_exvar_Env_notin_Env_idempotent in *. 2,3,4,5: eauto.
  (**)
  EInst_split_destr. eassumption.
  (**)
  forwards [dt1 [dt2 [dsub1' [dsub2 [? [DOMSUB ?INST]]]]]]: umi_split_head. eassumption.
  (**)
  subst. rewr*. exists. apply EInst_merge. eassumption.
  applys_eq (umi_split_tail ([(exA2, dt2)] ++ [(exA1, dt1)]) ([(exA, DT_Fun dt1 dt2)])).
  2:{ rewr. norm in INST1. eassumption. } rewr. reflexivity.
  (**)
  intros sch IN.
  forwards SUB: fv_sch_in_wfenv_subset sch (env1 ::a (a2 ++ [exA] ++ a1) +++ env2). rewr. fsetdec'. auto.
  inv_AInst.
  (* forwards DOMSUB: EInst_props1. apply EInstA. apply INST1. rewr. eassumption. *)
  apply umi_split_substr.
  - unfold not. rewrite SUB. intros.
    assert (FR': FrA [exA1] (env1 +++ <a2 ++ [exA] ++ a1>a +++ env2)). simpl in FR. eauto.
    inverts FR'. crush.
  - unfold not. rewrite SUB. intros.
    inverts FR. crush.
  - assert (UNI: NoDup' [exA2; exA1]). apply FrA_props in FR. jauto.
    destruct (exA1 == exA2). subst. inverts UNI. crush. assumption.
  - unfold not. rewrite <- DOMSUB. intro IN'.
    assert (NI: exA \notin Env_Obj_exvars (env1 ::a a1)). eauto.
    apply NI. rewr. indestr in IN'. destr. fsetdec. auto.
  - unfold not. rewrite <- DOMSUB. intro IN'.
    assert (wf(env1 ::a (exA1 :: a1))). eauto.
    assert (FR': FrA (exA1 :: a1) env1). eauto.
    inverts FR'. apply FR0. indestr in IN'. destr; rewr; eauto.
  - unfold not. rewrite <- DOMSUB. intro IN'.
    inverts FR. apply FR0. indestr in IN'. destr; rewr. eauto. fsetdec.
Qed.

(** split drop *)
Theorem umi_split__drop: forall (n : nat) (denv : DEnv) (exA exA1 exA2 : exvar) (env1 : Env) (a1 a2 : A) (env2 : Env),
    FullEInst (Env_drop n (subst_exvar_Env (T_Fun (T_ExVar exA1) (T_ExVar exA2)) exA (env1 ::a (a2 ++ (exA2 :: exA1 :: a1)) +++ env2))) denv
  -> wf(Env_drop n (subst_exvar_Env (T_Fun (T_ExVar exA1) (T_ExVar exA2)) exA (env1 ::a (a2 ++ (exA2 :: exA1 :: a1)) +++ env2)))
  -> wf(env1 ::a (a2 ++ [exA] ++ a1) +++ env2)
  -> FrA [exA2; exA1] (env1 ::a (a2 ++ [exA] ++ a1) +++ env2)
  -> FullEInst (Env_drop n (                                                           env1 ::a (a2 ++ (exA  ::        a1)) +++ env2 )) denv.
Proof.
  introv [dsub INST] WF1 WF2 WFTY. rewrite Env_drop_subst_exvar_Env_comm in *.
  dropdistr*. destruct (le_lt_dec n (Env_length env2)).
  - forwards NIL: nat_minus_greater. eassumption. rewrite NIL in *. rewr*.
    eapply umi_split. rewr. eauto. rewr. eassumption.
    rewrite Env_drop_distr'. eauto using wf_Env_drop.
    rewrite Env_drop_distr'. eauto using FrA_drop.
  - rewrite (Env_drop_greater n) in *. 2,3,4: crush.
    rewr*.
    assert (exA `notin` Env_Obj_exvars env1).
    { forwards DISJ: wf_Env_exvar_disj env1. norm in WF2. rep_Env_app_assoc in WF2. apply WF2.
      eapply in_disjoint_impl_notin1. eassumption. rewr. fsetdec. }
    destruct (n - Env_length env2).
    + simpl in *.
      rewrite subst_exvar_Env_notin_Env_idempotent in INST. 3:{ eauto. } 2:assumption.
      forwards [dty [dsub1 [dsub2 [? [? [? ?]]]]]]: umi_split_head exA. eassumption.
      exists. eassumption.
    + simpl in *. exists.
      rewrite subst_exvar_Env_notin_Env_idempotent in INST. eassumption.
      rewrite Env_drop_Env_exvars_Obj. assumption.
      eauto using wf_Env_drop.
Qed.

(*** Umi_subst *)
Lemma umi_subst_head_helper : forall (exA : exvar) (dty : DTy) (a : A) (da : DA) (dsub : DSub) (denv__init : DEnv) (dsub__init : DSub),
    {denv__init, dsub__init}a|= a ~> {da, dsub}
  -> denv__init :::a da |=dty DS_Mono dty
  -> {denv__init, dsub__init}a|= exA :: a ~> {da, (exA, dty) :: dsub}.
Proof. introv INST WFDTY. rewrite <- (app_nil_l da). econstructor; crush. Qed.

Lemma umi_subst_head: forall (exA : exvar) (ty : Ty) (env1 : Env) (a1 a2 : A) (denv0 : DEnv) (dsub : DSub),
    {▪, []}|= env1 ::a (a2 ++ a1) ~> {denv0, dsub}
  -> (env1 ::a a1) |=ty S_Mono ty
  -> wf(env1 ::a (exA :: a1))
  -> exists (dty : DTy) (dsub1 dsub2 : DSub),
          dsub = dsub2 ++ dsub1
        /\ DSub_app_t ty dsub1 = emb_Ty dty
        /\ DSub_unique ((exA, dty) :: dsub1)
        /\ {▪, []}|= env1 ::a (a2 ++ exA :: a1) ~> {denv0, dsub2 ++ (exA, dty) :: dsub1}.
Proof.
  introv INST WFTY WF. inverts INST.
  (**)
  AInst_split_destr. eassumption.
  (**)
  forwards dsch EMB WFDTY: EInst_WfTy_impl_emb. 2:{ eassumption. } econstructor. eassumption. eassumption.
  emb_auto. rewr*.
  (**)
  forwards INSTA': umi_subst_head_helper exA a1. eassumption. eassumption. rewr in INSTA'.
  forwards INSTA'': EInstA. eassumption. eapply AInst_merge. rewr. apply INSTA'. eapply AInst_swap_subinit. rewr. eassumption.
  exists dty (dsub ++ DSub1) dsub0. splits.
  - reflexivity.
  - auto.
  - forwards WFSUB: EInst_props__wf (env1 ::a (exA :: a1)). econstructor. eassumption. rewr.
    econstructor. 2:eassumption. instantiate (2 := nil). rewr. eassumption. assumption.
    auto. crush. rewr in WFSUB. eauto.
  - rewr*. eassumption.
Qed.

Lemma umi_subst_sub : forall (exA : exvar) (ty : Ty) (dty : DTy) (dsub : DSub) (sch : Sch),
    DSub_unique ((exA, dty) :: dsub)
  -> DSub_app_t ty dsub = emb_Ty dty
  -> DSub_app (subst_exvar_Sch ty exA sch) dsub = subst_exvar_Sch (emb_Ty dty) exA (DSub_app sch dsub).
Proof.
  introv UNI EMB.
  subdist. Sch_Ty_ind sch. 1,2,4,6: crush. all:simpl.
  - ifdec'.
    + DSub_exA_decide; rewrite EMB. rewrite INV. simpl. if_taut.
      rewrite EMB0. rewrite subst_exvar_Ty_embed_idempotent.
      forwards: UNI dty dty0. rewr. fsetdec. rewr. fsetdec'. crush.
    + DSub_exA_decide. rewrite INV. simpl. if_taut.
      rewrite EMB0. rewrite subst_exvar_Ty_embed_idempotent. crush.
  - rewr. crush.
Qed.

Lemma umi_subst_tail : forall (dty : DTy) (exA : exvar) (ty : Ty) (dsub1 dsub2 : DSub) (env : Env) (denv : DEnv) (dsub : DSub) (denv__init : DEnv),
    {denv__init, dsub2 ++ dsub1}|= subst_exvar_Env ty exA env ~> {denv, dsub}
  -> DSub_app_t ty dsub1 = emb_Ty dty
  -> DSub_unique ((exA, dty) :: dsub1)
  -> {denv__init, dsub2 ++ (exA, dty) :: dsub1}|= env ~> {denv, dsub}.
Proof.
  introv INST EMB UNI.
  EInst_genind' INST env.
  - auto.
  - econstructor. eauto. eauto using AInst_swap_subinit.
  - econstructor. eauto. subdist*.
    erewrite <- umi_subst_sub; eassumption.
  - destruct Obj5; inverts H3.
    econstructor. eauto. eauto using AInst_swap_subinit. subdist*.
    erewrite <- umi_subst_sub; eassumption.
Qed.

(** subst main *)
Theorem umi_subst : forall (exA : exvar) (ty : Ty) (env1 env2 : Env) (a1 a2 : A) (denv : DEnv),
    FullEInst (subst_exvar_Env ty exA (env1 ::a (a2 ++ a1) +++ env2)) denv
  -> wf(env1 ::a (a2 ++ exA :: a1) +++ env2)
  -> env1 ::a a1 |=ty (S_Mono ty)
  -> FullEInst (env1 ::a (a2 ++ exA :: a1) +++ env2) denv.
Proof.
  introv INST WF2 WFTY. destr. rewr*.
  assert (exA `notin` Env_Obj_exvars env1).
  { forwards DISJ: wf_Env_exvar_disj env1. norm in WF2. rep_Env_app_assoc in WF2. apply WF2.
    eapply in_disjoint_impl_notin1. eassumption. rewr. fsetdec. }
  rewrite subst_exvar_Env_notin_Env_idempotent in *. 2,3: eauto.
  (**)
  EInst_split_destr. eassumption.
  (**)
  forwards [dty [dsub1' [dsub2 [? [? [? ?]]]]]]: umi_subst_head exA a1. eassumption. eassumption. constructor. eauto.
  constructor. eauto.
  assert (FrA (exA :: a1) env1). eauto. inv_FrA. eassumption.
  subst.
  (**)
  eexists. rewr*. apply EInst_merge.
  - eassumption.
  - rewr. eapply umi_subst_tail. eassumption. eassumption. eassumption.
Qed.

(** subst drop *)
Theorem umi_subst__drop : forall (n : nat) (exA : exvar) (ty : Ty) (env1 env2 : Env) (a1 a2 : A) (denv : DEnv),
    FullEInst (Env_drop n (subst_exvar_Env ty exA (env1 ::a (a2 ++ a1) +++ env2))) denv
  -> wf(Env_drop n (subst_exvar_Env ty exA (env1 ::a (a2 ++ a1) +++ env2)))
  -> wf(env1 ::a (a2 ++ exA :: a1) +++ env2)
  -> env1 ::a a1 |=ty (S_Mono ty)
  -> FullEInst (Env_drop n (env1 ::a (a2 ++ exA :: a1) +++ env2)) denv.
Proof.
  introv [dsub INST] WF1 WF2 WFTY. rewrite Env_drop_subst_exvar_Env_comm in *.
  dropdistr*. destruct (le_lt_dec n (Env_length env2)).
  - forwards NIL: nat_minus_greater. eassumption. rewrite NIL in *. rewr*.
    eapply umi_subst. rewr. eauto. rewrite Env_drop_distr'. eauto using wf_Env_drop.
    eassumption.
  - rewrite (Env_drop_greater n) in *. 2,3,4: crush.
    rewr*.
    assert (exA `notin` Env_Obj_exvars env1).
    { forwards DISJ: wf_Env_exvar_disj env1. norm in WF2. rep_Env_app_assoc in WF2. apply WF2.
      eapply in_disjoint_impl_notin1. eassumption. rewr. fsetdec. }
    destruct (n - Env_length env2).
    + simpl in *.
      rewrite subst_exvar_Env_notin_Env_idempotent in INST. 3:{ eauto. } 2:assumption.
      forwards [dty [dsub1 [dsub2 [? [? [? ?]]]]]]: umi_subst_head exA. eassumption. eassumption. constructor. eauto.
      constructor. eauto.
      assert (FrA (exA :: a1) env1). eauto. inv_FrA. eassumption.
      exists. eassumption.
    + simpl in *. exists.
      rewrite subst_exvar_Env_notin_Env_idempotent in INST. eassumption.
      rewrite Env_drop_Env_exvars_Obj. assumption.
      eauto using wf_Env_drop.
Qed.

(*** Main theorems *)
Theorem unification_maintains_instantiation : forall (env__in env__out : Env) (eqs : Eqs) (denv : DEnv),
    U env__in eqs env__out
  -> FullEInst env__out denv
  -> wf( env__in )
  -> FullEInst env__in denv.
Proof.
  introv UNI [Sub INST] WF1. inverts UNI.
  induction Us. eauto.
  forwards WF2: Uss_Wf. eassumption. auto.
  forwards [Sub__IH INST__IH]: IHUs. eassumption. assumption.
  destruct UNI; simpl in WF2; simpl in  INST__IH; eauto using umi_split, umi_subst.
Qed.

Theorem unification_maintains_instantiation__drop : forall (n : nat) (env__in env__out : Env) (eqs : Eqs) (denv : DEnv),
    U env__in eqs env__out
  -> FullEInst (Env_drop n env__out) denv
  -> wf(env__in)
  -> FullEInst (Env_drop n env__in) denv.
Proof.
  introv UNI [Sub INST] WF1. inverts UNI.
  induction Us. eauto.
  forwards WF2: Uss_Wf. eassumption. auto.
  forwards [Sub__IH INST__IH]: IHUs. eassumption. assumption.
  destruct UNI; simpl in WF2; simpl in  INST__IH; eauto using umi_split__drop, umi_subst__drop.
Qed.
