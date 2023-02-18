(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.
Require Import Defs.Defs.
Require Import Wf.Wf.

Require Import Sound.Imi.
Require Import Sound.Umi.
Require Import Sound.Uu.


(*** Lemmas *)
Lemma Inst_to_SubSump : forall (dsub : DSub) (dsch : DSch) (dty : DTy) (denv : DEnv) (env : Env) (sch : Sch) (a : A) (ty : Ty),
    env |= sch ≤ ⟨a⟩ ty
  -> varl a [<=] DSub_dom dsub
  -> DSub_app_t ty dsub = emb_Ty dty
  -> DSub_app sch dsub = emb_Sch dsch
  -> DSub_wf denv dsub
  -> SubSump denv dsch (DS_Mono dty).
Proof.
  introv INST INS EMB__ty EMB__sch SUBWF. gen dty dsch denv. induction INST; intros.
  - emb_auto. rewrite EMB__ty in *. forwards: emb_Ty_inj. eassumption. crush.
  - do_DSub_exA_decide dsub exA.
    + (*exA is in sub so this can't be*)
      assert (exA \in DSub_dom dsub). rewrite <- INS. rewr. fsetdec. crush.
    + emb_auto. eapply (SubSumpInst (L \u DSub_codom_dskvars dsub)).
      * instantiate (1 := dty0). eauto.
      * intros. eapply H.
        -- instantiate (1 := dskA). fsetdec.
        -- rewrite <- INS. rewr. fsetdec.
        -- eassumption.
        -- assert (lc_DTy dty0). eauto.
           rewrite subst_skvar_Sch_open_Sch_wrt_Ty. 2:auto. rewrite subst_dskvar_DSch_open_DSch_wrt_DTy. 2:auto. simpl. if_taut.
           rewrite DSub_app_open_comm. 2,3:auto. rewrite embed_Sch_open_comm. rewrite EMB.
           rewrite DSub_app_susbst_skvar_Sch. 2:auto. rewrite embed_Sch_subst_dskvar_DSch. crush. eauto.
        -- auto.
Qed.

Lemma AInst_shift_DAin_to_produced_DEnv : forall (denv__init : DEnv) (da1 da2 : DA) (a : A) (dsub__init dsub : DSub),
    {denv__init :::a da1, dsub__init }a|= a ~> {da2, dsub}
  -> exists da,
    {denv__init, dsub__init }a|= a ~> {da, dsub}
  /\ da [<=]l (da1 ++ da2).
Proof.
  intros. gen da2 dsub. induction a; intros; inv_AInst.
  - exists (nil : DA). auto.
  - forwards [da [INST SUB]]: IHa. eassumption.
    econstructor. split.
    + econstructor. instantiate (1 := da). 2:assumption.
      instantiate (1 := da1 ++ DA2 ++ DA1). eapply WfDTy_DEnv_sub. eassumption.
      unfold DEnv_sub. unfold_DEnv_to_Set. progress (autorewrite with DEnv_to_Set List_to_Set). fold_DEnv_to_Set.
      fold DEnv_sub.
      rewr_derel.
      rewrite (fold_right_varl (DA2 ++ DA1)).
      rewrite (fold_right_varl (da1 ++ DA2 ++ DA1 ++ da)). rewr. fsetdec.
    + rewrite SUB. autounfold. rewr. fsetdec.
Qed.

Lemma generalize_Sch_generalize_DSch__helper : forall (L : vars) (dsub : DSub) (sch : Sch) (exA : exvar) (dsch : DSch),
    DSub_app (generalize_Sch sch [exA] empty) dsub = emb_Sch (DS_Forall dsch)
  -> (exists denv : DEnv, DSub_wf denv dsub)
  -> exists dskA,
    dskA `notin` L
  /\ DSub_app sch (dsub ++ [(exA, DT_SkVar_f dskA)]) = emb_Sch (open_DSch_wrt_DTy dsch (DT_SkVar_f dskA)).
Proof.
  introv EMB WFS. remember (proj1_sig (atom_fresh (free_skvars_Sch sch \u (L \u free_skvars_Sch (emb_Sch dsch) \u DSub_codom_dskvars dsub)))) as dskA.
  erewrite (generalize_Sch_l_irrelevance (L \u free_skvars_Sch (emb_Sch dsch) \u DSub_codom_dskvars dsub)) in EMB.
  forwards: proj1_sig_fresh (free_skvars_Sch sch \u (L \u free_skvars_Sch (emb_Sch dsch) \u DSub_codom_dskvars dsub)).
  exists dskA. split.
  - fsetdec.
  - eapply (close_Sch_wrt_Ty_inj _ _ dskA).
    subst. simpl in EMB. emb_auto. rewrite embed_Sch_open_comm. subdist. simpl.
    rewrite DSub_app_close_Sch_wrt_Ty in EMB. rewrite EMB.
    rewrite close_Sch_wrt_Ty_open_Sch_wrt_Ty. reflexivity.
    forwards: proj1_sig_fresh (free_skvars_Sch sch \u (free_skvars_Sch (emb_Sch dsch) \u DSub_codom_dskvars dsub)).
    crush. fsetdec. eassumption.
Qed.

Inductive DA_for_A : DA -> A -> DSub -> Prop :=    (* defn DFrA *)
 | DA_for_A_nil  : DA_for_A (nil : DA) (nil : A) (nil : DSub)
 | DA_for_A_cons : forall (dskA:dskvar) (exA:exvar) (DA:DA) (A:A) (DSub:DSub)
     (DA_rec: DA_for_A DA A DSub),
     DA_for_A (cons dskA DA) (cons exA A) (((exA, DT_SkVar_f dskA)) :: DSub).
#[export] Hint Constructors DA_for_A : core.

Lemma generalize_Sch_generalize_DSch : forall (sch : Sch) (a : A) (dsch2 : DSch) (dsub : DSub) (denv : DEnv),
    DSub_app (generalize_Sch sch a empty) dsub = emb_Sch dsch2
  -> DSub_wf denv dsub
  -> (exists (env : Env), FrA a env /\ DSub_dom dsub [<=] Env_exvars env)
  -> exists dsch1 da dsub',
      generalize_DSch dsch1 da = dsch2
    /\ DSub_app sch (dsub ++ dsub') = emb_Sch dsch1
    /\ DA_for_A da a dsub'
    /\ DSub_wf (denv :::a da) (dsub ++ dsub')
    /\ DFrA da denv.
Proof.
  introv EMB WFS FR.
  gen denv dsub dsch2. listind a; intros.
  - simpl in EMB. exists dsch2 (nil:DA) (nil:DSub). crush.
  - rewrite generalize_sch_cons in EMB.
    assert (EQ__dsch2 : exists dsch2', dsch2 = DS_Forall dsch2'). simpl in EMB. emb_auto. exists. auto.
      destruct EQ__dsch2 as [dsch2' ?]. subst.
    forwards [dskA [NIV EMB']]: generalize_Sch_generalize_DSch__helper (free_dskvars_DSch dsch2' \u DEnv_dskvars denv). eassumption. exists denv. assumption.
    destruct FR as [env [FrA SUB__env]].
    forwards dsch1 da dsub' GEN__IH [EMB__IH [DAFORA__IH [WF__dsub DFR]]]: IHa. 3:eassumption. instantiate (1 := denv :::s dskA).
    apply DSub_wf_snoc. eauto. eapply in_disjoint_impl_notin1. symmetry.
    rewrite SUB__env. conv. apply FrA_props. eassumption. rewr. fsetdec. constructor. rewr. fsetdec.
    exists (env ::a [exA]). split. apply FrA_cons_shift. assumption. rewr. crush.
    eexists. exists (dskA :: da). exists ((exA, DT_SkVar_f dskA) :: dsub'). splits.
    + rewrite generalize_DSch_cons. rewrite GEN__IH. simpl.
      rewrite close_DSch_wrt_DTy_open_DSch_wrt_DTy. reflexivity. fsetdec.
    + rewr in EMB__IH. eassumption.
    + crush.
    + eapply DSub_wf_rewr. eassumption. rewr_derel. rewrite (fold_right_varl (dskA :: da)). rewr. fsetdec. rewr. fsetdec.
    + apply DFrA_cons_shift. eassumption. fsetdec.
Qed.

Lemma DA_for_A_AInst : forall DEnv__init DSub__init DA A DSub,
    DA_for_A DA A DSub
  -> {DEnv__init, DSub__init }a |= A ~> {DA, DSub}.
Proof.
  intros DEnv__init DSub__init DA A DSub DAFA. induction DAFA. auto.
  applys_eq AInstCons. norm. reflexivity. constructor. rewr. fsetdec. assumption.
Qed.

Lemma DA_for_A_DSub_dom : forall da a dsub,
    DA_for_A da a dsub
  -> DSub_dom dsub [=] varl a.
Proof. introv DAforA. induction DAforA; crush. Qed.

(*** Main theorem *)
Definition Inf_sound__def := forall (env__in : Env) (e : e) (a : A) (ty : Ty) (env__out : Env) (denv : DEnv) (dty : DTy),
    env__in |= e ▸ ⟨a⟩ ty =| env__out
  -> wf(env__in)
  -> FullEInst ((env__out ::a a) ::o ⟦S_Mono ty⟧) (denv :::o ⟦DS_Mono dty⟧d)
  -> denv |=m e ▸ dty.
Definition Inf_sound__prop (env__in : Env) (e : e) (a : A) (ty : Ty) (env__out : Env)
                          (inf : env__in |= e ▸ ⟨a⟩ ty =| env__out) : Prop := forall (denv : DEnv) (dty : DTy),
    wf(env__in)
  -> FullEInst ((env__out ::a a) ::o ⟦S_Mono ty⟧) (denv :::o ⟦DS_Mono dty⟧d)
  -> denv |=m e ▸ dty.
#[local] Hint Unfold Inf_sound__def Inf_sound__prop : core.

Definition Gen_sound__def := forall (env__in : Env) (e : e) (sch: Sch) (env__out : Env) (denv : DEnv) (dsch : DSch),
    env__in |= e ▸ sch =| env__out
  -> wf(env__in)
  -> FullEInst (env__out ::o ⟦sch⟧) (denv :::o ⟦dsch⟧d)
  -> denv |=p e ▸ dsch.
Definition Gen_sound__prop (env__in : Env) (e : e) (sch: Sch) (env__out : Env)
                          (gen : env__in |= e ▸ sch =| env__out) : Prop := forall (denv : DEnv) (dsch : DSch),
    wf(env__in)
  -> FullEInst (env__out ::o ⟦sch⟧) (denv :::o ⟦dsch⟧d)
  -> denv |=p e ▸ dsch.
#[local] Hint Unfold Gen_sound__def Gen_sound__prop : core.

Theorem EInst_WfTy_partial_DSub_app : forall (sch : Sch) (dsch : DSch) (env : Env) (denv : DEnv) (dsub dsub' : DSub),
    {▪, []}|= env ~> {denv, dsub}
  -> DSub_app sch (dsub' ++ dsub) = emb_Sch dsch
  -> env |=ty sch
  -> DSub_app sch           dsub  = emb_Sch dsch
  /\ denv |=dty dsch.
Proof.
  introv INST EMB WFTY.
  forwards [dsch' [EMB' WFDTY]]: EInst_WfTy_impl_emb. eassumption. eassumption.
  subdist in EMB. rewrite EMB' in EMB. rewr in EMB. apply emb_Sch_inj in EMB. crush.
Qed.

Corollary EInst_WfTy_partial_DSub_app_Ty : forall (ty : Ty) (dty : DTy) (env : Env) (denv : DEnv) (dsub dsub' : DSub),
    DSub_app_t ty (dsub' ++ dsub) = emb_Ty dty
  -> {▪, []}|= env ~> {denv, dsub}
  -> env |=ty (S_Mono ty)
  -> DSub_app_t ty           dsub  = emb_Ty dty.
Proof. introv EMB INST WFTY. forwards: EInst_WfTy_partial_DSub_app (S_Mono ty) (DS_Mono dty). eassumption. crush. eassumption. crush. Qed.

Theorem Inf_Gen_sound : Inf_sound__def /\ Gen_sound__def.
Proof.
  forwards: (Inf_Gen_mut Inf_sound__prop Gen_sound__prop)
  ; unfold Inf_sound__prop in *; unfold Gen_sound__prop in *
  .
  7:{ jauto. }

  (** var case*)
  - introv IN INSTANT WF [dsub INST].
    (**)
    forwards WF1 : Inf_Wf. econstructor; eauto. assumption.
    (**)
    EInst_props. eassumption. inv_Wf. constructor. eauto. auto. eauto. auto. crush.
    forwards [dsch [EMB IN']]: IN__sch Sch5. rewr. eauto. rewr in IN'.
    (**)
    applys TmVar dsch. eassumption.
    (**)
    inv_EInst'. eapply (Inst_to_SubSump (DSub2 ++ DSub1)). eassumption. 2,3:crush.
    + forwards [_ [_ EQ__A]]: AInst_props__base. eassumption.
      unfold DSub_dom. subst. rewr. fsetdec.
    + eapply DSub_wf_rewr. 3:reflexivity. rewr in WF__dsub. eassumption. rewr_derel. reflexivity.

  (** unit case*)
  - introv _ _ [dsub INST]. inv_EInst'. rewr*. emb_auto. crush.

  (** let case*)
  - introv FR INF IH WF__in [dsub INST].
    (**)
    (**)
    fresh_atom.
    (** We need the same with x' later*)
    forwards WF__out: Inf_Wf. eapply INF. eassumption. do 2 constructor. assumption. constructor. auto. crush. crush.
    (**)
    inv_EInst'. rewr*. emb_auto.
    (**)
    EInst_props__base. eapply EInstA. eassumption. apply AInst_merge; rewr; eassumption. rewr in SUB__wfdty.
    (**)
    econstructor.
    + forwards [FV__sk [_ LC]]: WfTy_props_mono1 (Envout ::a (A2 ++ A1)). inv_Wf. eapply WfTy_Env_sub. eassumption. eauto.
      eapply embed_Ty_WfDTy. eassumption. rewr. eassumption. rewrite <- SUB__sk.
      eassumption. eassumption.
    + intros x' NIL'. rewrite DEnv_cons_da_app_split. apply Mon_shift_DA. eapply IH. eassumption.
      do 2 constructor. assumption. constructor. auto. crush. crush.
      eexists. econstructor. constructor. constructor. constructor. all: rewr. 1,2: eassumption. 3,4:crush.
      * rewr.
        forwards EMB1': EInst_WfTy_partial_DSub_app_Ty Ty1 (dsub ++ DSub1) dsub0.
          eassumption. eapply EInstA. eassumption. rewr. eassumption. eauto.
        crush.
      * rewr. eapply AInst_init_DEnv_sub. eassumption. crush.

  (** app case*)
  - introv FR INF__e1 IH__e1 INF__e2 IH__e2 UNI WF__in [dsub INST__out].
    (**)
    forwards WF1: Inf_Wf. apply INF__e1. assumption. inv_Wf. rename WF into WF1.
    forwards WF2: Inf_Wf. apply INF__e2. eauto. inv_Wf. rename WF0 into WF2.
    rename Ty_5 into ty. rename Ty1 into ty1. rename Ty' into ty'. rename Ty2 into ty2.
    (**)
    forwards [ty__uni UNI']: U_unifies. eassumption.
    (**)
    assert (WF2': wf((((Env2 ::a (exB :: A2 ++ A1')) ::o ⟦⟨[]⟩ S_Mono (T_ExVar exB)⟧) ::o ⟦⟨[]⟩ S_Mono ty'⟧) ::o ⟦⟨[]⟩ S_Mono (T_Fun ty1 (T_ExVar exB))⟧)).
    { econstructor. 2:auto. constructor. 2:auto. econstructor. 2:auto. econstructor. assumption.
      - constructor. apply FrA_app_split. split. erewrite <- FrA_Obj. eauto. eassumption. crush.
      - constructor. crush.
      - eapply WfTy_Env_sub. eassumption. autounfold. rewr. crush.
      - constructor. eapply WfTy_Env_sub. eassumption. autounfold. rewr. crush. constructor. crush.
    }
    (**)
    forwards WF__out: U_Wf. apply UNI'. assumption.
    (**)
    forwards [dsch [EMB WFDTY]]: EInst_WfTy_impl_emb (S_Mono ty__uni). eassumption.
    inv_Wf. eapply WfTy_Env_sub. eassumption. rewr_erel. fsetdec.
    destruct dsch as [dty'|?]. 2:inverts EMB. emb_auto.
    (**)
    forwards [?dsub INST2]: unification_maintains_instantiation.
      { apply UNI'. }
      { exists. econstructor.
        - econstructor. eauto. auto. instantiate (1 := DS_Mono dty'). rewr. crush.
        - auto.
        - instantiate (1 := DS_Mono dty'). rewr. crush.
      }
      assumption.
    forwards [_ [_ [_ [_ SUB__wf]]]]: EInst_props. apply INST2. eauto. auto. crush. rewr in SUB__wf.
    inv_EInst'. rewr*. emb_auto.
    (**)
    norm in EMB1. rewrite app_assoc in EMB1. eapply EInst_WfTy_partial_DSub_app_Ty in EMB1.
    2:{ eapply EInstA. eassumption. rewr. eassumption. }
    2:{ eassumption. }
    (**)
    norm in EMB5. rewrite (DSub_unique_sub_DSub_app_t _ ([(exB, DTy5)] ++ dsub ++ dsub0 ++ DSub0)) in EMB5.
    2:{ apply DSub_full_t_emb. exists. eassumption. }
    2:{ rewr_dsrel. fsetdec'. }
    2:{ unfold DSub_unique. introv IN1 IN2. eapply SUB__wf. instantiate (1 := exA).
        rewr_derel. rewr_derel in IN1. fsetdec'.
        rewr_derel. rewr_derel in IN2. fsetdec'. }
    rewrite app_assoc in EMB5.
    forwards [da0' [?INST SUB]]: AInst_shift_DAin_to_produced_DEnv. apply INSTA0. eapply EInst_WfTy_partial_DSub_app_Ty in EMB5.
    2:{ apply EInstA. eassumption. rewr. eapply AInst_swap_subinit. eassumption. }
    2:{ eapply WfTy_Env_sub. eassumption. rewr_erel. fsetdec. }
    (**)
    assert (dty = dty2). destruct (eq_Ty (emb_Ty dty) (emb_Ty dty2)). eauto using emb_Ty_inj. crush. subst.
    (**)
    forwards [?dsub INST2]: inference_maintains_instantiation. apply INF__e2. constructor; auto.
      exists. econstructor. eauto. rewr. eassumption. rewr. instantiate (1 := DS_Mono (DT_Fun dty1 dty2)). crush.
    (**)
    eapply (TmApp _ _ _ _ dty1).
    (* assert ((DEnv_0 :::a (DA2 ++ da0 ++ da)) |=m e1 ▸ DT_Fun dty1 dty2). *)
    +
      inv_EInst'.
      eapply Mon_DEnv_x_sub. eapply IH__e1. auto.
        exists. inv_EInst'. rewr*. econstructor. econstructor. eassumption. rewr. apply INSTA1. auto. rewr. assumption.
        autounfold. split. rewr. rewrite (fold_right_varl (DA2 ++ da0 ++ da)). rewr. fsetdec. rewr. crush.
    + eapply Mon_DEnv_x_sub. eapply (IH__e2 (DEnv_0 :::o ⟦⟨da⟩ DS_Mono (DT_Fun dty1 dty2)⟧d :::a da0')). eauto.
      * exists. econstructor. econstructor. econstructor. eassumption. rewr. eassumption. rewr. rewrite EMB1. reflexivity.
        rewr. eapply AInst_swap_subinit. eapply AInst_init_DEnv_sub. eassumption. crush. auto. rewr. crush.
      * autounfold. split. rewr. autounfold in SUB. rewrite SUB. rewr. rewrite (fold_right_varl (DA2 ++ da0 ++ da)). rewr. fsetdec.
        rewr. crush.

  (** let case *)
  - introv POL IH__e1 INF IH__e2 WF1 [dsub INST__out].
    forwards [x NIL__x]: atom_fresh.
    (**)
    forwards WF2: Gen_Wf. eassumption. assumption.
    (**)
    forwards WF__out: Inf_Wf. eapply INF. eassumption. eauto with slow.
    inv_EInst'. inv_Wf. rewr*.
    (**)
    forwards [dsch' [EMB' WFDTY]]: EInst_WfTy_impl_emb. 2:apply WFTY0. eassumption.
    (**)
    econstructor.
    + forwards [dsub INST__mid]: inference_maintains_instantiation. eapply INF. eassumption. eapply wf_Env_Obj_noa_x1. auto.
        exists. econstructor. eassumption. rewr. eassumption. inv_EInst'. rewr*.
      eapply DGen_DEnv_x_sub. apply IH__e1. auto. exists. econstructor. eassumption. auto. rewr. eassumption. auto.
    + intros y NIL__y.
      (** This usage of Mon_DEnv_x_sub just reshuffles *)
      eapply Mon_DEnv_x_sub. eapply IH__e2. eassumption. eauto.
      exists. econstructor. econstructor. econstructor. eassumption. rewr. eassumption. rewr.
      eapply AInst_init_DEnv_sub. eassumption. eauto. auto. rewr. eassumption. autounfold.
      (** reshuffeling here *)
      split. rewr. fsetdec. rewr_dsrel. fsetdec'.

  (** generalization case *)
  - introv INF IH GEN WF__in [dsub INST__out].
    forwards WF__out: Inf_Wf. eassumption. assumption. inv_Wf.
    inv_EInst'. rewr*. subst.
    EInst_props. eassumption. auto. auto. crush. rewr*.
    (**)
    forwards [dsch' [da [dsub' [GEN [AFORA [EMB' [WF__dusb' DFR]]]]]]]: generalize_Sch_generalize_DSch denv. eassumption. eauto. exists Envout. crush.
    emb_auto.
    (**)
    eapply TmGen. 3:{ reflexivity. } eassumption. apply IH. auto.
    exists. econstructor. econstructor. eassumption. rewr.
    eauto using DA_for_A_AInst. auto. rewr.
    rewrite DSub_app_t_app_symm. 2:{ apply DSub_unique_app_symm. eauto. }
    crush.
Qed.

Theorem Soundness__mono : forall (e : e) (a : A) (ty : Ty) (dty : DTy),
    • |= e ▸ ⟨a⟩ ty =| •
  -> FullEInst (<a>a ::o ⟦S_Mono ty⟧) <⟦DS_Mono dty⟧d>do
  -> ▪ |=m e ▸ dty.
Proof.
  introv Inf [dsub INST]. forwards S : proj1 Inf_Gen_sound. unfold Inf_sound__def in S.
  forwards: S ▪. eassumption. auto. exists dsub. eassumption. eassumption.
Qed.

Theorem Soundness__poly : forall (e : e) (sch : Sch) (dsch : DSch),
    • |= e ▸ sch =| •
  -> FullEInst <⟦sch⟧>o <⟦dsch⟧d>do
  -> ▪ |=p e ▸ dsch.
Proof.
  introv Gen [dsub INST]. forwards S : proj2 Inf_Gen_sound. unfold Inf_sound__def in S.
  forwards: S ▪. eassumption. auto. exists dsub. eassumption. eassumption.
Qed.
