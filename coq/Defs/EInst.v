(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Defs.AInst.
Require Import Defs.DEnv.
Require Import Defs.DSub.
Require Import Defs.Env.
Require Import Defs.Embed.
Require Import Defs.Freevars.
Require Import Defs.Lc.
Require Import Defs.List.
Require Import Defs.Obj.
Require Import Defs.Set.
Require Import Defs.Varbindings.

Require Import Defs.FrA.
Require Import Defs.WfDTy.
Require Import Defs.WfEnv.
Require Import Defs.WfTy.

(*** Notation, tactics etc*)
Notation "{ A ,  B } |= C  ~>  { D ,  E }" := (EInst A B C D E) (at level 50) : type_scope.

Notation FullEInst env denv := (exists (dsub : DSub), {▪, []}|= env ~> {denv, dsub}).

Ltac EInst_genind H :=
  match type of H with
    | EInst _ _ ?env ?denv ?dsub => gen denv dsub; induction env; intros
  end; inverts H.
Ltac EInst_genind' H env :=
  match type of H with
    | EInst _ _ _ ?denv ?dsub => gen denv dsub; induction env; intros
  end; inverts H.
Ltac EInst_genind_noinv H env :=
  match type of H with
    | EInst _ _ _ ?denv ?dsub => gen denv dsub; induction env; intros
  end.

Ltac inv_EInst_ :=
  match goal with
    | [ H : {_, _}|= _ ::o ⟦⟨ _ ⟩ _ ⟧ ~> {_, _} |- _ ] => inverts H
    | [ H : {_, _}|= _ ::a _ ~> {_, _} |- _ ] => inverts H
    | [ H : {_, _}|= _ ::s _ ~> {_, _} |- _ ] => inverts H
    | [ H : {_, _}|= _ ::x _ :- _ ~> {_, _} |- _ ] => inverts H
  end.
Ltac inv_EInst := repeat inv_EInst_.
Ltac inv_EInst' := repeat (try inv_EInst; inv_AInst).

(*** Props *)
Theorem DSub_to_A_app_distr : forall (dsub1 dsub2 : DSub),
    DSub_to_A (dsub2 ++ dsub1) = DSub_to_A dsub2 ++ DSub_to_A dsub1.
Proof. induction dsub2; simpl; crush. Qed.
#[export] Hint Rewrite DSub_to_A_app_distr : core.

(* Theorem EInst_props : forall (denv__init : DEnv) (dsub__init : DSub) (env : Env) (denv : DEnv) (dsub : DSub), *)
(*     {denv__init, dsub__init}|= env ~> {denv, dsub} *)
(*   -> Env_exvars env [=] DSub_dom dsub *)
(*   /\ Env_skvars env [<=] DEnv_dskvars denv *)
(*   /\ DSub_wf denv dsub *)
(*   /\ (forall (x : termvar) (sch : Sch), In (x, sch) (Env_bindings env) -> exists dsch, DSub_app (dsub ++ dsub__init) sch = emb_Sch dsch /\ In (x, dsch) (DEnv_bindings denv)). *)
(* Proof. *)
(*   introv INST. EInst_genind INST. *)
(*   - crush. *)
(*   - forwards IH__ex IH__sk IH__wf IH__insub: IHenv; try eassumption. rewr. splits. *)
(*     + rewrite IH__ex. *)
(*       forwards: AInst_DSub_to_A. eassumption. unfold DSub_dom. crush. *)
(*     + crush. *)
(*     + unfold DSub_wf. auto. (*placeholder subwf*) *)
(*     + intros x sch IN. forwards [dsch [EMB IN']]: IH__insub x sch IN. exists dsch. split; subdist*; crush. *)
(*   - forwards IH__ex IH__sk IH__wf IH__insub: IHenv; try eassumption. splits. 1,2,3:crush. *)
(*     intros y sch IN. simpl in IN. destr. *)
(*     + exists. split. eassumption. simpl. auto. *)
(*     + forwards [dsch [EMB' IN']]: IH__insub y sch. assumption. exists dsch. split; subdist*; crush. *)
(*   - forwards IH__ex IH__sk IH__wf IH__insub: IHenv; try eassumption. splits. 1,2,3:crush. *)
(*     intros y sch IN. simpl in IN. *)
(*     forwards [dsch [EMB' IN']]: IH__insub y sch. assumption. exists dsch. split; subdist*; crush. *)
(* Qed. *)
(* Ltac EInst_props := forwards [?EQ__ex [?SUB__sk [?WFSUB ?INIMPL]]]: EInst_props. *)

Theorem disjoint_union : forall s1 s2 s2',
    s1 [><] s2
  -> s1 [><] s2'
  -> s1 [><] s2 \u s2'.
Proof. unfold AtomSetImpl.disjoint. intros. fsetdec. Qed.

Theorem Env_exvars_Obj_sub : forall (env : Env),
    Env_exvars env [<=] Env_Obj_exvars env.
Proof. intros. unfold AtomSetImpl.Subset. crush. Qed.
#[export] Hint Resolve Env_exvars_Obj_sub : core.

Theorem varl_DSub_to_A_DSub_dom : forall dsub,
    varl (DSub_to_A dsub) = DSub_dom dsub.
Proof. crush. Qed.
#[export] Hint Rewrite varl_DSub_to_A_DSub_dom : core.

Theorem DSub_wf_cons_var : forall (denv : DEnv) (x : termvar) (dsch : DSch) (dsub : DSub),
    DSub_wf  denv                 dsub
  <-> DSub_wf (denv :::x x :- dsch) dsub.
Proof.
  intros. assert (denv [<=]de denv :::x x :- dsch). crush. split; intros. eauto.
  eapply DSub_wf_rewr. eassumption. rewr_derel. reflexivity. reflexivity. Qed.
Theorem DSub_wf_cons_var1 : forall (denv : DEnv) (x : termvar) (dsch : DSch) (dsub : DSub),
    DSub_wf  denv                 dsub
  -> DSub_wf (denv :::x x :- dsch) dsub.
Proof. apply DSub_wf_cons_var. Qed.
Theorem DSub_wf_cons_var2 : forall (denv : DEnv) (x : termvar) (dsch : DSch) (dsub : DSub),
    DSub_wf (denv :::x x :- dsch) dsub
  -> DSub_wf  denv                 dsub.
Proof. apply DSub_wf_cons_var. Qed.
#[export] Hint Resolve DSub_wf_cons_var1 : core.

Theorem DSub_wf_cons_obj : forall (denv : DEnv) (dobj : DObj) (dsub : DSub),
    DSub_wf  denv            dsub
  <-> DSub_wf (denv :::o dobj) dsub.
Proof.
  intros. assert (denv [<=]de denv :::o dobj). crush. split; intros. eauto.
  eapply DSub_wf_rewr. eassumption. rewr_derel. reflexivity. reflexivity. Qed.
Theorem DSub_wf_cons_obj1 : forall (denv : DEnv) (dobj : DObj) (dsub : DSub),
    DSub_wf  denv            dsub
  -> DSub_wf (denv :::o dobj) dsub.
Proof. apply DSub_wf_cons_obj. Qed.
Theorem DSub_wf_cons_obj2 : forall (denv : DEnv) (dobj : DObj) (dsub : DSub),
    DSub_wf (denv :::o dobj) dsub
  -> DSub_wf  denv            dsub.
Proof. apply DSub_wf_cons_obj. Qed.
#[export] Hint Resolve DSub_wf_cons_obj1 : core.

Theorem EInst_props__base : forall (denv__init : DEnv) (dsub__init : DSub) (env : Env) (denv : DEnv) (dsub : DSub),
    {denv__init, dsub__init}|= env ~> {denv, dsub}
  -> Env_exvars env [=] DSub_dom dsub
  /\ Env_skvars env [<=] DEnv_dskvars denv
  /\ DSub_WfDTy (denv__init ++++ denv) dsub
  /\ ( forall (x : termvar) ( sch :  Sch),  SchPSI.In (x,  sch) ( Env_bindings  env)
      -> exists dsch, DSub_app sch (dsub ++ dsub__init) = emb_Sch dsch /\ DSchPSI.In (x, dsch) (DEnv_bindings denv))
  /\ ( forall (x : termvar) (dsch : DSch), DSchPSI.In (x, dsch) (DEnv_bindings denv)
      -> exists  sch, DSub_app sch (dsub ++ dsub__init) = emb_Sch dsch /\  SchPSI.In (x,  sch) ( Env_bindings  env)).
Proof.
  introv INST.
  EInst_genind INST.
  - crush.
  - forwards IH__ex IH__sk IH___subwf IH__insub IH__indsub: IHenv; try eassumption.
    forwards [WFSUB1 [WFSUB2 EQ__A]]: AInst_props__base. eassumption. subst.
    splits.
    + rewr. rewrite IH__ex. crush.
    + rewr. crush.
    + eapply DSub_WfDTy_app. norm. norm in WFSUB1. eassumption. eauto.
    + rewr. intros x  sch IN. rewr in IN. forwards [dsch [EMB IN']]: IH__insub  x  sch IN. exists dsch. split. subdist*. crush. rewr. assumption.
    + rewr. intros x dsch IN. rewr in IN. forwards [ sch [EMB IN']]: IH__indsub x dsch IN. exists  sch. split. subdist*. crush. rewr. assumption.
  - forwards IH__ex IH__sk IH__subwf IH__insub IH__indsub: IHenv; try eassumption. eauto. splits. 1,2:crush. eauto.
    + intros y sch IN. rewr in IN. indestr.
      * forwards [dsch [EMB' IN']]: IH__insub y sch. assumption. exists dsch. split; subdist*; crush.
      * rewr in H. destr. exists. split. eassumption. rewr. fsetdec.
    + intros y dsch IN. rewr in IN. indestr.
      * forwards [sch [EMB' IN']]: IH__indsub y dsch. assumption. exists sch. split; subdist*; crush.
      * rewr in H. destr. exists. split. eassumption. rewr. fsetdec.
  - forwards IH__ex IH__sk IH__subwf IH__insub IH__indsub: IHenv; try eassumption. eauto. splits. 1,2:crush. eauto.
    + intros x sch IN. rewr in IN. indestr.
      * forwards [dsch [EMB' IN']]: IH__insub x sch. assumption. exists dsch. split; subdist*; crush.
    + intros x dsch IN. rewr in IN. indestr.
      * forwards [sch [EMB' IN']]: IH__indsub x dsch. assumption. exists sch. split; subdist*; crush.
Qed.
Ltac EInst_props__base := forwards [?EQ__ex [?SUB__sk [?SUB__wfdty [?IN__sch ?IN__dsch]]]]: EInst_props__base.

Corollary EInst_props__base1 : forall (denv__init : DEnv) (dsub__init : DSub) (env : Env) (denv : DEnv) (dsub : DSub),
    {denv__init, dsub__init}|= env ~> {denv, dsub}
  -> Env_exvars env [=] DSub_dom dsub.
Proof. apply EInst_props__base. Qed.
Corollary EInst_props__base2 : forall (denv__init : DEnv) (dsub__init : DSub) (env : Env) (denv : DEnv) (dsub : DSub),
    {denv__init, dsub__init}|= env ~> {denv, dsub}
  -> Env_skvars env [<=] DEnv_dskvars denv.
Proof. apply EInst_props__base. Qed.
Corollary EInst_props__base3 : forall (denv__init : DEnv) (dsub__init : DSub) (env : Env) (denv : DEnv) (dsub : DSub),
    {denv__init, dsub__init}|= env ~> {denv, dsub}
  -> DSub_WfDTy (denv__init ++++ denv) dsub.
Proof. apply EInst_props__base. Qed.

Theorem EInst_props__wf : forall (denv__init : DEnv) (dsub__init : DSub) (env : Env) (denv : DEnv) (dsub : DSub),
    {denv__init, dsub__init}|= env ~> {denv, dsub}
  -> wf(env)
  -> DSub_wf denv__init dsub__init
  -> Env_exvars env [><] DSub_dom dsub__init
  -> DSub_wf (denv__init ++++ denv) (dsub ++ dsub__init).
Proof.
  introv INST WF SUB__wf DISJ__dusbinit.
  EInst_genind INST.
  - crush.
  - forwards IH: IHenv; try eassumption. eauto. eapply disj_subset_proper. 3:eassumption. crush. crush.
    forwards IH__ex _ _ _: EInst_props__base. eassumption.
    forwards [_ [_ H__A]]: AInst_props__base. eassumption. subst.
    forwards WF__dsub: AInst_props__wf. eassumption. rewr. apply disjoint_union. rewrite <- IH__ex.
      forwards DISJ: FrA_props3 (DSub_to_A DSub2). eauto. rewr in DISJ. conv. assumption.
      eapply disj_subset_proper. 3:apply DISJ__dusbinit. crush. reflexivity. eauto. eassumption.
    rewr. eassumption.
  - rewr in DISJ__dusbinit.
    forwards IH: IHenv; try eassumption. eauto. crush.
  - rewr in DISJ__dusbinit.
    forwards IH: IHenv; try eassumption. eauto. crush.
Qed.

Theorem EInst_props : forall (denv__init : DEnv) (dsub__init : DSub) (env : Env) (denv : DEnv) (dsub : DSub),
    {denv__init, dsub__init}|= env ~> {denv, dsub}
  -> wf(env)
  -> DSub_wf denv__init dsub__init
  -> Env_exvars env [><] DSub_dom dsub__init
  -> Env_exvars env [=] DSub_dom dsub
  /\ Env_skvars env [<=] DEnv_dskvars denv
  /\ ( forall (x : termvar) ( sch :  Sch),  SchPSI.In (x,  sch) ( Env_bindings  env)
      -> exists dsch, DSub_app sch (dsub ++ dsub__init) = emb_Sch dsch /\ DSchPSI.In (x, dsch) (DEnv_bindings denv))
  /\ ( forall (x : termvar) (dsch : DSch), DSchPSI.In (x, dsch) (DEnv_bindings denv)
      -> exists  sch, DSub_app sch (dsub ++ dsub__init) = emb_Sch dsch /\  SchPSI.In (x,  sch) ( Env_bindings  env))
  /\ DSub_wf (denv__init ++++ denv) (dsub ++ dsub__init).
Proof. intros. forwards: EInst_props__base. eassumption. destr. splits; try eassumption. eapply EInst_props__wf; eassumption. Qed.
Ltac EInst_props := forwards [?EQ__ex [?SUB__sk [?IN__sch [?IN__dsch ?WF__dsub]]]]: EInst_props.

Theorem EInst_props' : forall (env : Env) (denv : DEnv) (dsub : DSub),
    {▪, []}|= env ~> {denv, dsub}
  -> wf(env)
  -> Env_exvars env [=] DSub_dom dsub
  /\ Env_skvars env [<=] DEnv_dskvars denv
  /\ ( forall (x : termvar) ( sch :  Sch),  SchPSI.In (x,  sch) ( Env_bindings  env)
      -> exists dsch, DSub_app sch dsub = emb_Sch dsch /\ DSchPSI.In (x, dsch) (DEnv_bindings denv))
  /\ ( forall (x : termvar) (dsch : DSch), DSchPSI.In (x, dsch) (DEnv_bindings denv)
      -> exists  sch, DSub_app sch dsub = emb_Sch dsch /\  SchPSI.In (x,  sch) ( Env_bindings  env))
  /\ DSub_wf denv dsub.
Proof. intros. forwards: EInst_props ▪ ([]:DSub). eassumption. eassumption. crush. crush. rewr*. jauto. Qed.
Ltac EInst_props' := forwards [?EQ__ex [?SUB__sk [?IN__sch [?IN__dsch ?WF__dsub]]]]: EInst_props'.

(*** Split/merge *)
Theorem EInst_split : forall (denv__init : DEnv) (dsub__init : DSub) (env1 env2 : Env) (denv : DEnv) (dsub : DSub),
    {denv__init, dsub__init}|= env1 +++ env2 ~> {denv, dsub}
  -> exists (denv1 denv2 : DEnv) (dsub1 dsub2 : DSub),
      denv = denv1 ++++ denv2
    /\ dsub = dsub2 ++ dsub1
    /\ {denv__init, dsub__init}|= env1 ~> {denv1, dsub1}
    /\ {denv__init ++++ denv1, dsub1 ++ dsub__init}|= env2 ~> {denv2, dsub2}.
Proof.
  introv INST.
  EInst_genind_noinv INST env2.
  - do 4 eexists. splits. 3:{ eassumption. } 3:{ auto. } all: auto.
  - inverts INST.
  - inverts INST.
    forwards: IHenv2. eassumption. destr.
    do 4 eexists. splits. 3:{ eassumption. } 3:{ econstructor; norm*; eassumption. }
    all: norm; auto.
  - inverts INST.
    forwards: IHenv2. eassumption. destr.
    do 4 eexists. splits. 3:{ eassumption. } 3:{ econstructor; norm*; eassumption. }
    all: norm; auto.
  - inverts INST.
    forwards: IHenv2. eassumption. destr.
    do 4 eexists. splits. 3:{ eassumption. } 3:{ econstructor; norm*; eassumption. }
    all: norm; auto.
Qed.
Ltac EInst_split_destr := forwards [?denv [?denv [?dsub [?dsub [?EQ__denv [?EQ__dsub [?INST ?INST]]]]]]]: EInst_split.

Theorem EInst_merge : forall (denv__init denv1 denv2 : DEnv) (dsub__init dsub1 dsub2 : DSub) (env1 env2 : Env),
    {denv__init, dsub__init}|= env1 ~> {denv1, dsub1}
  -> {denv__init ++++ denv1, dsub1 ++ dsub__init}|= env2 ~> {denv2, dsub2}
  -> {denv__init, dsub__init}|= env1 +++ env2 ~> {denv1 ++++ denv2, dsub2 ++ dsub1}.
Proof.
  introv INST1 INST2. EInst_genind INST2.
  - crush.
  - rewr. econstructor. eapply IHenv2; auto. crush.
  - rewr. econstructor. eapply IHenv2; auto. crush.
  - forwards: EInstObjSch. eapply IHenv2. eassumption.
    norm*. eassumption.
    norm*. eassumption.
    norm*. eassumption.
Qed.

(*** EInst to EMB *)
(* Lemma EInst_WfTy_impl_emb_helper : forall (sch : Sch) (env : Env) (denv : DEnv) (dsub : DSub), *)
(*     {▪, []}|= env ~> {denv, dsub} *)
(*   -> env |=ty sch *)
(*   -> exists dsch, DSub_app sch dsub = emb_Sch dsch *)
(*   /\ free_dskvars_DSch dsch [<=] DEnv_dskvars denv. *)
(* Proof. *)
(*   introv INST WFTY. *)
(*   rewrite WfTy_props in WFTY. destruct WFTY as [IN__sk [IN__ex LC]]. clear LC. *)
(*   gen denv. Sch_Ty_ind sch; intros. *)
(*   - exists (DS_Mono (DT_SkVar_b n)). crush. *)
(*   - exists (DS_Mono (DT_SkVar_f skA)). crush. *)
(*   - do_DSub_exA_decide dsub exA. *)
(*     + false. apply NIS. rewrite <- SUB__skA. rewrite <- IN__ex. crush. *)
(*     + exists (DS_Mono dty). *)
(*       (* assert (denv |=dty DS_Mono dty). crush. *) *)
(*       split. crush. crush. *)
(*       forwards: DSub_wf_prop. eassumption. eassumption. *)
(*       crush. *)
(*   - exists (DS_Mono DT_Unit). crush. *)
(*   - rewr*. *)
(*     forwards [dty1 [EMB1 FV1]]: IHTy1; try fsetdec. emb_auto. *)
(*     forwards [dty2 [EMB2 FV2]]: IHTy2; try fsetdec. emb_auto. *)
(*     exists (DS_Mono (DT_Fun dty dty0)). crush. *)
(*   - forwards [dsch EMB]: IHsch; try fsetdec.  *)
(*     exists (DS_Forall dsch). crush. *)
(* Qed. *)

Lemma EInst_WfTy_impl_emb_helper : forall (sch : Sch) (env : Env) (denv : DEnv) (dsub : DSub),
    {▪, []}|= env ~> {denv, dsub}
  -> env |=ty sch
  -> exists dsch, DSub_app sch dsub = emb_Sch dsch
  /\ free_dskvars_DSch dsch [<=] DEnv_dskvars denv.
Proof.
  introv INST WFTY.
  apply EInst_props__base in INST. destruct INST as [SUB__skA [SUB__exA [WF _]]]. rewr in WF.
  rewrite WfTy_props in WFTY. destruct WFTY as [IN__sk [IN__ex LC]]. clear LC.
  gen denv. Sch_Ty_ind sch; intros.
  - exists (DS_Mono (DT_SkVar_b n)). crush.
  - exists (DS_Mono (DT_SkVar_f skA)). crush.
  - do_DSub_exA_decide dsub exA.
    + false. apply NIS. rewrite <- SUB__skA. rewrite <- IN__ex. crush.
    + exists (DS_Mono dty).
      assert (denv |=dty DS_Mono dty). eauto.
      split. crush. crush.
  - exists (DS_Mono DT_Unit). crush.
  - rewr*.
    forwards [dty1 [EMB1 FV1]]: IHTy1; try fsetdec. auto. emb_auto.
    forwards [dty2 [EMB2 FV2]]: IHTy2; try fsetdec. auto. emb_auto.
    exists (DS_Mono (DT_Fun dty dty0)). crush.
  - forwards [dsch EMB]: IHsch; try fsetdec. auto.
    exists (DS_Forall dsch). crush.
Qed.

Theorem EInst_WfTy_impl_emb : forall (sch : Sch) (env : Env) (denv : DEnv) (dsub : DSub),
    {▪, []}|= env ~> {denv, dsub}
  -> env |=ty sch
  -> exists dsch, DSub_app sch dsub = emb_Sch dsch
          /\ denv |=dty dsch.
Proof.
  introv INST WFTY.
  forwards dsch EMB FR: EInst_WfTy_impl_emb_helper. eassumption. eassumption.
  exists dsch. split. jauto. apply WfDTy_props. split. eassumption.
  forwards: DSub_app_lc sch dsub. eauto. exists. eauto using EInst_props__base3. rewrite EMB in *.
  apply embed_Sch_lc. assumption.
Qed.

(* Theorem EInst_WfTy_partial_DSub_app : forall (sch : Sch) (dsch : DSch) (env : Env) (denv : DEnv) (dsub dsub' : DSub), *)
(*     {▪, []}|= env ~> {denv, dsub} *)
(*   -> DSub_app (dsub' ++ dsub) sch = emb_Sch dsch *)
(*   -> env |=ty sch *)
(*   -> DSub_app           dsub  sch = emb_Sch dsch *)
(*   /\ denv |=dty dsch. *)
(* Proof. *)
(*   introv INST EMB WFTY. *)
(*   forwards [dsch' [EMB' WFDTY]]: EInst_WfTy_impl_emb. eassumption. eassumption. *)
(*   subdist in EMB. rewrite EMB' in EMB. rewr in EMB. apply emb_Sch_inj in EMB. crush. *)
(* Qed. *)

(* Corollary EInst_WfTy_partial_DSub_app_Ty : forall (ty : Ty) (dty : DTy) (env : Env) (denv : DEnv) (dsub dsub' : DSub), *)
(*     DSub_app_t (dsub' ++ dsub) ty = emb_Ty dty *)
(*   -> {▪, []}|= env ~> {denv, dsub} *)
(*   -> env |=ty (S_Mono ty) *)
(*   -> DSub_app_t           dsub  ty = emb_Ty dty. *)
(* Proof. introv EMB INST WFTY. forwards: EInst_WfTy_partial_DSub_app (S_Mono ty) (DS_Mono dty). eassumption. crush. eassumption. crush. Qed. *)

(*** Unsorted *)

