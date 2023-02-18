(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Defs.DEnv.
Require Import Defs.DSub.
Require Import Defs.Env.
Require Import Defs.List.
Require Import Defs.Set.

Require Import Defs.FrA.
Require Import Defs.WfDTy.

(*** Notation, tactics etc*)
Notation "{ A ,  B }a |= C  ~>  { D ,  E }" := (AInst A B C D E) (at level 50) : type_scope.

(** Ltac inv_Ainst --> see bottom of file *)

Ltac AInst_genind H :=
  match type of H with
    | AInst _ _ ?a ?da ?dsub => gen da dsub; induction a; intros
  end; inverts H.
Ltac AInst_genind' H a :=
  match type of H with
    | AInst _ _ _ ?da ?dsub => gen da dsub; induction a; intros
  end; inverts H.


(*** Props *)
Theorem varl_DSub_to_A_DSub_dom : forall (dsub : DSub),
    varl (DSub_to_A dsub) = DSub_dom dsub.
Proof.
  intros. induction dsub. crush. simpl. rewr. rewrite IHdsub. reflexivity. Qed.
#[export] Hint Rewrite varl_DSub_to_A_DSub_dom : core.

Theorem AInst_props__base : forall denv__init dsub__init a da dsub,
    AInst denv__init dsub__init a da dsub
  -> DSub_WfDTy (denv__init :::a da) dsub
  /\ (DSub_WfDTy denv__init dsub__init -> DSub_WfDTy (denv__init :::a da) (dsub ++ dsub__init))
  /\ DSub_to_A dsub = a.
Proof.
  introv AINST. induction AINST.
  - split; crush.
  - destr. assert (DSub_WfDTy (DEnvin :::a (DA2 ++ DA1)) ((exA, DTy5) :: DSub_5)).
    unfold DSub_WfDTy. intros. rewr in H. indestr.
    + crush.
    + applys WfDTy_DEnv_sub (DEnvin :::a DA1). eauto. crush.
    + splits. assumption. 2:crush. intros.
      unfold DSub_WfDTy. intros. rewr in H3. indestr.
      * rewr in H3. crush.
      * eauto.
      * eauto.
Qed.

Theorem AInst_props__wf : forall denv__init dsub__init a da dsub,
    AInst denv__init dsub__init a da dsub
  -> varl a [><] DSub_dom dsub__init
  -> (exists env, FrA a env)
  -> DSub_wf denv__init dsub__init
  -> DSub_wf (denv__init :::a da) (dsub ++ dsub__init).
Proof.
  introv AINST. gen da dsub. induction 1.
  - crush.
  - intros. forwards: IHAINST. assert (varl A5 [<=] varl (exA :: A5)). crush. rewrite H2. assumption.
    destruct H0. inverts H0. eauto. assumption.
    forwards [_ [WFDTY' _]]: AInst_props__base. eapply AInstCons. 1,2:eassumption.
    split. eauto. unfold DSub_wf in *.
    + autounfold. simpl. introv IN1 IN2. rewr*.
      forwards [_ [_ EQ]]: AInst_props__base. eassumption.
      rewrite DTyPS_facts.union_iff in IN1. rewrite DTyPS_facts.union_iff in IN2. destr.
      * crush.
      * rewr*. destr. indestr.
        -- assert (IN1 : exA0 \notin Env_Obj_exvars (env ::a (DSub_to_A DSub_5))). auto. rewr in IN1.
           assert (IN2 : exA0 \notin Env_Obj_exvars (oneA (DSub_to_A DSub_5))). rewr. fsetdec. rewr in IN2.
           assert (exA0 \in DSub_dom DSub_5). eauto.
           fsetdec.
        -- false. applys in_disjoint_impl exA0. eassumption. fsetdec. eauto.
      * rewr*. destr. indestr.
        -- assert (IN1 : exA0 \notin Env_Obj_exvars (env ::a (DSub_to_A DSub_5))). auto. rewr in IN1.
           assert (IN2 : exA0 \notin Env_Obj_exvars (oneA (DSub_to_A DSub_5))). rewr. fsetdec. rewr in IN2.
           assert (exA0 \in DSub_dom DSub_5). eauto.
           fsetdec.
        -- false. applys in_disjoint_impl exA0. eassumption. fsetdec. eauto.
      * unfold DSub_unique in H5. eapply H5; rewr; eassumption.
Qed.

(*** Split/merge *)
Theorem ainst_split : forall (denv : DEnv) (dsub : DSub) (a1 a2 : A) (da : DA) (dsub' : DSub),
    {denv, dsub }a |= a2 ++ a1 ~> {da, dsub'}
  -> exists (da1 da2 : list dskvar) (dsub1 dsub2 : DSub),
      da = da2 ++ da1
    /\ dsub' = dsub2 ++ dsub1
    /\ {denv, dsub }a |= a1 ~> {da1, dsub1}
    /\ {denv :::a da1, dsub1 ++ dsub }a |= a2 ~> {da2, dsub2}.
Proof.
  introv INST. gen da dsub'. listind a2; intros.
  - exists da. eexists nil. exists dsub'. eexists nil. crush.
  - inverts INST.
    forwards [da__IH1 [da__IH2 [dsub__IH1 [dsub__IH2 ?]]]]: IHa2. eassumption. destr.
    do 4 eexists. splits. 3:{ eassumption. }
    rep_app_assoc. auto. norm. rep_app_assoc. auto.
    constructor; crush. norm*. auto.
Qed.
Ltac AInst_split_destr := forwards [?da [?da [?dsub [?dsub [?EQ__da [?EQ__dsub [?INSTA ?INSTA]]]]]]]: ainst_split.

Theorem AInst_merge : forall (denv__init : DEnv) (da1 da2 : DA) (dsub__init dsub1 dsub2 : DSub) (a1 a2 : A),
    {denv__init, dsub__init}a|= a1 ~> {da1, dsub1}
  -> {denv__init :::a da1, dsub1 ++ dsub__init}a|= a2 ~> {da2, dsub2}
  -> {denv__init, dsub__init}a|= a2 ++ a1 ~> {da2 ++ da1, dsub2 ++ dsub1}.
Proof.
  introv INST1 INST2. AInst_genind INST2. crush.
  norm. econstructor. norm*. assumption. eauto.
Qed.

(*** inv_Ainst *)
Ltac inv_AInst :=
  repeat
    let da1 := fresh "da" in
    let da2 := fresh "da" in
    let dsub1 := fresh "dsub" in
    let dsub2 := fresh "dsub" in
    let EQ__da := fresh "EQ__da" in
    let EQ__dsub := fresh "EQ__dsub" in
    let INSTA1 := fresh "INSTA" in
    let INSTA2 := fresh "INSTA" in
    match goal with
    (*AInst*)
    | [ H : AInst _ _ nil _ _ |- _ ] => inverts H
    | [ H : AInst _ _ (_::_) _ _ |- _ ] => inverts H
    | [ H : AInst _ _ ([_] ++ _) _ _ |- _ ] => inverts H
    | [ H : AInst _ _ (Env_Empty _) _ _ |- _ ] => inverts H
    | [ H : AInst _ _ • _ _ |- _ ] => inverts H
    | [ H : AInst _ _ (Env_Skol _ _) _ _ |- _ ] => inverts H
    | [ H : AInst _ _ (Env_A _ _) _ _ |- _ ] => inverts H
    | [ H : AInst _ _ (Env_Var _ _ _) _ _ |- _ ] => inverts H
    | [ H : AInst _ _ (Env_Obj _ _) _ _ |- _ ] => inverts H
    | [ H : AInst _ _ <_>a _ _ |- _ ] => inverts H
    | [ H : AInst _ _ (_ ++ _) _ _ |- _ ] => apply ainst_split in H; destruct H as [da1 [da2 [dsub1 [dsub2 [EQ__da [EQ__dsub [INSTA1 INSTA2]]]]]]]; subst
  end.

(*** Rewriting *)
Theorem AInst_swap_subinit : forall (denv__init : DEnv) (da : DA) (dsub__init dsub__init' dsub : DSub) (a : A),
    {denv__init, dsub__init }a|= a ~> {da, dsub}
  -> {denv__init, dsub__init'}a|= a ~> {da, dsub}.
Proof.
  introv INST. AInst_genind INST. crush.
  constructor. norm*. auto. auto.
Qed.

Theorem AInst_init_DEnv_sub : forall denv1 denv2 dsub__init a da dsub,
    {denv1, dsub__init}a |= a ~> {da, dsub}
  -> denv1 [<=]de denv2
  -> {denv2, dsub__init}a |= a ~> {da, dsub}.
Proof.
  introv INST SUB. induction INST. auto.
  constructor; eauto.
Qed.

Theorem AInst_init_DEnv_sub' : forall denv1 denv2 dsub__init dsub__init' a da dsub,
    {denv1, dsub__init }a |= a ~> {da, dsub}
  -> denv1 [<=]de denv2
  -> {denv2, dsub__init'}a |= a ~> {da, dsub}.
Proof. intros. eapply AInst_init_DEnv_sub. eapply AInst_swap_subinit. eassumption. eassumption. Qed.

(*** Making *)

Theorem AInst_trivial : forall (denv__in : DEnv) (dsub__in : DSub) (a : A),
    exists dsub,
    {denv__in, dsub__in}a |= a ~> {[], dsub}.
Proof.
  introv. listind a. exists ([]:DSub). auto.
  destruct IHa as [dsub INSTA]. exists ((exA, DT_Unit) :: dsub).
  applys_eq AInstCons. instantiate (1 := []). crush. auto. auto.
Qed.

Theorem AInst_trivial' : forall (denv__in : DEnv) (dsub__in : DSub) (a : A),
    exists dsub,
    a = DSub_to_A dsub
  /\ {denv__in, dsub__in}a |= a ~> {[], dsub}.
Proof.
  introv. listind a. exists ([]:DSub). split; auto.
  destruct IHa as [dsub INSTA]. exists ((exA, DT_Unit) :: dsub). destr.
  split. simpl. rewr. reflexivity. applys_eq AInstCons. instantiate (1 := []). crush. auto. auto.
Qed.

Lemma AInst_DSub_wf : forall denv dsub dsub__init,
    DSub_wf denv dsub
  -> {denv, dsub__init}a|= DSub_to_A dsub ~> {[], dsub}.
Proof.
  introv WF. induction dsub. auto. destruct a. simpl.
  applys_eq AInstCons. instnil. crush.
  applys WfDTy_DEnv_sub denv. apply WF. rewr. fsetdec'. crush. eauto.
Qed.

Theorem AInst_NN_create : forall denv__in dsub__in a da,
    NonNil a
  -> exists dsub, {denv__in, dsub__in}a |= a ~> {da, dsub}.
Proof.
  intros. destruct a. unfold NonNil in H. crush.
  forwards: AInst_trivial a. destr.
  exists. applys_eq AInstCons. 3:eassumption. crush. auto.
Qed.

Theorem AInst_NN_extend' : forall denv__in dsub__in a1 da1 da2 dsub1,
    {denv__in, dsub__in}a |= a1 ~> {da1, dsub1}
  -> NonNil a1
  -> {denv__in, dsub__in}a |= a1 ~> {da2 ++ da1, dsub1}.
Proof.
  introv INST NN. destruct a1. unfold NonNil in NN. contradiction.
  inv_AInst. rewrite app_assoc. constructor. 2:assumption. rewr. eauto.
Qed.
(*** Unsorted *)
Lemma ainst_locate_exa_helper : forall a1 a2 exA dsub,
    DSub_to_A dsub = a2 ++ [exA] ++ a1
  -> exists DSub1 dty DSub2,
      dsub = DSub2 ++ [(exA, dty)] ++ DSub1.
Proof.
  introv EQ. gen dsub. induction a2; intros.
  - destruct dsub; crush.
    do 2 eexists. exists (nil : DSub). crush.
  - destruct dsub; crush.
    forwards: IHa2. eauto. destr.
    do 2 eexists. exists ((a, b) :: DSub2). reflexivity.
Qed.

Theorem ainst_locate_exa : forall (denv__in : DEnv) (dsub__in : DSub) (a1 a2 : A) (exA : exvar) (da : DA) (dsub : DSub),
    {denv__in, dsub__in}a|= a2 ++ [exA] ++ a1 ~> {da, dsub}
  -> exists dsub1 dty dsub2,
      dsub = dsub2 ++ [(exA, dty)] ++ dsub1.
Proof.
  intros. forwards: AInst_props__base. eassumption. destr.
  eauto using ainst_locate_exa_helper.
Qed.

