(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.
Require Import Defs.Defs.

(*** Definition *)
Fixpoint DEnv_skvar_list (denv : DEnv) : list dskvar :=
  match denv with
  | DEnv_Empty              => []
  | (DEnv_DSkol denv' dskA) => dskA :: DEnv_skvar_list denv'
  | (DEnv_DVar  denv' _ _ ) =>        DEnv_skvar_list denv'
  | (DEnv_DObj  denv' _   ) =>        DEnv_skvar_list denv'
end.

Fixpoint DEnv_varbindings_list (denv : DEnv) : list (dskvar * DSch) :=
  match denv with
  | DEnv_Empty              => []
  | (DEnv_DSkol denv' _     ) =>             DEnv_varbindings_list denv'
  | (DEnv_DVar  denv' x dsch) => (x, dsch) :: DEnv_varbindings_list denv'
  | (DEnv_DObj  denv' _     ) =>             DEnv_varbindings_list denv'
end.

Fixpoint DEnv_varbindings_list_subsump (denv : DEnv) (subs sups : list (dskvar * DSch)) : Prop :=
  match subs, sups with
  | [], [] => True
  | _ , [] => False
  | [], _  => False
  | ((x, sub) :: subs'), ((y, sup) :: sups') => DEnv_varbindings_list_subsump denv subs' sups' /\ SubSump denv sub sup /\ x = y
end.

Definition DEnvComplRel (denv1 denv2 : DEnv) : Prop :=
    DEnv_skvar_list denv1 = DEnv_skvar_list denv2
  /\ DEnv_varbindings_list_subsump denv1 (DEnv_varbindings_list denv1) (DEnv_varbindings_list denv2).

Notation "A ≦ B" := (DEnvComplRel A B) (at level 65, format "A  ≦  B").

Theorem DEnv_skvar_list_DEnv_sub : forall (denv1 denv2 : DEnv),
    DEnv_skvar_list denv1 = DEnv_skvar_list denv2
  -> denv1 [=]de denv2.
Proof.
  introv EQ. gen denv2. induction denv1; intros.
  - induction denv2.
    + crush.
    + crush.
    + rewr_derel. crush.
    + rewr_derel. crush.
  - induction denv2; simpl in EQ; try inverts EQ.
    + rewr_derel. forwards: IHdenv1. eassumption.
      unfold DEnv_eq in H. fsetdec.
    + rewr_derel. forwards: IHdenv2. eassumption.
      unfold DEnv_eq in H. rewr_derel in H. fsetdec.
    + rewr_derel. forwards: IHdenv2. eassumption.
      unfold DEnv_eq in H. rewr_derel in H. fsetdec.
 - simpl in EQ. forwards: IHdenv1. eassumption. rewrite H. rewr_derel. reflexivity.
 - simpl in EQ. forwards: IHdenv1. eassumption. rewrite H. rewr_derel. reflexivity.
Qed.
#[export] Hint Resolve DEnv_skvar_list_DEnv_sub : core.

(** Conversions *)
Theorem DEnvComplRel_DEnv_eq : forall (denv1 denv2 : DEnv),
    denv1 ≦ denv2
  -> denv1 [=]de denv2.
Proof. introv SUB. unfold DEnvComplRel in SUB. jauto. Qed.
#[export] Hint Resolve DEnvComplRel_DEnv_eq : core.

Theorem DSchSI_in_DEnv_varbindings_list_In : forall denv dsch x,
    DSchPSI.In (x, dsch) (DEnv_bindings denv) <-> In (x, dsch) (DEnv_varbindings_list denv).
Proof.
  intros. induction denv.
  - split; intros. rewr in H. crush. simpl in H. crush.
  - split; intros. rewr in H. crush. simpl in H. crush.
  - split; intros. rewr in H. indestr. apply IHdenv in H. right. auto. crush.
    simpl in H. destr. crush. crush.
  - split; intros. rewr in H. crush. simpl in H. crush.
Qed.

(*** DEnv_skvar_list *)
Lemma DEnv_skvar_list_extend_app : forall (denv1 denv2 denv : DEnv),
    DEnv_skvar_list  denv1            = DEnv_skvar_list  denv2
  -> DEnv_skvar_list (denv1 ++++ denv) = DEnv_skvar_list (denv2 ++++ denv).
Proof. intros. induction denv; crush. Qed.
#[export] Hint Rewrite DEnv_skvar_list_extend_app : core.

Theorem DEnv_skvar_list_app : forall denv1 denv2,
    DEnv_skvar_list (denv1 ++++ denv2) = DEnv_skvar_list denv2 ++ DEnv_skvar_list denv1.
Proof. intros. induction denv2; crush. Qed.
#[export] Hint Rewrite DEnv_skvar_list_app : core.

(*** DEnv_varbindings_list *)
Theorem DEnv_varbindings_list_app : forall denv1 denv2,
    DEnv_varbindings_list (denv1 ++++ denv2) = DEnv_varbindings_list denv2 ++ DEnv_varbindings_list denv1.
Proof. intros. induction denv2; crush. Qed.
#[export] Hint Rewrite DEnv_varbindings_list_app : core.

Theorem DEnv_varbindings_list_oneDA : forall da,
    DEnv_varbindings_list (oneDA da) = [].
Proof. intros. induction da; crush. Qed.
#[export] Hint Rewrite DEnv_varbindings_list_oneDA : core.

Theorem DEnv_varbindings_list_subsump_DEnv_sub : forall denv1 denv2 sups subs,
    DEnv_varbindings_list_subsump denv1 subs sups
  -> denv1 [<=]de denv2
  -> DEnv_varbindings_list_subsump denv2 subs sups.
Proof.
  introv SS SUB. gen sups. induction subs; intros.
  - destruct sups. auto. inverts SS.
  - destruct sups. simpl in SS. tauto.
    destruct a. destruct p.
    simpl in SS. inverts SS. destr.
    simpl. splits. eauto. rewrite <- SUB. eassumption. tauto.
Qed.
#[export] Hint Resolve DEnv_varbindings_list_subsump_DEnv_sub : core.

Theorem DEnv_varbindings_list_subump_lookup : forall denv subs sups x dsch__sup,
    DEnv_varbindings_list_subsump denv subs sups
  -> In (x, dsch__sup) sups
  -> exists dsch__sub,
      In (x, dsch__sub) subs
    /\ SubSump denv dsch__sub dsch__sup.
Proof.
  introv SS IN. gen subs. induction sups; intros; simpl in IN. inverts IN.
  destruct subs. inverts SS. destruct p. destruct a. destruct IN.
  simpl in SS. destr. exists. splits. simpl. left. auto. auto.
  simpl in SS. destr. forwards: IHsups. eassumption. eassumption. destr.
  exists. split. right. eassumption. eassumption.
Qed.

(*** DEnvComplRel *)
Theorem DEnvComplRel_lookup : forall denv__sub denv__sup dsch__sup x,
    denv__sub ≦ denv__sup
  -> DSchPSI.In (x, dsch__sup) (DEnv_bindings denv__sup)
  -> exists dsch__sub,
    DSchPSI.In (x, dsch__sub) (DEnv_bindings denv__sub)
  /\ SubSump denv__sub dsch__sub dsch__sup.
Proof.
  intros. unfold DEnvComplRel in *. destr.
  apply DSchSI_in_DEnv_varbindings_list_In in H0.
  forwards: DEnv_varbindings_list_subump_lookup. eassumption. eassumption.
  destr. exists. split. eapply DSchSI_in_DEnv_varbindings_list_In. eassumption. eassumption.
Qed.

Lemma DEnv_varbindings_list_subsump_add_obj : forall denv denv1 denv1' xs dobj,
    DEnv_varbindings_list_subsump denv (DEnv_varbindings_list (denv1           ++++ denv1')) xs
  -> DEnv_varbindings_list_subsump denv (DEnv_varbindings_list (denv1 :::o dobj ++++ denv1')) xs.
Proof.
  introv SS. gen xs. induction denv1'; intros.
  - simpl in *. assumption.
  - simpl in *. eauto.
  - destruct xs. simpl in SS. crush.
    destruct p. simpl in *. destr. splits; eauto.
  - simpl in *. eauto.
Qed.


(*** Rewrites *)
Theorem DEnvComplRel_swap_l : forall denv1 denv2 da x dsch,
    denv1 :::a da :::x x :- dsch ≦ denv2
  -> denv1 :::x x :- dsch :::a da ≦ denv2.
Proof.
  introv SUB. unfold DEnvComplRel in *. simpl in *. destr. split.
  norm. norm in H. eassumption. norm*.
  simpl. rewr. destruct (DEnv_varbindings_list denv2). contradiction.
  destruct p. destr.
  assert ((denv1 ++++ <da>da ++++ <d :- dsch>dx) [=]de (denv1 :::x d :- dsch ++++ <da>da)).
  rewr_derel. fsetdec.
  splits; eauto.
Qed.

(*** Creating *)
Lemma DEnvComplRel__genhelper : forall (denv1 denv2 : DEnv) (da : DA),
    denv1 ≦ denv2
  -> denv1 :::a da ≦ denv2 :::a da.
Proof.
  introv SUB. unfold DEnvComplRel in *. destr. split.
  - do 2 rewrite DEnv_cons_a_one. auto using DEnv_skvar_list_extend_app.
  - norm. eauto.
Qed.

Theorem DEnvComplRel__consvar : forall denv1 denv2 dsch1 dsch2 x,
    denv1 ≦ denv2
  -> SubSump (denv1 :::x x :- dsch1) dsch1 dsch2
  -> denv1 :::x x :- dsch1 ≦ denv2 :::x x :- dsch2.
Proof.
  introv SUB SS. unfold DEnvComplRel in *. destr. split.
  - clear H0. simpl. eassumption.
  - clear H. simpl. splits.
    + eapply DEnv_varbindings_list_subsump_DEnv_sub. eassumption. crush.
    + assumption.
    + tauto.
Qed.

Lemma DEnvComplRel__lethelper : forall (denv1 denv2 : DEnv) (dsch__sub dsch__sup : DSch)  (da : list dskvar) (x : termvar),
    denv1 :::a da ≦ denv2
  -> SubSump (denv1 :::a da) dsch__sub dsch__sup
  -> (denv1 :::x x :- dsch__sub) :::a da ≦ denv2 :::x x :- dsch__sup.
Proof.
  introv SUB SS. apply DEnvComplRel_swap_l. apply DEnvComplRel__consvar. eassumption. eauto.
Qed.

Lemma DEnvComplRel__apphelper : forall (denv1 denv1' denv2 : DEnv) (dobj : DObj),
    denv1           ++++ denv1' ≦ denv2
  -> denv1 :::o dobj ++++ denv1' ≦ denv2.
Proof.
  introv SUB. unfold DEnvComplRel in *. destr. split. rewr. simpl. rewr in H. simpl in H. assumption.
  apply DEnv_varbindings_list_subsump_add_obj. eapply DEnv_varbindings_list_subsump_DEnv_sub. eassumption. crush.
Qed.

(*** Unsorted *)
Theorem  DFra_DEnv_sup_rem : forall denv1 denv2 da,
    denv1 ≦ denv2
  -> DFrA da denv2
  -> DFrA da denv1.
Proof.
  introv SUB DFR. unfold DEnvComplRel in SUB. destr.
  apply DFrA_props. apply DFrA_props in DFR. destr. split. 2:assumption.
  eapply disj_subset_proper. 3:eassumption. crush. rewr.
  assert (denv1 [=]de denv2). auto. crush.
Qed.
