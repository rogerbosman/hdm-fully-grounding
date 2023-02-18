
(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Defs.DEnv.
Require Import Defs.DFra.
Require Import Defs.List.
Require Import Defs.Set.
Require Import Defs.Substs.

Require Import Defs.WfDEnv.
Require Import Defs.WfDTy.

(*** Notation, tactics etc*)
Notation  "A |=m B ▸ C" := (TmMon A B C) (at level 50, format "A  |=m  B  ▸  C " ) : type_scope.
Notation  "A |=p B ▸ C" := (TmDGen A B C) (at level 50, format "A  |=p  B  ▸  C " ) : type_scope.

Scheme Mon_mut := Induction for TmMon Sort Prop
  with DGen_mut := Induction for TmDGen Sort Prop.
Combined Scheme Mon_DGen_mut
         from Mon_mut, DGen_mut.

(*** Weakening *)
Definition Mon_DEnv_x_sub__def := forall (denv1 : DEnv) (e : e) (dty : DTy) (denv2 : DEnv),
    denv1 |=m e ▸ dty
  -> denv1 [<=]dex denv2
  -> denv2 |=m e ▸ dty.
Definition Mon_DEnv_x_sub__prop (denv1 : DEnv) (e : e) (dty : DTy)
                                  (MON : denv1 |=m e ▸ dty) : Prop := forall (denv2 : DEnv),
    denv1 [<=]dex denv2
  -> denv2 |=m e ▸ dty.
#[local] Hint Unfold Mon_DEnv_x_sub__def Mon_DEnv_x_sub__prop : core.

Definition DGen_DEnv_x_sub__def := forall (denv1 : DEnv) (e : e) (dsch : DSch) (denv2 : DEnv),
    denv1 |=p e ▸ dsch
  -> denv1 [<=]dex denv2
  -> denv2 |=p e ▸ dsch.
Definition DGen_DEnv_x_sub__prop (denv1 : DEnv) (e : e) (dsch : DSch)
                                   (DGEn : denv1 |=p e ▸ dsch) : Prop := forall (denv2 : DEnv),
    denv1 [<=]dex denv2
  -> denv2 |=p e ▸ dsch.
#[local] Hint Unfold DGen_DEnv_x_sub__def DGen_DEnv_x_sub__prop : core.

Theorem supdenv_weaken_subsump : forall (denv1 denv2 : DEnv) (dsch1 dsch2 : DSch),
    SubSump denv1 dsch1 dsch2
  -> denv1 [<=]de denv2
  -> SubSump denv2 dsch1 dsch2.
Proof.
  introv SS SUP. gen denv2. induction SS; crush.
  - econstructor. intros. eapply H. eassumption. crush.
  - econstructor. 2:eauto. eauto.
Qed.

Theorem generalize_DSch_app : forall da1 da2 sch,
    generalize_DSch sch (da2 ++ da1) = generalize_DSch (generalize_DSch sch da1) da2.
Proof. induction da2; crush. Qed.

Theorem subst_dskvar_DSch_DSchPSI_In : forall x dsch denv dty skA,
    DSchPSI.In (x,                           dsch) (DEnv_bindings                            denv )
  -> DSchPSI.In (x, subst_dskvar_DSch dty skA dsch) (DEnv_bindings (subst_dskvar_DEnv dty skA denv)).
Proof.
  introv IN. induction denv. 1,2,4:crush.
  rewr in IN. indestr; crush.
Qed.

Theorem subst_dskvar_DEnv_app : forall dty__in skA denv1 denv2,
    subst_dskvar_DEnv dty__in skA (denv1 ++++ denv2) = subst_dskvar_DEnv dty__in skA denv1 ++++ subst_dskvar_DEnv dty__in skA denv2.
Proof. intros. induction denv2; crush. Qed.
#[export] Hint Rewrite subst_dskvar_DEnv_app : core.

Theorem DEnv_dskvars_subst_dskvar_DEnv : forall dty skA denv,
    DEnv_dskvars (subst_dskvar_DEnv dty skA denv) [=] DEnv_dskvars denv.
Proof. introv. induction denv; crush. Qed.
#[export] Hint Rewrite DEnv_dskvars_subst_dskvar_DEnv : core.

(* Theorem subst_dskA_dskA_SubSump : forall dskA__in dskA__out denv dsch dty, *)
(*     SubSump denv dsch (DS_Mono dty) *)
(*   (* -> dskA \notin dskA__in *) *)
(*   -> SubSump (subst_dskvar_DEnv dskA__in dskA__out denv) (subst_dskvar_DSch (DT_SkVar_f dskA__in) dskA__out dsch) (DS_Mono (subst_dskvar_DTy (DT_SkVar_f dskA__in) dskA__out dty)). *)
(* Proof. *)
(* About SubSump_ind. *)
(*   introv SS. dependent induction SS. *)
(*   - crush. *)
(*   - simpl. applys SubSumpInst (L \u singleton dskA__in \u singleton dskA__out). eapply subst_dskA_dskA_WfDTy_mono. eassumption. intros. *)
(*     remember (subst_dskvar_DEnv dskA__in dskA__out DEnv5) as denv. *)
(*     forwards: H dskA. fsetdec. reflexivity. *)
(*     remember (DS_Mono (subst_dskvar_DTy (DT_SkVar_f dskA__in) dskA__out dty)) as dty'. *)
(*     asserts_rewrite ( subst_dskvar_DSch (subst_dskvar_DTy (DT_SkVar_f dskA__in) dskA__out DTy1) dskA *)
(*                        (open_DSch_wrt_DTy (subst_dskvar_DSch (DT_SkVar_f dskA__in) dskA__out DSch5) (DT_SkVar_f dskA)) *)
(*                     = subst_dskvar_DSch (DT_SkVar_f dskA__in) dskA__out *)
(*                          (subst_dskvar_DSch DTy1 dskA (open_DSch_wrt_DTy DSch5 (DT_SkVar_f dskA)))). *)
(*     rewrite subst_dskvar_DSch_open_DSch_wrt_DTy. simpl. if_taut. *)
(*     rewrite subst_dskvar_DSch_open_DSch_wrt_DTy. simpl. if_taut. *)
(*     rewrite subst_dskvar_DSch_open_DSch_wrt_DTy. *)
(*     rewrite <- subst_dskvar_DSch_subst_dskvar_DSch. reflexivity. *)
(*     (*side conditions*) *)
(*     simpl. unfold not. intros. rewr in H2. fsetdec. unfold not. intros. fsetdec. auto. eauto. *)
(*     eapply subst_dskvar_DTy_lc_DTy; eauto. *)
(*     eassumption. *)
(* Qed. *)

Theorem subst_dskvar_DEnv_oneDA : forall dty skA da,
    subst_dskvar_DEnv dty skA (oneDA da) = oneDA da.
Proof. intros. induction da; crush. Qed.
#[export] Hint Rewrite subst_dskvar_DEnv_oneDA : core.

Theorem subst_dskvar_DEnv_consDA : forall dty skA da denv,
    subst_dskvar_DEnv dty skA (denv :::a da) = subst_dskvar_DEnv dty skA denv :::a da.
Proof. intros. induction da; crush. Qed.
#[export] Hint Rewrite subst_dskvar_DEnv_consDA : core.

Theorem generalize_DSch_subst_dskvar_DSch : forall dty skA dsch da,
    lc_DTy dty
  -> skA \notin varl da
  -> free_dskvars_DTy dty [><] varl da
  -> generalize_DSch (subst_dskvar_DSch dty skA dsch) da = subst_dskvar_DSch dty skA (generalize_DSch dsch da).
Proof.
  introv LC NID DISJ. induction da. crush. simpl. rewrite IHda.
  rewrite subst_dskvar_DSch_close_DSch_wrt_DTy. reflexivity. eassumption.
  unfold not in *. intros.  apply NID. crush.
  eapply in_disjoint_impl_notin1. eassumption. rewr. fsetdec. rewr in NID. fsetdec.
  rewr in DISJ. eapply disj_subset_proper. 3:eassumption. crush. rewr. crush.
Qed.

Lemma WFDTY_subst_skA : forall denv1 skA denv2 dty skB,
    (denv1 :::s skA ++++ denv2) |=dty DS_Mono dty
  -> subst_dskvar_DEnv (DT_SkVar_f skB) skA (denv1 :::s skB ++++ denv2) |=dty DS_Mono (subst_dskvar_DTy (DT_SkVar_f skB) skA dty).
Proof.
  introv WFDTY.
  eapply WfDTy_props in WFDTY.
  destr. eapply WfDTy_props. split.
  * simpl. norm. rewr.
    rewrite free_dskvars_DTy_subst_dskvar_DTy_upper. simpl.
    rewrite H.
    unfold AtomSetImpl.Subset. intros. indestr. crush. rewr in H1.
    apply remove_iff in H1. destr. indestr. crush. crush. crush.
  * inverts H0. constructor. apply subst_dskvar_DTy_lc_DTy; auto.
Qed.

Theorem SubSump_subst_skA : forall denv1 skA denv2 dsch dty skB,
    SubSump (denv1 :::s skA ++++ denv2) dsch (DS_Mono dty)
  -> SubSump (subst_dskvar_DEnv (DT_SkVar_f skB) skA (denv1 :::s skB ++++ denv2))
      (subst_dskvar_DSch (DT_SkVar_f skB) skA dsch) (DS_Mono (subst_dskvar_DTy (DT_SkVar_f skB) skA dty)).
Proof.
  introv SS. dependent induction SS.
  - clear H H0. crush.
  - applys SubSumpInst
      (L \u free_dskvars_DSch DSch5 \u free_dskvars_DSch (subst_dskvar_DSch (DT_SkVar_f skB) skA DSch5))
      (subst_dskvar_DTy (DT_SkVar_f skB) skA DTy1).
    + eauto using WFDTY_subst_skA.
    + intros. fold subst_dskvar_DSch.
      forwards: H dskA. fsetdec. reflexivity. reflexivity.
      rewrite subst_dskvar_DSch_open_DSch_wrt_DTy in H1. 2:eauto. simpl in H1. if_taut.
      rewrite subst_dskvar_DSch_open_DSch_wrt_DTy. 2:eauto. simpl. if_taut.
      rewrite subst_dskvar_DSch_open_DSch_wrt_DTy in H1.
      rewrite (subst_dskvar_DSch_not_in_DSch_idempotent _ _ dskA) in H1. 2:fsetdec. 2:auto. 2:apply subst_dskvar_DTy_lc_DTy; eauto.
      rewrite subst_dskvar_DSch_not_in_DSch_idempotent. 2:fsetdec.
      assumption.
Qed.

Definition subst_name (x__in x__out x : termvar) : termvar := (if eq_var x x__out then x__in else x).
#[export] Hint Unfold subst_name : core.

Fixpoint subst_name_DEnv (x__in x__out : termvar) (denv:DEnv) : DEnv :=
  match denv with
  | DEnv_Empty              => DEnv_Empty
  | (DEnv_DSkol denv' dskA  ) => DEnv_DSkol (subst_name_DEnv x__in x__out denv') dskA
  | (DEnv_DVar  denv' x dsch) => DEnv_DVar  (subst_name_DEnv x__in x__out denv') (subst_name x__in x__out x) dsch
  | (DEnv_DObj  denv' dobj  ) => DEnv_DObj  (subst_name_DEnv x__in x__out denv') dobj
end.
#[export] Hint Unfold subst_name_DEnv : core.

Definition Mon_rename_binding__def := forall (denv : DEnv) (e : e) (dty : DTy),
    denv |=m e ▸ dty
  -> forall x__in x__out,
    (subst_name_DEnv x__in x__out denv) |=m subst_tm_e (e_Var_f x__in) x__out e ▸ dty.
(* Definition Mon_rename_binding__prop (denv : DEnv) (e : e) (dty : DTy) *)
(*                                   (MON : denv |=m e ▸ dty) : Prop := forall (denv1 : DEnv) (skA : skvar) (denv2 : DEnv), *)
(*     denv = (denv1 :::s skA ++++ denv2) *)
(*   -> exists L, forall skB, *)
(*     skB \notin L *)
(*   -> subst_dskvar_DEnv (DT_SkVar_f skB) skA (denv1 :::s skB ++++ denv2) |=m e ▸ (subst_dskvar_DTy (DT_SkVar_f skB) skA dty). *)
(* #[local] Hint Unfold Mon_rename_binding__def Mon_rename_binding__prop : core. *)

Definition DGen_rename_binding__def := forall (denv : DEnv) (e : e) (dsch : DSch),
    denv |=p e ▸ dsch
  -> forall x__in x__out,
    (subst_name_DEnv x__in x__out denv) |=p subst_tm_e (e_Var_f x__in) x__out e ▸ dsch.
(* Definition DGen_rename_binding__prop (denv : DEnv) (e : e) (dsch : DSch) *)
(*                                    (DGEn : denv |=p e ▸ dsch) : Prop := forall (denv1 : DEnv) (skA : skvar) (denv2 : DEnv), *)
(*     denv = (denv1 :::s skA ++++ denv2) *)
(*   -> exists L, forall skB, *)
(*     skB \notin L *)
(*   -> subst_dskvar_DEnv (DT_SkVar_f skB) skA (denv1 :::s skB ++++ denv2) |=p e ▸ (subst_dskvar_DSch (DT_SkVar_f skB) skA dsch). *)
(* #[local] Hint Unfold DGen_rename_binding__def DGen_rename_binding__prop : core. *)

Theorem subst_name_DEnv_lookup: forall (denv : DEnv) (x__in x__out x : termvar) (dsch : DSch),
    DSchPSI.In (x, dsch) (DEnv_bindings denv)
  -> DSchPSI.In (subst_name x__in x__out x, dsch) (DEnv_bindings (subst_name_DEnv x__in x__out denv)).
Proof.
  introv IN. induction denv.
  - crush.
  - simpl. rewr in IN. rewr. eauto.
  - simpl. rewr in IN. rewr. indestr; eauto.
  - simpl. rewr in IN. rewr. eauto.
Qed.

Theorem SubSump_DEnv_sub : forall denv1 denv2 sch dty,
    SubSump denv1 sch dty
  -> denv1 [=]de denv2
  -> SubSump denv2 sch dty.
Proof.
  intros. gen denv2. induction H; intros. crush. admit.
  econstructor. eapply WfDTy_DEnv_sub. eassumption. eauto. eauto.
Admitted.

Theorem subst_name_DEnv_cons_DA : forall x__in x__out denv da,
    subst_name_DEnv x__in x__out (denv :::a da) = subst_name_DEnv x__in x__out denv :::a da.
Proof. intros. induction da; crush. Qed.

Theorem subst_name_DEnv_DEnv_eq : forall x__in x__out denv,
    subst_name_DEnv x__in x__out denv [=]de denv.
Proof.
  induction denv. 1,2,4:crush.
  rewr_derel. simpl. rewr. eauto.
Qed.

Theorem Mon_DGen_rename_binding : Mon_rename_binding__def /\ DGen_rename_binding__def.
Proof.
  apply Mon_DGen_mut.
  - introv IN SS. intros.
    forwards IN': subst_name_DEnv_lookup x__in x__out. eassumption.
    unfold subst_name in IN'. destruct (x == x__out).
    + simpl. if_taut. intros. econstructor. eassumption.
      eapply SubSump_DEnv_sub. eassumption. auto using subst_name_DEnv_DEnv_eq.
    + simpl. if_taut. intros. econstructor. eassumption.
      eapply SubSump_DEnv_sub. eassumption. auto using subst_name_DEnv_DEnv_eq.

  - intros. simpl. crush.

  - introv NIE INF IH. intros.
    forwards: subst_name_DEnv_DEnv_eq x__in x__out DEnv5.
    simpl. applys TmAbs (L \u singleton x__out). eapply WfDTy_DEnv_sub. eassumption. auto.
    intros y NI__y.
    forwards: IH y x__in x__out. fsetdec.
    assert (y <> x__out). unfold not. intros. apply NI__y. fsetdec.
    asserts_rewrite ( subst_tm_e (e_Var_f x__in) x__out (open_e_wrt_e e5 (e_Var_f y))
                    = open_e_wrt_e (subst_tm_e (e_Var_f x__in) x__out e5) (e_Var_f y)) in H0.
      rewrite subst_tm_e_open_e_wrt_e. simpl. ifdec. contradiction. reflexivity. auto.
    asserts_rewrite (subst_name x__in x__out y = y) in H0.
      unfold subst_name. ifdec. contradiction. reflexivity.
    assumption.

  - introv MON__e1 IH__e1 MON__e2 IH__e2. intros.
    simpl.
   forwards IH1: IH__e1 x__in x__out.
    forwards IH2: IH__e2 x__in x__out.
    eauto.

  - introv GEN IH__gen MON IH__mon. intros.
    forwards: IH__gen.
    simpl. applys TmLet (L \u singleton x__out).
    + eassumption.
    + intros y NI__y. forwards: IH__mon y x__in x__out. fsetdec.
      assert (y <> x__out). unfold not. intros. apply NI__y. fsetdec.
      asserts_rewrite ( subst_tm_e (e_Var_f x__in) x__out (open_e_wrt_e e2 (e_Var_f y))
                      = open_e_wrt_e (subst_tm_e (e_Var_f x__in) x__out e2) (e_Var_f y)) in H0.
        rewrite subst_tm_e_open_e_wrt_e. simpl. ifdec. contradiction. reflexivity. auto.
      asserts_rewrite (subst_name x__in x__out y = y) in H0.
        unfold subst_name. ifdec. contradiction. reflexivity.
      eassumption.

  - introv DFR MON IH__mon GEN. intros.
    forwards: IH__mon x__in x__out.
    applys TmGen DA5.
    eapply DFrA_DEnv_sub. eassumption. eauto using subst_name_DEnv_DEnv_eq.
    rewrite subst_name_DEnv_cons_DA in H.
    eassumption.
    eassumption.
Qed.

Theorem DEnv_boundvars_subst_dskvar_DEnv : forall denv skA dty,
    DEnv_boundvars (subst_dskvar_DEnv dty skA denv) [=] DEnv_boundvars denv.
Proof. induction denv; crush. Qed.
#[export] Hint Rewrite DEnv_boundvars_subst_dskvar_DEnv : core.

Theorem subst_name_DEnv_notin_involuntive : forall (x__out x__in : termvar) (denv : DEnv),
    x__out \notin DEnv_boundvars denv
  -> subst_name_DEnv x__in x__out denv = denv.
Proof.
  induction denv.
  - crush.
  - crush.
  - intros. simpl. unfold subst_name. ifdec; crush.
  - crush.
Qed.

Theorem Mon_rename_binding' : forall y denv x dsch e dty,
    (denv :::x x :- dsch) |=m e ▸ dty
  -> x \notin (DEnv_boundvars denv)
  -> (denv :::x y :- dsch) |=m subst_tm_e (e_Var_f y) x e ▸ dty.
Proof.
  introv MON NIE. destruct (x == y).
  - subst.
    asserts_rewrite (subst_tm_e (e_Var_f y) y e = e). rewrite subst_tm_e_spec. crush.
    assumption.
  - forwards: proj1 Mon_DGen_rename_binding. unfold Mon_rename_binding__def in H. forwards: H y x. eassumption.
    simpl in H0. unfold subst_name in H0. if_taut.
    forwards REWR1: subst_name_DEnv_notin_involuntive x denv.  fsetdec. rewrite REWR1 in H0.
    assumption.
Qed.


(*** New Mon_DEnv_subst_skA *)
(* Definition Mon_DEnv_subst_skA__def := forall (denv1 : DEnv) (denv2 : DEnv) (e : e) (dty : DTy) (skA : skvar), *)
(*     (denv1 :::s skA ++++ denv2) |=m e ▸ dty *)
(*   -> exists L, forall skB, *)
(*     skB \notin L *)
(*   -> (denv1 :::s skA ++++ (subst_dskvar_DEnv (DT_SkVar_f skB) skA denv2)) |=m e ▸ (subst_dskvar_DTy (DT_SkVar_f skB) skA dty). *)
(* Definition Mon_DEnv_subst_skA__prop (denv : DEnv) (e : e) (dty : DTy) *)
(*                                   (MON : denv |=m e ▸ dty) : Prop := forall (denv1 : DEnv) (skA : skvar) (denv2 : DEnv), *)
(*     denv = (denv1 :::s skA ++++ denv2) *)
(*   -> exists L, forall skB, *)
(*     skB \notin L *)
(*   -> (denv1 :::s skA ++++ (subst_dskvar_DEnv (DT_SkVar_f skB) skA denv2)) |=m e ▸ (subst_dskvar_DTy (DT_SkVar_f skB) skA dty). *)
(* #[local] Hint Unfold Mon_DEnv_subst_skA__def Mon_DEnv_subst_skA__prop : core. *)

(* Definition DGen_DEnv_subst_skA__def := forall (denv1 : DEnv) (skA : skvar) (denv2 : DEnv) (e : e) (dsch : DSch) (denv2 : DEnv), *)
(*     (denv1 :::s skA ++++ denv2) |=p e ▸ dsch *)
(*   -> exists L, forall skB, *)
(*     skB \notin L *)
(*   -> (denv1 :::s skB ++++ (subst_dskvar_DEnv (DT_SkVar_f skB) skA denv2)) |=p e ▸ (subst_dskvar_DSch (DT_SkVar_f skB) skA dsch). *)
(* Definition DGen_DEnv_subst_skA__prop (denv : DEnv) (e : e) (dsch : DSch) *)
(*                                    (DGEn : denv |=p e ▸ dsch) : Prop := forall (denv1 : DEnv) (skA : skvar) (denv2 : DEnv), *)
(*     denv = (denv1 :::s skA ++++ denv2) *)
(*   -> exists L, forall skB, *)
(*     skB \notin L *)
(*   -> (denv1 :::s skB ++++ (subst_dskvar_DEnv (DT_SkVar_f skB) skA denv2)) |=p e ▸ (subst_dskvar_DSch (DT_SkVar_f skB) skA dsch). *)
(* #[local] Hint Unfold DGen_DEnv_subst_skA__def DGen_DEnv_subst_skA__prop : core. *)

(* Theorem Mon_DGen_DEnv_subst_skA : Mon_DEnv_subst_skA__def /\ DGen_DEnv_subst_skA__def. *)
(* Proof. *)
(*   forwards: (Mon_DGen_mut Mon_DEnv_subst_skA__prop DGen_DEnv_subst_skA__prop) *)
(*   ; unfold Mon_DEnv_subst_skA__prop in *; unfold DGen_DEnv_subst_skA__prop in *. *)
(*   7:{ jauto. } *)
(*   - introv IN SS EQ. subst. *)
(*     exists empty. introv NIL. *)
(*     (**) *)
(*     applys TmVar (subst_dskvar_DSch (DT_SkVar_f skB) skA DSch5). *)
(* Admitted. *)
(*     eapply subst_dskvar_DSch_DSchPSI_In. rewr. rewr in IN. eassumption. *)
(*     eauto using SubSump_subst_skA. *)
(*   - introv _ EQ. subst. *)
(*     exists empty. introv NIL. *)
(*     crush. *)
(*   - introv WFDTY MON IH EQ. subst. *)
(*     forwards [y NIL__y]: atom_fresh (L \u union (DEnv_boundvars denv1) (DEnv_boundvars denv2) \u free_xs_e e5). *)
(*     forwards [L' IH']: IH y denv1 skA (denv2 :::x y :- DS_Mono DTy1). fsetdec. reflexivity. *)
(*     exists L'. introv NIL. *)
(*     (**) *)
(*     applys TmAbs empty. *)
(*     + fold subst_dskvar_DTy. *)
(*       eauto using WFDTY_subst_skA. *)
(*     + fold subst_dskvar_DTy. *)
(*       intros x NIL__x. *)
(*       forwards: IH' skB. eassumption. *)
(*       forwards: Mon_rename_binding' x. apply H. rewr. fsetdec. *)
(*       rewrite subst_tm_e_open_e_wrt_e in H0. simpl in H0. if_taut. *)
(*       asserts_rewrite (subst_tm_e (e_Var_f x) y e5 = e5) in H0. crush. eassumption. auto. *)
(*   - introv MON__fun IH__fun MON__arg IH__arg EQ. subst. *)
(*     forwards [L__fun IH__fun']: IH__fun denv1 skA denv2. reflexivity. *)
(*     forwards [L__arg IH__arg']: IH__arg denv1 skA denv2. reflexivity. *)
(*     (**) *)
(*     exists (L__fun \u L__arg). introv NIL. *)
(*     forwards: IH__fun' skB. fsetdec. *)
(*     forwards: IH__arg' skB. fsetdec. *)
(*     eauto. *)
(*   - introv POL IH__pol MON IH__mon EQ. subst. *)
(*     forwards [y NIL__y]: atom_fresh (L \u union (DEnv_boundvars denv1) (DEnv_boundvars denv2) \u free_xs_e e2). *)
(*     forwards [L__pol IH__pol']: IH__pol denv1 skA denv2. reflexivity. *)
(*     forwards [L__mon IH__mon']: IH__mon y denv1 skA (denv2 :::x y :- DSch5). fsetdec. reflexivity. *)
(*     (**) *)
(*     exists (L__pol \u L__mon). introv NIL. *)
(*     forwards POL': IH__pol' skB. fsetdec. *)
(*     forwards MON': IH__mon' skB. fsetdec. *)
(*     applys TmLet empty. eassumption. intros x NIL__x. *)
(*     forwards: Mon_rename_binding' x. apply MON'. rewr. fsetdec. *)
(*     rewrite subst_tm_e_open_e_wrt_e in H. simpl in H. if_taut. *)
(*     asserts_rewrite (subst_tm_e (e_Var_f x) y e2 = e2) in H. crush. eassumption. auto. *)
(*   - introv DFR MON IH GEN EQ. subst. *)
(*     forwards [L IH']: IH denv1 skA (denv2 :::a DA5). norm. reflexivity. *)
(*     (**) *)
(*     exists (L \u varl DA5). introv NIL. *)
(*     forwards MON': IH' skB. fsetdec. *)
(*     applys TmGen DA5. eapply DFrA_subst_skA. eassumption. fsetdec. *)
(*     rewr. rewr in MON'. eassumption. *)
(*     rewrite <- generalize_DSch_subst_dskvar_DSch. reflexivity. auto. *)
(*     apply DFrA_props in DFR. destr. *)
(*     unfold not. intros. applys in_disjoint_impl skA. apply H. eassumption. rewr. fsetdec. *)
(*     simpl. unfold AtomSetImpl.disjoint. fsetdec. *)
(* Qed. *)

(*** Old Mon_DEnv_subst_skA *)

Definition Mon_DEnv_subst_skA__def := forall (denv1 : DEnv) (denv2 : DEnv) (e : e) (dty : DTy) (skA : skvar),
    (denv1 :::s skA ++++ denv2) |=m e ▸ dty
  -> exists L, forall skB,
    skB \notin L
  -> subst_dskvar_DEnv (DT_SkVar_f skB) skA (denv1 :::s skB ++++ denv2) |=m e ▸ (subst_dskvar_DTy (DT_SkVar_f skB) skA dty).
Definition Mon_DEnv_subst_skA__prop (denv : DEnv) (e : e) (dty : DTy)
                                  (MON : denv |=m e ▸ dty) : Prop := forall (denv1 : DEnv) (skA : skvar) (denv2 : DEnv),
    denv = (denv1 :::s skA ++++ denv2)
  -> exists L, forall skB,
    skB \notin L
  -> subst_dskvar_DEnv (DT_SkVar_f skB) skA (denv1 :::s skB ++++ denv2) |=m e ▸ (subst_dskvar_DTy (DT_SkVar_f skB) skA dty).
#[local] Hint Unfold Mon_DEnv_subst_skA__def Mon_DEnv_subst_skA__prop : core.

Definition DGen_DEnv_subst_skA__def := forall (denv1 : DEnv) (skA : skvar) (denv2 : DEnv) (e : e) (dsch : DSch) (denv2 : DEnv),
    (denv1 :::s skA ++++ denv2) |=p e ▸ dsch
  -> exists L, forall skB,
    skB \notin L
  -> subst_dskvar_DEnv (DT_SkVar_f skB) skA (denv1 :::s skB ++++ denv2) |=p e ▸ (subst_dskvar_DSch (DT_SkVar_f skB) skA dsch).
Definition DGen_DEnv_subst_skA__prop (denv : DEnv) (e : e) (dsch : DSch)
                                   (DGEn : denv |=p e ▸ dsch) : Prop := forall (denv1 : DEnv) (skA : skvar) (denv2 : DEnv),
    denv = (denv1 :::s skA ++++ denv2)
  -> exists L, forall skB,
    skB \notin L
  -> subst_dskvar_DEnv (DT_SkVar_f skB) skA (denv1 :::s skB ++++ denv2) |=p e ▸ (subst_dskvar_DSch (DT_SkVar_f skB) skA dsch).
#[local] Hint Unfold DGen_DEnv_subst_skA__def DGen_DEnv_subst_skA__prop : core.

Theorem DFrA_subst_skA : forall da denv1 denv2 skA skB,
    DFrA da (denv1 :::s skA ++++ denv2)
  -> skB \notin varl da
  -> DFrA da (subst_dskvar_DEnv (DT_SkVar_f skB) skA (denv1 :::s skB ++++ denv2)).
Proof.
  introv DFR NID. induction da. crush.
  inverts DFR. rewr in NID. constructor. eauto.
  rewr_derel. rewr_derel in DFR0. fsetdec.
Qed.

Theorem Mon_DGen_DEnv_subst_skA : Mon_DEnv_subst_skA__def /\ DGen_DEnv_subst_skA__def.
Proof.
  forwards: (Mon_DGen_mut Mon_DEnv_subst_skA__prop DGen_DEnv_subst_skA__prop)
  ; unfold Mon_DEnv_subst_skA__prop in *; unfold DGen_DEnv_subst_skA__prop in *.
  7:{ jauto. }
  - introv IN SS EQ. subst.
    exists empty. introv NIL.
    (**)
    applys TmVar (subst_dskvar_DSch (DT_SkVar_f skB) skA DSch5).
    eapply subst_dskvar_DSch_DSchPSI_In. rewr. rewr in IN. eassumption.
    eauto using SubSump_subst_skA.
  - introv _ EQ. subst.
    exists empty. introv NIL.
    crush.
  - introv WFDTY MON IH EQ. subst.
    forwards [y NIL__y]: atom_fresh (L \u union (DEnv_boundvars denv1) (DEnv_boundvars denv2) \u free_xs_e e5).
    forwards [L' IH']: IH y denv1 skA (denv2 :::x y :- DS_Mono DTy1). fsetdec. reflexivity.
    exists L'. introv NIL.
    (**)
    applys TmAbs empty.
    + fold subst_dskvar_DTy.
      eauto using WFDTY_subst_skA.
    + fold subst_dskvar_DTy.
      intros x NIL__x.
      forwards: IH' skB. eassumption.
      forwards: Mon_rename_binding' x. apply H. rewr. fsetdec.
      rewrite subst_tm_e_open_e_wrt_e in H0. simpl in H0. if_taut.
      asserts_rewrite (subst_tm_e (e_Var_f x) y e5 = e5) in H0. crush. eassumption. auto.
  - introv MON__fun IH__fun MON__arg IH__arg EQ. subst.
    forwards [L__fun IH__fun']: IH__fun denv1 skA denv2. reflexivity.
    forwards [L__arg IH__arg']: IH__arg denv1 skA denv2. reflexivity.
    (**)
    exists (L__fun \u L__arg). introv NIL.
    forwards: IH__fun' skB. fsetdec.
    forwards: IH__arg' skB. fsetdec.
    eauto.
  - introv POL IH__pol MON IH__mon EQ. subst.
    forwards [y NIL__y]: atom_fresh (L \u union (DEnv_boundvars denv1) (DEnv_boundvars denv2) \u free_xs_e e2).
    forwards [L__pol IH__pol']: IH__pol denv1 skA denv2. reflexivity.
    forwards [L__mon IH__mon']: IH__mon y denv1 skA (denv2 :::x y :- DSch5). fsetdec. reflexivity.
    (**)
    exists (L__pol \u L__mon). introv NIL.
    forwards POL': IH__pol' skB. fsetdec.
    forwards MON': IH__mon' skB. fsetdec.
    applys TmLet empty. eassumption. intros x NIL__x.
    forwards: Mon_rename_binding' x. apply MON'. rewr. fsetdec.
    rewrite subst_tm_e_open_e_wrt_e in H. simpl in H. if_taut.
    asserts_rewrite (subst_tm_e (e_Var_f x) y e2 = e2) in H. crush. eassumption. auto.
  - introv DFR MON IH GEN EQ. subst.
    forwards [L IH']: IH denv1 skA (denv2 :::a DA5). norm. reflexivity.
    (**)
    exists (L \u varl DA5). introv NIL.
    forwards MON': IH' skB. fsetdec.
    applys TmGen DA5. eapply DFrA_subst_skA. eassumption. fsetdec.
    rewr. rewr in MON'. eassumption.
    rewrite <- generalize_DSch_subst_dskvar_DSch. reflexivity. auto.
    apply DFrA_props in DFR. destr.
    unfold not. intros. applys in_disjoint_impl skA. apply H. eassumption. rewr. fsetdec.
    simpl. unfold AtomSetImpl.disjoint. fsetdec.
Qed.

Theorem subst_dskvar_DEnv_not_in_DEnv : forall denv skA dty,
    wfd(denv)
  -> skA `notin` DEnv_dskvars denv
  -> subst_dskvar_DEnv dty skA denv = denv.
Proof.
  introv WFD NIE. induction denv; inverts WFD. 1,2:crush.
  - simpl. rewrite subst_dskvar_DSch_not_in_DSch_idempotent. crush.
    forwards: WfDTy_DSch_impls_dskvar_subset. eassumption. rewr in NIE. fsetdec.
Qed.

Axiom DEnv_dskvars_in_bindings : DEnv -> vars.

Theorem DMon_subst_skA : forall skA denv1 denv2 e dty,
    (denv1 :::s skA ++++ denv2) |=m e ▸ dty
  -> skA \notin DEnv_dskvars_in_bindings denv1
  -> exists L, forall skB,
    skB \notin L
  -> (denv1 :::s skB ++++ subst_dskvar_DEnv (DT_SkVar_f skB) skA denv2) |=m e ▸ (subst_dskvar_DTy (DT_SkVar_f skB) skA dty).
Abort.
(* Proof. *)
(*   introv MON WFD. *)
(*   forwards [L H]: (proj1 Mon_DGen_DEnv_subst_skA). eassumption. *)
(*   exists (L \u singleton skA). intros. forwards MON': H skB. fsetdec. *)
(*   norm. norm in MON'. simpl in MON'. *)
(*   assert (WFD': WfDEnv (denv1 :::s skA)). eauto. inverts WFD'. *)
(*   rewrite (subst_dskvar_DEnv_not_in_DEnv denv1) in MON'. eassumption. eauto. assumption. *)
(* Qed. *)

Lemma DGen_swap_DA__fsetdechelper : forall skA' L L' L'' da',
    skA' `notin` union L (union L' (union (varl da') L''))
  -> free_dskvars_DTy (DT_SkVar_f skA') [><] varl da'.
Proof. introv NIL. unfold AtomSetImpl.disjoint. simpl. fsetdec. Qed.

Theorem DGen_swap_DA : forall denv1 da1 da2 e dty dsch L,
    (denv1 :::a da1 :::a da2) |=m e ▸ dty
  -> generalize_DSch (DS_Mono dty) da1 = dsch
  -> wfd(denv1)
  -> exists da1' dty',
    (denv1 :::a da1' :::a da2) |=m e ▸ dty'
  /\ generalize_DSch (DS_Mono dty') da1' = dsch
  /\ varl da1' [><] L.
Abort.
(* Proof. *)
(*   introv MON GEN WFD. gen da2 dsch L. induction da1 as [|skA da1]; intros. *)
(*   - exists ([]:DA) dty. crush. *)
(*   - simpl in GEN. destruct dsch. inverts GEN. inversion GEN. clear GEN. rename H0 into GEN. *)
(*     forwards: close_DSch_wrt_DTy_open_DSch_wrt_DTy dsch skA. subst. *)
(*     rewrite free_dskvars_DSch_close_DSch_wrt_DTy. eauto. *)
(*     rewrite <- H in GEN. clear H. apply close_DSch_wrt_DTy_inj in GEN. *)
(*     forwards [da' [dty' [MON__IH [GEN__IH DISJ]]]]: IHda1 (da2 ++ [skA]) (singleton skA \u L). *)
(*       eauto. norm. simpl in MON. norm in MON. assumption. *)
(*       norm. norm in WFD. eassumption. *)
(*     (**) *)
(*     forwards [L' MON__IH']: DMon_subst_skA (denv1 ++++ <da'>da). norm in MON__IH. norm. apply MON__IH. *)
(*     admit. (* norm. norm in WFD'. eassumption. *) *)
(*     (**) *)
(*     forwards [skA' NIL]: atom_fresh (L \u L' \u varl da' \u free_dskvars_DSch (close_DSch_wrt_DTy skA (open_DSch_wrt_DTy dsch (DT_SkVar_f skA))) *)
(*                                        \u DEnv_dskvars (denv1 ++++ <da'>da) \u varl da2). *)
(*     exists (skA' :: da'). exists (subst_dskvar_DTy (DT_SkVar_f skA') skA dty'). simpl. rewr. splits. *)
(*     + forwards MON__IH'': MON__IH' skA'. fsetdec. norm in MON__IH''. norm. eassumption. *)
(*     + rewrite GEN. *)
(*       asserts_rewrite ( DS_Mono (subst_dskvar_DTy (DT_SkVar_f skA') skA dty') *)
(*                       = subst_dskvar_DSch (DT_SkVar_f skA') skA (DS_Mono dty') ). reflexivity. *)
(*       forwards: generalize_DSch_subst_dskvar_DSch (DT_SkVar_f skA') skA da'. auto. *)
(*         admit. *)
(*         (* admit. *) *)
(*         (* norm in WFD'. assert (WFD'': wfd(denv1 ++++ <da'>da ++++ <[skA]>da)). eauto. inverts WFD''. *) *)
(*         (* rewr in FR. fsetdec. *) *)
(*         eauto using DGen_swap_DA__fsetdechelper. *)
(*       rewrite H. *)
(*       rewrite GEN__IH. *)
(*       rewrite subst_dskvar_DSch_spec. rewrite close_DSch_wrt_DTy_open_DSch_wrt_DTy. reflexivity. eauto. *)
(*     (* + norm. apply WfDEnv_oneDA. split. *) *)
(*     (*   constructor. norm in WFD'. eauto. fsetdec. *) *)
(*     (*   norm in WFD'. apply WfDEnv_oneDA in WFD'. destr. *) *)
(*     (*   apply DFrA_props. apply DFrA_props in H0. destr. split. 2:assumption. *) *)
(*     (*   assert (varl da2 [><] DEnv_dskvars (denv1 ++++ <da'>da ++++ <[skA]>da ++++ <skA'>ds)). *) *)
(*     (*     symmetry. simpl. rewr. applys_eq disjoint_extend. fsetdec. *) *)
(*     (*     simpl in H0. rewr in H0. rewrite (fold_right_varl da') in H0. symmetry. eassumption. *) *)
(*     (*   eapply disj_subset_proper. 3:apply H2. crush. rewr. fsetdec. *) *)
(*     + apply disjoint_extend. fsetdec. *)
(*       eapply disj_subset_proper. 3:apply DISJ. 1,2:crush. *)

Axiom DGen_swap_DA : forall denv1 da1 da2 e dty dsch,
    (denv1 :::a da1 :::a da2) |=m e ▸ dty
  -> generalize_DSch (DS_Mono dty) da1 = dsch
  -> exists da1' dty',
    (denv1 :::a da1' :::a da2) |=m e ▸ dty'
  /\ generalize_DSch (DS_Mono dty') da1' = dsch
  /\ DFrA da1' denv1.

Theorem Mon_DGen_DEnv_x_sub : Mon_DEnv_x_sub__def /\ DGen_DEnv_x_sub__def.
Proof.
  forwards: (Mon_DGen_mut Mon_DEnv_x_sub__prop DGen_DEnv_x_sub__prop)
  ; unfold Mon_DEnv_x_sub__prop in *; unfold DGen_DEnv_x_sub__prop in *.
  7:{ jauto. }
  (* 2,4,5: eauto. *)
  - introv IN SS SUB.
    unfold_derel in SUB. destr.
    applys TmVar DSch5. rewrite <- H0. eassumption.
    eauto using supdenv_weaken_subsump.
  - eauto.
  - introv WFDTY1 MON IH SUB. econstructor. eauto. introv NIL. apply IH. eassumption. crush.
  - eauto.
  - introv MON__e1 IH__e1 MON__e2 IH__e2 SUB.
    econstructor. eauto. intros. apply IH__e2. eassumption. crush.

  - introv FR MON IH GEN SUB.
    forwards MON__IH: IH (denv2 :::a DA5). eauto.
    forwards [da' [dty' [MON' [GEN' DFR]]]]: DGen_swap_DA DA5 ([]:DA). simpl. eassumption. eassumption. simpl in DFR. simpl in MON'.
    econstructor. apply DFR. eassumption.  eassumption.
Qed.
Print Assumptions Mon_DGen_DEnv_x_sub.

Theorem Mon_DEnv_x_sub : forall (denv1 : DEnv) (e : e) (dty : DTy) (denv2 : DEnv),
    denv1 |=m e ▸ dty
  -> denv1 [<=]dex denv2
  -> denv2 |=m e ▸ dty.
Proof. apply Mon_DGen_DEnv_x_sub. Qed.

Theorem DGen_DEnv_x_sub : forall (denv1 : DEnv) (e : e) (dsch : DSch) (denv2 : DEnv),
    denv1 |=p e ▸ dsch
  -> denv1 [<=]dex denv2
  -> denv2 |=p e ▸ dsch.
Proof. apply Mon_DGen_DEnv_x_sub. Qed.

Corollary Mon_shift_DA : forall (denv1 : DEnv) (x : termvar) (dsch : DSch) (da : DA) (e : e) (dty : DTy),
    denv1 :::x x :- dsch :::a da |=m e ▸ dty
  -> denv1 :::a da :::x x :- dsch |=m e ▸ dty.
Proof.
  introv MON. eapply Mon_DEnv_x_sub. eassumption.
  autounfold. split. rewr. fsetdec'. rewr. fsetdec'.
Qed.
