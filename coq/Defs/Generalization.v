(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Export Defs.DEnv.
Require Export Defs.Env.
Require Export Defs.Freevars.
Require Export Defs.Lc.
Require Export Defs.List.
Require Export Defs.Set.

Require Export Defs.WfTy.

Lemma generalize_Sch_l_irrelevance__helper : forall (sch : Sch) (skA skB : skvar) (exA : exvar) (n : nat),
    skA \notin free_skvars_Sch sch
  -> skB \notin free_skvars_Sch sch
  -> S_Forall (close_Sch_wrt_Ty_rec n skA (subst_exvar_Sch (T_SkVar_f skA) exA sch)) =
    S_Forall (close_Sch_wrt_Ty_rec n skB (subst_exvar_Sch (T_SkVar_f skB) exA sch)).
Proof.
  introv NI__skA NI__skB. gen n. Sch_Ty_ind sch; crush.
  - ifdec; crush.
  - unfold close_Sch_wrt_Ty. ifdec; crush. if_taut.
  - simpl.
    forwards IH1: H n; try fsetdec. inverts IH1.
    forwards IH2: H1 n; try fsetdec. inverts IH2.
    reflexivity.
Qed.

Lemma generalize_Sch_l_irrelevance : forall (L2 L1 : vars) (sch : Sch) (a : A),
    generalize_Sch sch a L1 = generalize_Sch sch a L2.
Proof.
  introv. listind a; crush.
  unfold close_Sch_wrt_Ty. eapply generalize_Sch_l_irrelevance__helper.
  - forwards: proj1_sig_fresh (union (free_skvars_Sch (generalize_Sch sch a L2)) L1). crush.
  - crush. forwards: proj1_sig_fresh (union (free_skvars_Sch (generalize_Sch sch a L2)) L2). crush.
Qed.

Lemma generalize_sch_cons : forall (sch : Sch) (a : A) (exA : exvar) (L : vars),
    generalize_Sch sch (cons exA a) L =
      generalize_Sch (generalize_Sch sch a L) [exA] L.
Proof. crush. Qed.

Lemma generalize_DSch_cons : forall (dsch : DSch) (da : DA) (dskA : dskvar),
    generalize_DSch dsch (cons dskA da) =
      generalize_DSch (generalize_DSch dsch da) [dskA].
Proof. crush. Qed.

Lemma lc_Sch_generalize_Sch : forall (exA : exvar) (sch : Sch) (L : atoms),
    lc_Sch sch
  -> lc_Sch (generalize_Sch sch [exA] L).
Proof.
  introv LC.
  unfold generalize_Sch. simpl. constructor. intros.
  apply lc_Sch_open_Sch_wrt_Ty; auto. simpl. apply lc_Sch_subst_exvar_Sch; auto.
Qed.

Lemma generalize_props : forall (a : A) (sch : Sch) (L : atoms),
    lc_Sch sch
  -> free_skvars_Sch (generalize_Sch sch a L) [=] free_skvars_Sch sch
  /\ free_exvars_Sch (generalize_Sch sch a L) [=] AtomSetImpl.diff (free_exvars_Sch sch) (varl a)
  /\ lc_Sch (generalize_Sch sch a L).
Proof.
  intros. listind a; intros. simpl. crush. fsetdec. destruct IHa as [FV__sk [FV__ex LC]]. splits.
  - simpl. rewrite free_skvars_Sch_close_Sch_wrt_Ty.
    rewrite <- FV__sk. apply remove_free_skvars_Sch_subst_exvar_Sch. fresh_assert. fsetdec.
  - simpl. remember (proj1_sig (atom_fresh (union (free_skvars_Sch (generalize_Sch sch a L)) L))) as skA__in.
    rewrite free_exvars_Sch_close_Sch_wrt_Ty. rewrite free_exvars_Sch_subst_exvar_Sch_skA. rewrite FV__ex. rewr*. fsetdec.
  - apply lc_Sch_generalize_Sch. jauto.
Qed.

Lemma generalize_Wf : forall (env : Env) (a : A) (sch : Sch) (L : atoms),
    env ::a a |=ty sch
  -> env |=ty generalize_Sch sch a L.
Proof.
  introv WFTY. apply WfTy_props in WFTY. destruct WFTY as [FV__sk1 [FV__ex1 LC1]]. apply WfTy_props. destr.
  forwards [FV__sk2 [FV__ex2 LC2]]: generalize_props a L. eassumption. destr. splits. 1,3:crush.
  rewrite FV__ex2.
  unfold AtomSetImpl.Subset. intros exA INDIFF. apply diff_iff in INDIFF.
  unfold AtomSetImpl.Subset in FV__ex1. forwards: FV__ex1 exA. jauto.
  rewr*. fsetdec.
Qed.

Theorem free_exvars_Sch_generalize_Sch : forall sch a L,
  free_exvars_Sch (generalize_Sch sch a L) [<=] AtomSetImpl.diff (free_exvars_Sch sch) (varl a).
Proof.
  intros. induction a.
  - simpl. fsetdec.
  - simpl. remember (proj1_sig (atom_fresh (union (free_skvars_Sch (generalize_Sch sch a0 L)) L))) as skA.
    rewrite free_exvars_Sch_close_Sch_wrt_Ty.
    rewrite free_exvars_Sch_subst_exvar_Sch_upper. rewrite IHa. rewr. fsetdec.
Qed.
