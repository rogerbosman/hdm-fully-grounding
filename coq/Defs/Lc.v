(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Defs.Embed.
Require Import Defs.Substs.

(*** Notation, tactics etc*)
Ltac LC_ind LC :=
    let LC' := fresh "LC__ty" in
    induction LC as [LC' | ?]; [induction LC' | idtac].

Ltac inv_LC :=
  repeat match goal with
    | [ H : lc_Ty (T_SkVar_b _) |- _ ] => inverts H
    | [ H : lc_DTy (DT_SkVar_b _) |- _ ] => inverts H

    | [ H : lc_Ty (T_Fun _ _) |- _ ] => inverts H
    | [ H : lc_DTy (DT_Fun _ _) |- _ ] => inverts H


    | [ H : lc_Sch (S_Mono _) |- _ ] => inverts H
    | [ H : lc_DSch (DS_Mono _) |- _ ] => inverts H
  end.

(*** Sch <-> DSch & Ty <-> DTy LC *)
Theorem emb_Ty_lc : forall (dty : DTy),
    lc_Ty  (emb_Ty dty)
  <-> lc_DTy dty.
Proof. split; intros LC; induction dty; inverts LC; crush. Qed.
Corollary emb_Ty_lc2 : forall (dty : DTy),
    lc_Ty  (emb_Ty dty)
  -> lc_DTy dty.
Proof. apply emb_Ty_lc. Qed.
Corollary emb_Ty_lc1 : forall (dty : DTy),
    lc_DTy dty
  -> lc_Ty  (emb_Ty dty).
Proof. apply emb_Ty_lc. Qed.
#[export] Hint Resolve emb_Ty_lc1 emb_Ty_lc2 : slow.

#[export] Hint Extern 4 (lc_Ty (emb_Ty _)) => apply emb_Ty_lc : core.

Theorem embed_Sch_lc : forall (dsch : DSch),
    lc_Sch  (emb_Sch dsch)
  <-> lc_DSch dsch.
Proof.
  split.
  - introv LC. dependent induction LC. emb_auto. apply emb_Ty_lc in H. crush.
    (assert (EMB: exists dsch', dsch = DS_Forall dsch')). emb_auto. exists. crush.
    destruct EMB as [dsch' EMB]. subst. simpl in *. inverts x.
    constructor. intros. eapply (H0 dskA). rewrite embed_Sch_open_comm. crush.
  - introv LC. induction LC. constructor. apply emb_Ty_lc. assumption.
    constructor. fold emb_Sch. intros skA.
    forwards IH: H0 skA. rewrite embed_Sch_open_comm in IH. crush.
Qed.

Corollary embed_Sch_lc1 : forall (dsch : DSch),
    lc_Sch  (emb_Sch dsch)
  -> lc_DSch dsch.
Proof. apply embed_Sch_lc. Qed.
Corollary embed_Sch_lc2 : forall (dsch : DSch),
    lc_DSch dsch
  -> lc_Sch  (emb_Sch dsch).
Proof. apply embed_Sch_lc. Qed.
#[export] Hint Resolve embed_Sch_lc1 embed_Sch_lc2 : slow.

Theorem lc_Sch_mono : forall (ty : Ty),
    lc_Sch (S_Mono ty)
  <-> lc_Ty ty.
Proof. split. inversion 1. auto. auto. Qed.
#[export] Hint Rewrite lc_Sch_mono : core.
Theorem lc_DSch_mono : forall (dty : DTy),
    lc_DSch (DS_Mono dty)
  <-> lc_DTy dty.
Proof. split. inversion 1. auto. auto. Qed.
#[export] Hint Rewrite lc_DSch_mono : core.

(*** LC/substs *)
Theorem lc_Sch_subst_exvar_Sch : forall (sch : Sch) (ty : Ty) (exA : exvar),
    lc_Sch sch
  -> lc_Ty ty
  -> lc_Sch (subst_exvar_Sch ty exA sch).
Proof.
  introv LC__sch LC__ty.
  LC_ind LC__sch; default_simp.
  - constructor. constructor.
    forwards: IHLC__ty0_1. eassumption. inverts H. assumption.
    forwards: IHLC__ty0_2. eassumption. inverts H. assumption.
  - simpl. constructor. intros. simpl.
    forwards: H0 skA. rewrite subst_exvar_Sch_open_Sch_wrt_Ty in H1; crush.
Qed.

Corollary lc_Sch_subst_exvar_Sch' : forall (exA : exvar) (sch : Sch) (ty : Ty),
    lc_Sch sch
  -> lc_Sch (S_Mono ty)
  -> lc_Sch (subst_exvar_Sch ty exA sch).
Proof. intros. inv_LC. apply lc_Sch_subst_exvar_Sch; eauto. Qed.

Theorem lc_Sch_open_Sch_wrt_Ty : forall (sch : Sch) (skA : skvar) (ty : Ty),
    lc_Sch sch
  -> lc_Ty ty
  -> lc_Sch (open_Sch_wrt_Ty (close_Sch_wrt_Ty skA sch) ty).
Proof.
  introv LC__sch LC__ty. rewrite <- subst_skvar_Sch_spec. eauto using subst_skvar_Sch_lc_Sch.
Qed.
