(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Defs.Env.
Require Import Defs.Set.
Require Import Defs.Substs.


(*** Simplification *)
Theorem embed_Sch_mono : forall dty,
    emb_Sch (DS_Mono dty) = S_Mono (emb_Ty dty).
Proof. reflexivity. Qed.
#[export] Hint Rewrite embed_Sch_mono : core.

(*** Inj *)
Theorem emb_Ty_inj : forall (dty1 dty2 : DTy),
    emb_Ty dty1 = emb_Ty dty2
  -> dty1 = dty2.
Proof.
  induction dty1; destruct dty2; crush.
  erewrite IHdty1_1. erewrite IHdty1_2. crush. crush. crush.
Qed.

Theorem emb_Sch_inj : forall (dsch1 dsch2 : DSch),
    emb_Sch dsch1 = emb_Sch dsch2
  -> dsch1 = dsch2.
Proof.
  induction dsch1; destruct dsch2; crush. apply emb_Ty_inj in H. crush.
  forwards: IHdsch1. eassumption. crush.
Qed.

(*** Embed & open *)
Lemma embed_Ty_open_comm_rec : forall (dty1 dty2 : DTy) (n : nat),
   emb_Ty (open_DTy_wrt_DTy_rec n dty2 dty1) = open_Ty_wrt_Ty_rec n (emb_Ty dty2) (emb_Ty dty1).
Proof. intros. induction dty1; crush. ltdec; ifdec; crush. Qed.

Theorem embed_Ty_open_comm : forall (dty1 dty2 : DTy),
   emb_Ty (open_DTy_wrt_DTy dty1 dty2) = open_Ty_wrt_Ty (emb_Ty dty1) (emb_Ty dty2).
Proof. unfold open_DTy_wrt_DTy. unfold open_Ty_wrt_Ty. eauto using embed_Ty_open_comm_rec. Qed.

Theorem embed_Sch_open_comm : forall (dsch : DSch) (dty : DTy),
   emb_Sch (open_DSch_wrt_DTy dsch dty) = open_Sch_wrt_Ty (emb_Sch dsch) (emb_Ty dty).
Proof.
  intros. unfold open_DSch_wrt_DTy. unfold open_Sch_wrt_Ty. generalize 0.
  induction dsch; intros.
  - simpl. rewrite embed_Ty_open_comm_rec. reflexivity.
  - crush.
Qed.

(*** emb_auto *)
Lemma emb_auto_forall : forall (sch : Sch) (dsch : DSch),
    S_Forall sch = emb_Sch dsch
    -> exists dsch', dsch = DS_Forall dsch'
             /\ sch = emb_Sch dsch'.
Proof. destruct dsch; crush. eauto. Qed.

Lemma emb_auto_forall' : forall (sch1 sch2 : Sch),
    S_Forall sch1 = S_Forall sch2
  -> sch1 = sch2.
Proof. inversion 1. auto. Qed.

Lemma emb_auto_mono : forall (ty : Ty) (dsch : DSch),
    S_Mono ty = emb_Sch dsch
  -> exists dty, dsch = DS_Mono dty
          /\ ty = emb_Ty dty.
Proof. destruct dsch; crush. eauto. Qed.

Lemma emb_auto_sk_n : forall (n : nat) (dty : DTy),
    T_SkVar_b n = emb_Ty dty
  -> dty = DT_SkVar_b n.
Proof. destruct dty; crush. Qed.

Lemma emb_auto_sk_f : forall (skA : skvar) (dty : DTy),
    T_SkVar_f skA = emb_Ty dty
  -> dty = DT_SkVar_f skA.
Proof. destruct dty; crush. Qed.

Lemma emb_auto_ex : forall (exA : exvar) (dty : DTy),
    T_ExVar exA = emb_Ty dty
  -> False.
Proof. destruct dty; crush. Qed.

Lemma emb_auto_unit : forall (dty : DTy),
    T_Unit = emb_Ty dty
  -> dty = DT_Unit.
Proof. destruct dty; crush. Qed.

Lemma emb_auto_fun : forall (ty1 ty2 : Ty) (dty : DTy),
    T_Fun ty1 ty2 = emb_Ty dty
  -> exists dty1 dty2, dty = DT_Fun dty1 dty2
               /\ ty1 = emb_Ty dty1
               /\ ty2 = emb_Ty dty2.
Proof. destruct dty; crush. eauto. Qed.

Theorem embed_Sch_Forall : forall dsch,
    emb_Sch (DS_Forall dsch) = S_Forall (emb_Sch dsch).
Proof. reflexivity. Qed.
#[export] Hint Rewrite embed_Sch_Forall : dsub_simpl.

Theorem emb_auto_DSub_app_Forall : forall dsub sch1 sch2,
    DSub_app sch1 dsub = S_Forall sch2
  -> exists sch1', sch1 = S_Forall sch1'
           /\ DSub_app sch1' dsub = sch2.
Proof.
  introv EMB. destruct sch1.
  - crush.
  - exists sch1. crush.
Qed.

Theorem embed_mono_inversion : forall (ty : Ty) (dty : DTy),
    S_Mono ty = S_Mono (emb_Ty dty)
  -> ty = emb_Ty dty.
Proof. inversion 1. reflexivity. Qed.

Ltac emb_auto' :=
  let sch   := fresh "sch" in
  let dsch' := fresh "dsch" in
  let dty'  := fresh "dty"  in
  let dty1  := fresh "dty1" in
  let dty2  := fresh "dty2" in
  let EQ    := fresh "EQ"   in
  let EMB'  := fresh "EMB"  in
  let EMB1  := fresh "EMB1" in
  let EMB2  := fresh "EMB2" in
  repeat match goal with
    | [ H: DS_Mono _ = DS_Mono _  |- _ ] =>
        symmetry in H; inverts H
    | [ H: S_Mono ?ty = S_Mono (emb_Ty ?dty)  |- _ ] =>
        apply embed_mono_inversion in H
    | [ H: S_Forall ?sch1 = S_Forall ?sch2 |- _ ] =>
        apply (emb_auto_forall' sch1 sch2) in H
    | [ H: S_Forall ?sch = emb_Sch ?dsch |- _ ] =>
        apply (emb_auto_forall sch dsch) in H; destruct H as [dsch' [EQ EMB']]
    | [ H: S_Mono ?ty = emb_Sch ?dsch |- _ ] =>
        apply (emb_auto_mono ty dsch) in H; destruct H as [dty' [EQ EMB']]
    | [ H: T_SkVar_b ?n = emb_Ty ?dty |- _ ] =>
        apply (emb_auto_sk_n n dty) in H
    | [ H: T_SkVar_f ?skA = emb_Ty ?dty |- _ ] =>
        apply (emb_auto_sk_f skA dty) in H
    | [ H: T_ExVar ?exA = emb_Ty ?dty |- _ ] =>
        apply (emb_auto_ex exA dty) in H
    | [ H: T_Unit = emb_Ty ?dty |- _ ] =>
        apply (emb_auto_unit dty) in H
    | [ H: T_Fun ?ty1 ?ty2 = emb_Ty ?dty |- _ ] =>
        apply (emb_auto_fun ty1 ty2 dty) in H; destruct H as [dty1 [dty2 [EQ [EMB1 EMB2]]]]
    | [ H: DSub_app ?sch1 ?dsub = S_Forall ?sch2 |- _ ] =>
        apply (emb_auto_DSub_app_Forall dsub sch1 sch2) in H; destruct H as [sch [EQ EMB']]
    | [ H: DSub_app _ _ = _ |- _ ] =>
        autorewrite with dsub_simpl in H
    | [ H: DSub_app_t _ _ = _ |- _ ] =>
        autorewrite with dsub_simpl in H
    end.

Ltac emb_auto := emb_auto'; subst.
Ltac emb_auto'' := repeat emb_auto.

(*** free vars embed *)
(* free_exvars_Ty*)
Theorem embedded_Ty_does_not_contain_exvars : forall (dty : DTy) (exA : exvar),
    exA \notin free_exvars_Ty (emb_Ty dty).
Proof. induction dty; crush. indestr; eauto. Qed.
#[export] Hint Resolve embedded_Ty_does_not_contain_exvars : core.

Theorem embedded_Sch_does_not_contain_exvars : forall (dsch : DSch) (exA : exvar),
    exA \notin free_exvars_Sch (emb_Sch dsch).
Proof. induction dsch; crush. forwards NIT: embedded_Ty_does_not_contain_exvars. crush. apply NIT. eauto. Qed.
#[export] Hint Resolve embedded_Sch_does_not_contain_exvars : core.

(* free_skvars_Ty*)
Theorem free_skvars_Ty_embed_Ty : forall (dty : DTy),
    free_skvars_Ty (emb_Ty dty) = free_dskvars_DTy dty.
Proof. introv. induction dty; crush. Qed.

Lemma free_skvars_Sch_embed_Sch : forall (dsch : DSch),
    free_skvars_Sch (emb_Sch dsch) = free_dskvars_DSch dsch.
Proof. introv. DSch_DTy_ind dsch; crush. Qed.

(*** embed/subst *)
Theorem subst_exvar_Ty_embed_idempotent : forall (dty : DTy) (ty__in : Ty) (exA : exvar),
    subst_exvar_Ty ty__in exA (emb_Ty dty) = emb_Ty dty.
Proof. eauto using subst_exvar_Ty_not_in_Ty_idempotent. Qed.
#[export] Hint Rewrite subst_exvar_Ty_embed_idempotent : core.

Theorem subst_exvar_Sch_embed_idempotent : forall (dsch : DSch) (ty__in : Ty) (exA : exvar),
    subst_exvar_Sch ty__in exA (emb_Sch dsch) = emb_Sch dsch.
Proof. eauto using subst_exvar_Sch_not_in_Sch_idempotent. Qed.
#[export] Hint Rewrite subst_exvar_Sch_embed_idempotent : core.

Theorem embed_Sch_subst_dskvar_DSch : forall dty dskA dsch,
    emb_Sch (subst_dskvar_DSch dty dskA dsch) = subst_skvar_Sch (emb_Ty dty) dskA (emb_Sch dsch).
Proof.
  introv. DSch_DTy_ind dsch. 1,3,4,5: crush.
  - rewr. simpl. ifdec; crush.
Qed.
