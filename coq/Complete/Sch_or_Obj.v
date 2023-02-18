(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.
Require Import Defs.Defs.

Require Import Complete.SameShape.

(*** Definition *)

Definition Sch_or_Obj (env : Env) := env = • \/ (exists x sch env', env = env' ::x x :- sch) \/ (exists obj env', env = env' ::o obj).
Ltac SOO_auto := ((now (left; eauto)) || (now (right; (now (left; exists; eauto)) || (now (right; exists; eauto))))).
Definition DSch_or_DObj (denv : DEnv) := denv = ▪ \/ (exists x dsch denv', denv = denv' :::x x :- dsch) \/ (exists dobj denv', denv = denv' :::o dobj).

(** Conversion *)
Theorem SOO_DSODO : forall denv__in dsub__in env denv dsub,
    {denv__in, dsub__in}|= env ~> {denv, dsub}
  -> Sch_or_Obj env
  -> DSch_or_DObj denv.
Proof.
  introv INST SOO. unfold Sch_or_Obj in SOO. destr.
  - inverts INST. SOO_auto.
  - inv_EInst. SOO_auto.
  - destruct obj.
    inv_EInst. SOO_auto.
Qed.

(*** DSODO *)
Theorem DSODO_cons_DA' : forall denv1 denv2 da1 da2,
    denv1 :::a da1 = denv2 :::a da2
  -> DSch_or_DObj denv1
  -> DSch_or_DObj denv2
  -> denv1 = denv2 /\ da1 = da2.
Proof.
  introv EQ DSODO1 DSODO2. gen da2. induction da1; intros.
  - destruct da2. crush.
    simpl in EQ. rewr in EQ. inverts EQ. unfold DSch_or_DObj in DSODO1. crush.
  - destruct da2.
    simpl in EQ. rewr in EQ. inverts EQ. unfold DSch_or_DObj in DSODO2. crush.
    simpl in EQ. rewr in EQ. inverts EQ. forwards: IHda1. eassumption. crush.
Qed.

Theorem DSODO_cons_DA : forall denv1 denv2 da1 da2,
    DSch_or_DObj denv1
  -> denv1 :::a da1 = denv2 :::a da2
  -> exists da1', da1 = da2 ++ da1' /\ denv2 = denv1 :::a da1'.
Proof.
  intros. gen da2. induction da1; intros.
  - destruct da2.
    + simpl in H0. subst. exists ([]:DA). crush.
    + destruct H; destr; inverts H0.
  - destruct da2.
    + simpl in H0. rewr in H0. subst.
      exists. crush.
    + simpl in H0. rewr in H0. inverts H0.
      forwards: IHda1. eassumption. destr. exists. crush.
Qed.

(*** SOO *)
Theorem SOO_Inf : forall env__in e a ty env__out,
    env__in |= e ▸ ⟨a⟩ ty =| env__out
  -> Sch_or_Obj env__in
  -> Sch_or_Obj env__out.
Proof.
  intros.
  forwards: Inf_SameShape. eassumption. unfold Sch_or_Obj in H0. destr; inverts H1; SOO_auto.
Qed.

Theorem SOO_Gen : forall env__in e sch env__out,
    env__in |= e ▸ sch =| env__out
  -> Sch_or_Obj env__in
  -> Sch_or_Obj env__out.
Proof.
  intros.
  forwards: Gen_SameShape. eassumption. unfold Sch_or_Obj in H0. destr; inverts H1; SOO_auto.
Qed.

Theorem SOO_cons_DA : forall env denv1 denv2 dsub da1 da2 denv__in dsub__in,
    {denv__in, dsub__in}|= env ~> {denv1, dsub}
  -> Sch_or_Obj env
  -> denv1 :::a da1 = denv2 :::a da2
  -> exists da1', da1 = da2 ++ da1' /\ denv2 = denv1 :::a da1'.
Proof. introv INST SOB EQ. eapply DSODO_cons_DA. eapply SOO_DSODO. all: eassumption. Qed.

