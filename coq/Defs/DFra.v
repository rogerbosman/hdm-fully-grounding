(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Coq.FSets.FSetProperties.

Require Import Defs.DEnv.
Require Import Defs.List.
Require Import Defs.Obj.
Require Import Defs.Set.

(* (*** Notation, tactics etc*) *)
(* Theorem FrA_app_split : forall (a1 a2 : DA) (denv : DEnv), *)
(*     DFrA (a2 ++ a1) env *)
(*   <-> (DFrA a2 (env ::a a1) /\ DFrA a1 env). *)
(* Proof. *)
(*   introv. split; induction a2; rewr. 1,3:crush. *)
(*   - split; inverts H. 2:{ apply IHa2. assumption. } *)
(*     constructor. crush. rewr*. intros. apply FR. fsetdec. *)
(*   - intros. destr. inverts H. destr. constructor. eauto. *)
(*     rewr*. intros. apply FR. fsetdec. *)
(* Qed. *)

(* Ltac inv_FrA_ := *)
(*   let H := fresh "H" in *)
(*   let FR1 := fresh "FR" in *)
(*   let FR2 := fresh "FR" in *)
(*   match goal with *)
(*     | [ H  : DFrA nil _ |- _ ] => clear H *)
(*     | [ H  : DFrA (cons _ _) _ |- _ ] => inverts H *)
(*     | [ H  : DFrA ([_]) _ |- _ ] => inverts H *)
(*     (* | [ H  : DFrA (?a2 ++ ?a1) ?env |- _ ] => assert (H' := H); apply FrA_app_split in H'; destruct H' as [FR1 FR2] *) *)
(*     | [ H  : DFrA (?a2 ++ ?a1) ?env |- _ ] => apply FrA_app_split in H; destruct H as [FR1 FR2] *)
(*   end. *)
(* Ltac inv_FrA := repeat inv_FrA_. *)

(* (*** Inversion *) *)
Theorem DFrA_inv : forall (dskA : dskvar) (da : DA) (denv : DEnv),
    DFrA (dskA :: da) denv
  -> DFrA da denv
  /\ dskA \notin DEnv_dskvars (denv :::a da).
Proof. inversion 1. jauto. Qed.
Corollary DFrA_inv__proj1 : forall (dskA : var) (da : DA) (denv : DEnv),
    DFrA (dskA :: da) denv
  -> DFrA         da  denv.
Proof. apply DFrA_inv. Qed.
Corollary DFrA_inv__proj2 : forall (dskA : var) (da : DA) (denv : DEnv),
    DFrA (dskA :: da) denv
  -> dskA \notin DEnv_dskvars (denv :::a da).
Proof. apply DFrA_inv. Qed.
#[export] Hint Resolve DFrA_inv__proj1 DFrA_inv__proj2 : core.

(* Ltac indestr := rewr*; autorewrite with in_disj in *; destr. *)
(* Tactic Notation "indestr" "in" hyp(H) := rewr in H; autorewrite with in_disj in H. *)

(* Theorem FrA_in_inv : forall (exA : var) (da : DA) (denv : DEnv), *)
(*     DFrA da denv *)
(*   -> exA \in varl da *)
(*   -> exA \notin DEnv_dskvars denv. *)
(* Proof. *)
(*   induction a. crush. intros. indestr. eauto. rewr*. subst. *)
(*   forwards: DFrA_inv__proj2. eassumption. unfold not in *. crush. *)
(* Qed. *)


(* (*** Props *) *)
Theorem DFrA_props : forall (da : DA) (denv : DEnv),
    DFrA da denv
  <-> varl da [><] DEnv_dskvars denv
  /\ NoDup' da.
Proof.
  intros. split.
  - induction 1. crush. destr. split.
    + rewr. apply disjoint_extend'. rewr in DFR. crush. eassumption.
    + constructor. rewr in DFR. crush. assumption.
  - intros [? ND]. induction ND. crush. rename a into da.
    constructor. rewr in H.
    apply IHND. assert (SUB: varl da [<=] varl da \u singleton exA). fsetdec.
    rewrite SUB. eassumption.
    rewr. intros. indestr. crush. eapply in_disjoint_impl. eassumption. 2:eassumption. fsetdec.
Qed.
Corollary DFrA_props1 : forall (da : DA) (denv : DEnv),
    DFrA da denv
  -> varl da [><] DEnv_dskvars denv
  /\ NoDup' da.
Proof. apply DFrA_props. Qed.
Corollary DFrA_props2 : forall (da : DA) (denv : DEnv),
    varl da [><] DEnv_dskvars denv
  -> NoDup' da
  -> DFrA da denv.
Proof. intros. apply DFrA_props. crush. Qed.
Corollary DFrA_props3 : forall (da : DA) (denv : DEnv),
    DFrA da denv
  -> varl da [><] DEnv_dskvars denv.
Proof. apply DFrA_props. Qed.
Corollary DFrA_props4 : forall (da : DA) (denv : DEnv),
    DFrA da denv
  -> NoDup' da.
Proof. apply DFrA_props. Qed.

(* (*** Rewriting *) *)
Theorem DFrA_rewr : forall (da1 da2 : DA) (denv1 denv2 : DEnv),
    DFrA da1 denv1
  -> da2 [<=]lu da1
  -> denv2 [<=]de denv1
  -> DFrA da2 denv2.
Proof.
  introv FRA SUB__l SUB__e. rewrite DFrA_props in *.
  split.
  - applys disj_subset_proper. 3:jauto. crush. auto.
  - jauto.
Qed.
#[export] Hint Resolve DFrA_rewr : core.

#[export] Instance DFrA_rewr_proper : Proper (flip list_uni_sub ==> flip DEnv_sub ==> impl) DFrA.
Proof. unfold Proper, respectful, impl, flip. intros. eauto. Qed.

Corollary DFrA_DEnv_sub : forall (denv1 denv2 : DEnv) (da : DA),
    DFrA da denv1
  -> denv2 [<=]de denv1
  -> DFrA da denv2.
Proof. eauto. Qed.
Corollary DFrA_sublist : forall (da1 da2 : DA) (denv : DEnv),
    DFrA da1 denv
  -> da2 [<=]lu da1
  -> DFrA da2 denv.
Proof. eauto. Qed.

(*** Unsorted *)
Lemma DFrA_cons_shift: forall (dskA : dskvar) (da : DA) (denv : DEnv),
    DFrA da (denv :::s dskA)
  -> dskA `notin` DEnv_dskvars denv
  -> DFrA (dskA :: da) denv.
Proof.
  introv DFR NID. apply DFrA_props in DFR. apply DFrA_props. destr. split.
  - rewr. apply disjoint_extend'. eassumption. simpl in H. rewr in H. eapply disj_subset_proper.
    3:eassumption. crush. rewr. crush.
  - constructor. 2:assumption. eapply in_disjoint_impl_notin1. eassumption. rewr. fsetdec.
Qed.

Theorem DFrA_app_shift : forall da1 da2 denv,
    DFrA (da1 ++ da2) denv
  -> DFrA da1 (denv :::a da2).
Proof.
  intros. induction da1. crush.
  constructor. inverts H. eauto. inverts H. rewr. rewr in DFR.
  rewrite (fold_right_varl da1). fsetdec.
Qed.
