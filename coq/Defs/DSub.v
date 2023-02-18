(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Defs.DEnv.
Require Import Defs.Env.
Require Import Defs.Embed.
Require Import Defs.Freevars.
Require Import Defs.Lc.
Require Import Defs.List.
Require Import Defs.OpenClose.
Require Import Defs.Set.
Require Import Defs.Substs.

Require Import Defs.WfDTy.


(*** Notation, tactics etc*)
#[export] Hint Unfold DSub_to_A : core.
#[export] Hint Unfold DSub_dom : core.

Ltac DSub_ind dsub :=
    let dsub' := fresh "dsub" in
    (* let DTY := fresh "dty" in *)
    (* let exA := fresh "exA" in *)
    induction dsub as [|[?exA ?dty] dsub'] using list_ind.
Ltac rev_DSub_ind dsub :=
    let dsub' := fresh "dsub" in
    (* let DTY := fresh "dty" in *)
    (* let exA := fresh "exA" in *)
    induction dsub as [|[?exA ?dty] dsub'] using rev_ind.

(*** DSub_dom_(sub/eq) *)
(** DSub_sub *)
(* Def *)
Definition DSub_dom_sub (dsub1 dsub2 : DSub) :=
   DSub_dom dsub1 [<=] DSub_dom dsub2.
#[export] Hint Unfold DSub_dom_sub : core.

Notation "A [<=]dsd B" := (DSub_dom_sub A B) (at level 65, format "A  [<=]dsd  B").

(* Instance *)
Lemma DSub_dom_sub_refl : Reflexive DSub_dom_sub.
Proof. autounfold. crush. Qed.
Lemma DSub_dom_sub_trans : Transitive DSub_dom_sub.
Proof. autounfold. crush. Qed.
#[export] Hint Resolve DSub_dom_sub_refl : core.

Theorem DSub_dom_sub_app : forall (dsub1 dsub1' dsub2 dsub2' : DSub),
    dsub1 [<=]dsd dsub1'
  -> dsub2 [<=]dsd dsub2'
  -> dsub1 ++ dsub2 [<=]dsd dsub1' ++ dsub2'.
Proof. autounfold. intros. rewr. fsetdec'. Qed.
#[export] Hint Resolve DSub_dom_sub_app : core.
#[export] Instance DSub_dom_sub_app_proper : Proper (DSub_dom_sub ==> DSub_dom_sub ==> DSub_dom_sub) (app (A:=(atom*DTy))).
Proof. eauto. Qed.

Module DSub_dom_sub_subrel <: list_subrel.
  Definition elt := (atom * DTy).
  Definition R : list elt -> list elt -> Prop := DSub_dom_sub.

  Definition refl  : Reflexive  R := DSub_dom_sub_refl.
  Definition trans : Transitive R := DSub_dom_sub_trans.

  Definition proper : Proper (R ==> R ==> R) (app (A := elt)) := DSub_dom_sub_app_proper.

  Theorem R_empty : forall (l : list elt), R [] l. unfold R, DSub_dom_sub. rewr. intros. fsetdec'. Qed.
End DSub_dom_sub_subrel.

Module Export DSub_dom_sub_subrel_facts := list_subrel_facts DSub_dom_sub_subrel.
#[export] Hint Extern 1 (DSub_dom_sub _ _) => fold DSub_dom_sub_subrel.R : core.

(** DSub_dom_eq *)
(* Def *)
Definition DSub_dom_eq (dsub1 dsub2 : DSub) :=
   DSub_dom dsub1 ⟪=⟫ DSub_dom dsub2.
#[export] Hint Unfold DSub_dom_eq : core.

Notation "A [=]dsd B" := (DSub_dom_eq A B) (at level 65, format "A  [=]dsd  B").

(* Instance *)
Lemma DSub_dom_eq_refl : Reflexive DSub_dom_eq.
Proof. autounfold. crush. Qed.
Lemma DSub_dom_eq_trans : Transitive DSub_dom_eq.
Proof. autounfold. crush. Qed.
Lemma DSub_dom_eq_symm : Symmetric DSub_dom_eq.
Proof. autounfold. crush. Qed.
#[export] Hint Resolve DSub_dom_eq_refl DSub_dom_eq_symm : core.

Theorem DSub_dom_eq_app : forall (dsub1 dsub1' dsub2 dsub2' : DSub),
    dsub1 [=]dsd dsub1'
  -> dsub2 [=]dsd dsub2'
  -> dsub1 ++ dsub2 [=]dsd dsub1' ++ dsub2'.
Proof. autounfold. intros. rewr. fsetdec'. Qed.
#[export] Hint Resolve DSub_dom_eq_app : core.
#[export] Instance DSub_dom_eq_app_proper : Proper (DSub_dom_eq ==> DSub_dom_eq ==> DSub_dom_eq) (app (A:=(atom*DTy))).
Proof. eauto. Qed.

Module DSub_dom_eq_eqrel <: list_eqrel.
  Definition elt := (atom * DTy).
  Definition R : list elt -> list elt -> Prop := DSub_dom_eq.

  Definition refl  : Reflexive  R := DSub_dom_eq_refl.
  Definition trans : Transitive R := DSub_dom_eq_trans.
  Definition symm  : Symmetric  R := DSub_dom_eq_symm.

  Definition proper : Proper (R ==> R ==> R) (app (A := elt)) := DSub_dom_eq_app_proper.
End DSub_dom_eq_eqrel.

Module Export DSub_dom_eq_eqrel_facts := list_eqrel_facts DSub_dom_eq_eqrel.
#[export] Hint Extern 1 (DSub_dom_eq _ _) => fold DSub_dom_eq_eqrel.R : core.

(* Conversion *)
Theorem DSub_dom_eq_sub : forall (dsub1 dsub2 : DSub),
    dsub1 [=]dsd dsub2
  -> dsub1 [<=]dsd dsub2.
Proof. autounfold. crush. Qed.
#[export] Hint Resolve DSub_dom_eq_sub : core.

Theorem DSub_dom_sub_eq : forall (dsub1 dsub2 : DSub),
    dsub1 [<=]dsd dsub2
  -> dsub2 [<=]dsd dsub1
  -> dsub1 [=]dsd dsub2.
Proof. autounfold. intros. fsetdec'. Qed.

(*** DSub_codom_(sub/eq) *)
(** DSub_sub *)
(* Def *)
Definition DSub_codom_sub (dsub1 dsub2 : DSub) :=
   DSub_codom dsub1 ⟪<=⟫ DSub_codom dsub2.
#[export] Hint Unfold DSub_codom_sub : core.

Notation "A [<=]dsc B" := (DSub_codom_sub A B) (at level 65, format "A  [<=]dsc  B").

(* Instance *)
Lemma DSub_codom_sub_refl : Reflexive DSub_codom_sub.
Proof. autounfold. crush. Qed.
Lemma DSub_codom_sub_trans : Transitive DSub_codom_sub.
Proof. autounfold. crush. Qed.
#[export] Hint Resolve DSub_codom_sub_refl : core.

Theorem DSub_codom_sub_app : forall (dsub1 dsub1' dsub2 dsub2' : DSub),
    dsub1 [<=]dsc dsub1'
  -> dsub2 [<=]dsc dsub2'
  -> dsub1 ++ dsub2 [<=]dsc dsub1' ++ dsub2'.
Proof. autounfold. intros. rewr. fsetdec'. Qed.
#[export] Hint Resolve DSub_codom_sub_app : core.
#[export] Instance DSub_codom_sub_app_proper : Proper (DSub_codom_sub ==> DSub_codom_sub ==> DSub_codom_sub) (app (A:=(atom*DTy))).
Proof. eauto. Qed.

Module DSub_codom_sub_subrel <: list_subrel.
  Definition elt := (atom * DTy).
  Definition R : list elt -> list elt -> Prop := DSub_codom_sub.

  Definition refl  : Reflexive  R := DSub_codom_sub_refl.
  Definition trans : Transitive R := DSub_codom_sub_trans.

  Definition proper : Proper (R ==> R ==> R) (app (A := elt)) := DSub_codom_sub_app_proper.

  Theorem R_empty : forall (l : list elt), R [] l. unfold R, DSub_codom_sub. rewr. intros. fsetdec'. Qed.
End DSub_codom_sub_subrel.

Module Export DSub_codom_sub_subrel_facts := list_subrel_facts DSub_codom_sub_subrel.
#[export] Hint Extern 1 (DSub_codom_sub _ _) => fold DSub_codom_sub_subrel.R : core.

(** DSub_codom_eq *)
(* Def *)
Definition DSub_codom_eq (dsub1 dsub2 : DSub) :=
   DSub_codom dsub1 ⟪=⟫ DSub_codom dsub2.
#[export] Hint Unfold DSub_codom_eq : core.

Notation "A [=]dsc B" := (DSub_codom_eq A B) (at level 65, format "A  [=]dsc  B").

(* Instance *)
Lemma DSub_codom_eq_refl : Reflexive DSub_codom_eq.
Proof. autounfold. crush. Qed.
Lemma DSub_codom_eq_trans : Transitive DSub_codom_eq.
Proof. autounfold. crush. Qed.
Lemma DSub_codom_eq_symm : Symmetric DSub_codom_eq.
Proof. autounfold. crush. Qed.
#[export] Hint Resolve DSub_codom_eq_refl DSub_codom_eq_symm : core.

Theorem DSub_codom_eq_app : forall (dsub1 dsub1' dsub2 dsub2' : DSub),
    dsub1 [=]dsc dsub1'
  -> dsub2 [=]dsc dsub2'
  -> dsub1 ++ dsub2 [=]dsc dsub1' ++ dsub2'.
Proof. autounfold. intros. rewr. fsetdec'. Qed.
#[export] Hint Resolve DSub_codom_eq_app : core.
#[export] Instance DSub_codom_eq_app_proper : Proper (DSub_codom_eq ==> DSub_codom_eq ==> DSub_codom_eq) (app (A:=(atom*DTy))).
Proof. eauto. Qed.

Module DSub_codom_eq_eqrel <: list_eqrel.
  Definition elt := (atom * DTy).
  Definition R : list elt -> list elt -> Prop := DSub_codom_eq.

  Definition refl  : Reflexive  R := DSub_codom_eq_refl.
  Definition trans : Transitive R := DSub_codom_eq_trans.
  Definition symm  : Symmetric  R := DSub_codom_eq_symm.

  Definition proper : Proper (R ==> R ==> R) (app (A := elt)) := DSub_codom_eq_app_proper.
End DSub_codom_eq_eqrel.

Module Export DSub_codom_eq_eqrel_facts := list_eqrel_facts DSub_codom_eq_eqrel.
#[export] Hint Extern 1 (DSub_codom_eq _ _) => fold DSub_codom_eq_eqrel.R : core.

(* Conversion *)
Theorem DSub_codom_eq_sub : forall (dsub1 dsub2 : DSub),
    dsub1 [=]dsc dsub2
  -> dsub1 [<=]dsc dsub2.
Proof. autounfold. crush. Qed.
#[export] Hint Resolve DSub_codom_eq_sub : core.

Theorem DSub_codom_sub_eq : forall (dsub1 dsub2 : DSub),
    dsub1 [<=]dsc dsub2
  -> dsub2 [<=]dsc dsub1
  -> dsub1 [=]dsc dsub2.
Proof. autounfold. intros. fsetdec'. Qed.

(*** DSub_(sub/eq) *)
(** DSub_sub *)
Definition DSub_sub (dsub1 dsub2 : DSub) :=
   DSub_bindings dsub1 ⟪<=⟫ DSub_bindings dsub2.
#[export] Hint Unfold DSub_sub : core.

Notation "A [<=]ds B" := (DSub_sub A B) (at level 65, format "A  [<=]ds  B").

(* Instance *)
Lemma DSub_sub_refl : Reflexive DSub_sub.
Proof. autounfold. crush. Qed.
Lemma DSub_sub_trans : Transitive DSub_sub.
Proof. autounfold. crush. Qed.
#[export] Hint Resolve DSub_sub_refl : core.

Theorem DSub_sub_app : forall (dsub1 dsub1' dsub2 dsub2' : DSub),
    dsub1 [<=]ds dsub1'
  -> dsub2 [<=]ds dsub2'
  -> dsub1 ++ dsub2 [<=]ds dsub1' ++ dsub2'.
Proof. autounfold. intros. rewr. fsetdec'. Qed.
#[export] Hint Resolve DSub_sub_app : core.
#[export] Instance DSub_sub_app_proper : Proper (DSub_sub ==> DSub_sub ==> DSub_sub) (app (A:=(atom*DTy))).
Proof. eauto. Qed.

Module DSub_sub_subrel <: list_subrel.
  Definition elt := (atom * DTy).
  Definition R : list elt -> list elt -> Prop := DSub_sub.

  Definition refl  : Reflexive  R := DSub_sub_refl.
  Definition trans : Transitive R := DSub_sub_trans.

  Definition proper : Proper (R ==> R ==> R) (app (A := elt)) := DSub_sub_app_proper.

  Theorem R_empty : forall (l : list elt), R [] l. unfold R, DSub_sub. rewr. intros. fsetdec'. Qed.
End DSub_sub_subrel.

Module Export DSub_sub_subrel_facts := list_subrel_facts DSub_sub_subrel.
#[export] Hint Extern 1 (DSub_sub _ _) => fold DSub_sub_subrel.R : core.

(* Conversions *)
Theorem DSub_bindings_dom : forall (exA : exvar) (dsub : DSub),
    (exists dty, DTyPSI.In (exA, dty) (DSub_bindings dsub)) <-> exA \in (DSub_dom dsub).
Proof.
  introv. induction dsub. split; intros; destr; fsetdec''.
  destruct a. destruct (eq_dec exA e).
  - subst. split; intros.
    +      rewr. fsetdec''. (*Note to reviewer: Why is this solved by DTySD.fsetdec ?? *)
    + exists d. rewr. fsetdec.
  - split; intros.
    + destr. rewr*.
      forwards>: IHdsub. exists dty. apply DTyPS_facts.union_iff in H. destr. assumption. assert ((exA, dty) = (e, d)). fsetdec''. crush.
      fsetdec'.
    + forwards< [dty IN]: IHdsub. rewr*. apply union_iff in H. simpl in H. fsetdec'.
      exists dty. rewr. fsetdec'.
Qed.
Corollary DSub_bindings_dom1 : forall (exA : exvar) (dty : DTy) (dsub : DSub),
     DTyPSI.In (exA, dty) (DSub_bindings dsub)
  -> exA \in (DSub_dom dsub).
Proof. intros. apply DSub_bindings_dom. exists dty. assumption. Qed.
#[export] Hint Resolve DSub_bindings_dom1 : core.

Theorem DSub_bindings_codom : forall (dty : DTy) (dsub : DSub),
    (exists exA, DTyPSI.In (exA, dty) (DSub_bindings dsub)) <-> DTySI.In dty (DSub_codom dsub).
Proof.
  introv. induction dsub. split; intros; destr; fsetdec''.
  destruct a. destruct (eq_DTy dty d).
  - subst. split; intros.
    +      rewr. fsetdec''. (*Note to reviewer: Why is this solved by DTySD.fsetdec ?? *)
    + exists e. rewr. fsetdec.
  - split; intros.
    + destr. rewr*.
      forwards>: IHdsub. exists exA. apply DTyPS_facts.union_iff in H. destr. assumption. assert ((exA, dty) = (e, d)). fsetdec''. crush.
      fsetdec'.
    + forwards< [exA IN]: IHdsub. rewr*. apply DTyS_facts.union_iff in H. simpl in H. fsetdec'.
      exists exA. rewr. fsetdec'.
Qed.
Corollary DSub_bindings_codom1 : forall (dty : DTy) (exA : exvar) (dsub : DSub),
    DTyPSI.In (exA, dty) (DSub_bindings dsub)
  -> DTySI.In dty (DSub_codom dsub).
Proof. intros. apply DSub_bindings_codom. exists exA. assumption. Qed.
#[export] Hint Resolve DSub_bindings_codom1 : core.

Theorem DSub_sub_dom : forall (dsub1 dsub2 : DSub),
    dsub1 [<=]ds  dsub2
  -> dsub1 [<=]dsd dsub2.
Proof.
  autounfold. rewr. unfold DTyPSI.Subset, AtomSetImpl.Subset. intros dsub1 dsub2 SUB__ds dty IN.
  apply DSub_bindings_dom in IN. destruct IN as [?dty IN]. apply DSub_bindings_dom. exists dty0. auto.
Qed.
#[export] Hint Resolve DSub_sub_dom : core.

Lemma in_codom_in_bindings : forall (dty : DTy) (dsub : DSub),
    DTySI.In dty (DSub_codom dsub) <-> (exists exA, DTyPSI.In (exA, dty) (DSub_bindings dsub)).
Proof.
  introv. induction dsub. split; intros; destr; fsetdec''.
  destruct a. destruct (DecidableDTy.eq_dec dty d).
  - subst. split; intros.
    + exists e. rewr. fsetdec.
    +      rewr. fsetdec.
  - split; intros.
    + forwards> [exA IN]: IHdsub. rewr*. apply DTyS_facts.union_iff in H. simpl in H. fsetdec'.
      exists exA. rewr. fsetdec'.
    + destr. rewr*.
      forwards<: IHdsub. exists exA. apply DTyPS_facts.union_iff in H. destr. assumption. assert ((exA, dty) = (e, d)). fsetdec''. crush.
      fsetdec'.
Qed.

Theorem DSub_sub_codom : forall (dsub1 dsub2 : DSub),
    dsub1 [<=]ds  dsub2
  -> dsub1 [<=]dsc dsub2.
Proof.
  autounfold. rewr. unfold DTyPSI.Subset, DTySI.Subset. intros dsub1 dsub2 SUB__ds dty IN.
  apply in_codom_in_bindings in IN. destruct IN as [exA IN]. apply in_codom_in_bindings. exists exA. auto.
Qed.
#[export] Hint Resolve DSub_sub_codom : core.

(** DSub_eq *)
(* Def *)
Definition DSub_eq (dsub1 dsub2 : DSub) :=
   DSub_bindings dsub1 ⟪=⟫ DSub_bindings dsub2.
#[export] Hint Unfold DSub_eq : core.

Notation "A [=]ds B" := (DSub_eq A B) (at level 65, format "A  [=]ds  B").

(* Instance *)
Lemma DSub_eq_refl : Reflexive DSub_eq.
Proof. autounfold. crush. Qed.
Lemma DSub_eq_trans : Transitive DSub_eq.
Proof. autounfold. crush. Qed.
Lemma DSub_eq_symm : Symmetric DSub_eq.
Proof. autounfold. crush. Qed.
#[export] Hint Resolve DSub_eq_refl DSub_eq_symm : core.

Theorem DSub_eq_app : forall (dsub1 dsub1' dsub2 dsub2' : DSub),
    dsub1 [=]ds dsub1'
  -> dsub2 [=]ds dsub2'
  -> dsub1 ++ dsub2 [=]ds dsub1' ++ dsub2'.
Proof. autounfold. intros. rewr. fsetdec'. Qed.
#[export] Hint Resolve DSub_eq_app : core.
#[export] Instance DSub_eq_app_proper : Proper (DSub_eq ==> DSub_eq ==> DSub_eq) (app (A:=(atom*DTy))).
Proof. eauto. Qed.

Module DSub_eq_eqrel <: list_eqrel.
  Definition elt := (atom * DTy).
  Definition R : list elt -> list elt -> Prop := DSub_eq.

  Definition refl  : Reflexive  R := DSub_eq_refl.
  Definition trans : Transitive R := DSub_eq_trans.
  Definition symm  : Symmetric  R := DSub_eq_symm.

  Definition proper : Proper (R ==> R ==> R) (app (A := elt)) := DSub_eq_app_proper.
End DSub_eq_eqrel.

Module Export DSub_eq_eqrel_facts := list_eqrel_facts DSub_eq_eqrel.
#[export] Hint Extern 1 (DSub_eq _ _) => fold DSub_eq_eqrel.R : core.

(* Conversions *)
Theorem DSub_eq_sub : forall (dsub1 dsub2 : DSub),
    dsub1 [=]ds dsub2
  -> dsub1 [<=]ds dsub2.
Proof. autounfold. crush. Qed.
#[export] Hint Resolve DSub_eq_sub : core.

Theorem DSub_eq_codom : forall (dsub1 dsub2 : DSub),
    dsub1 [=]ds  dsub2
  -> dsub1 [=]dsc dsub2.
Proof. auto using DSub_codom_sub_eq. Qed.

Theorem DSub_eq_dom : forall (dsub1 dsub2 : DSub),
    dsub1 [=]ds  dsub2
  -> dsub1 [=]dsd dsub2.
Proof. auto using DSub_dom_sub_eq. Qed.

(*** rewr_dsrel *)
Ltac unfold_dsrel :=
           ( (try unfold DSub_sub     ); (try unfold DSub_sub     ); (try unfold DSub_codom_sub     )
           ; (try unfold DSub_eq      ); (try unfold DSub_eq      ); (try unfold DSub_codom_eq      ) ).
Tactic Notation "unfold_dsrel" "in" hyp(H) :=
           ( (try unfold DSub_sub in H); (try unfold DSub_sub in H); (try unfold DSub_codom_sub in H)
           ; (try unfold DSub_eq  in H); (try unfold DSub_eq  in H); (try unfold DSub_codom_eq  in H) ).
Tactic Notation "unfold_dsrel*" :=
           ( (try unfold DSub_sub in *); (try unfold DSub_sub in *); (try unfold DSub_codom_sub in *)
           ; (try unfold DSub_eq  in *); (try unfold DSub_eq  in *); (try unfold DSub_codom_eq  in *) ).

Ltac   fold_dsrel :=
           ( (try   fold DSub_sub     ); (try   fold DSub_sub     ); (try   fold DSub_codom_sub     )
           ; (try   fold DSub_eq      ); (try   fold DSub_eq      ); (try   fold DSub_codom_eq      ) ).
Tactic Notation "  fold_dsrel" "in" hyp(H) :=
           ( (try   fold DSub_sub in H); (try   fold DSub_sub in H); (try   fold DSub_codom_sub in H)
           ; (try   fold DSub_eq  in H); (try   fold DSub_eq  in H); (try   fold DSub_codom_eq  in H) ).
Tactic Notation "  fold_dsrel*" :=
           ( (try   fold DSub_sub in *); (try   fold DSub_sub in *); (try   fold DSub_codom_sub in *)
           ; (try   fold DSub_eq  in *); (try   fold DSub_eq  in *); (try   fold DSub_codom_eq  in *) ).

Ltac rewr_dsrel :=
  unfold_dsrel     ; progress (rewr     ); fold_dsrel     .
Tactic Notation "rewr_dsrel" "in" hyp(H) :=
  unfold_dsrel in H; progress (rewr in H); fold_dsrel in H.
Tactic Notation "rewr_dsrel*" :=
  unfold_dsrel*    ; progress (rewr*    ); fold_dsrel*    .

Ltac a_ind a :=
  let exA := fresh "exA" in
  induction a as [|exA a].
Ltac rev_a_ind a :=
  let exA := fresh "exA" in
  induction a as [|exA a] using rev_ind.

Ltac da_ind da :=
  let dskA := fresh "dskA" in
  induction da as [|dskA da].
Ltac rev_da_ind da :=
  let dskA := fresh "dskA" in
  let da  := fresh "da" in
  induction da as [|dskA da] using rev_ind.

(*** Well-formedness *)
(** DSub_WfDTy *)
Definition DSub_WfDTy (denv : DEnv) (dsub : DSub) := forall dty,
    SIn dty (DSub_codom dsub)
  -> denv |=dty (DS_Mono dty).
#[export] Hint Unfold DSub_WfDTy : core.

Theorem DSub_WfDTy_app : forall (dsub1 dsub2 : DSub) (denv : DEnv),
    DSub_WfDTy denv dsub1
  -> DSub_WfDTy denv dsub2
  -> DSub_WfDTy denv (dsub1 ++ dsub2).
Proof. unfold DSub_WfDTy. introv IN1 IN2 IN. rewr in IN. indestr; eauto. Qed.

Theorem DSub_WfDTy_rewr : forall (denv1 denv2 : DEnv) (dsub1 dsub2 : DSub),
    DSub_WfDTy denv1 dsub1
  -> denv1 [<=]de denv2
  -> dsub2 [<=]dsc dsub1
  -> DSub_WfDTy denv2 dsub2.
Proof. autounfold. intros. eapply WfDTy_DEnv_sub. apply H. crush. crush. Qed.
#[export] Hint Resolve DSub_WfDTy_rewr : core.
#[export] Instance DSub_WfDTy_rewr_proper : Proper (DEnv_sub ==> flip DSub_codom_sub ==> impl) DSub_WfDTy.
Proof. eauto. Qed.

Theorem DSub_WfDTy_empty : forall denv,
    DSub_WfDTy denv [].
Proof. unfold DSub_WfDTy. intros. fsetdec''. Qed.
#[export] Hint Resolve DSub_WfDTy_empty : core.

(** DSub_lc *)
Definition DSub_lc (dsub : DSub) := forall dty,
    SIn dty (DSub_codom dsub)
  -> lc_DTy dty.
#[export] Hint Unfold DSub_lc : core.

Theorem DSub_lc_sub : forall (dsub1 dsub2 : DSub),
    DSub_lc dsub1
  -> dsub2 [<=]dsc dsub1
  -> DSub_lc dsub2.
Proof. autounfold. intros. apply H; crush. Qed.
#[export] Hint Resolve DSub_lc_sub : core.
#[export] Instance DSub_lc_sub_proper : Proper (flip DSub_codom_sub ==> impl) DSub_lc.
Proof. eauto. Qed.

Theorem DSub_WfDTy_lc : forall (denv : DEnv) (dsub : DSub),
    DSub_WfDTy denv dsub
  -> DSub_lc dsub.
Proof. autounfold. introv WF IN. forwards: WF. eassumption. eauto. Qed.
#[export] Hint Resolve DSub_WfDTy_lc : core.

(** DSub_unique *)
Definition DSub_unique (dsub : DSub) := forall (dty1 dty2 : DTy) (exA : exvar),
    DTyPSI.In (exA, dty1) (DSub_bindings dsub)
  -> DTyPSI.In (exA, dty2) (DSub_bindings dsub)
  -> dty1 = dty2.
#[export] Hint Unfold DSub_unique : core.

Theorem DSub_unique_rewr : forall (dsub1 dsub2 : DSub),
    DSub_unique dsub1
  -> dsub2 [<=]ds dsub1
  -> DSub_unique dsub2.
Proof. autounfold. intros. applys H exA; fsetdec'. Qed.
#[export] Hint Resolve DSub_unique_rewr : core.
#[export] Instance DSub_unique_rewr_proper : Proper (flip DSub_sub ==> impl) DSub_unique.
Proof. eauto. Qed.

Theorem DSub_unique_empty :
    DSub_unique [].
Proof. unfold DSub_unique. intros. fsetdec''. Qed.
#[export] Hint Resolve DSub_unique_empty : core.

Theorem DSub_unique_app_symm : forall (dsub1 dsub2 : DSub),
    DSub_unique (dsub1 ++ dsub2)
  -> DSub_unique (dsub2 ++ dsub1).
Proof.
  unfold DSub_unique. introv UNI IN1 IN2. rewr*. applys UNI exA; rewr; fsetdec'. Qed.

Theorem DSub_unique_cons : forall (dsub : DSub) (exA : exvar) (dty : DTy),
    DSub_unique               dsub
  -> exA \notin DSub_dom dsub
  -> DSub_unique ((exA, dty) :: dsub).
Proof.
  unfold DSub_unique. introv UNI NIS IN1 IN2. rewr*. indestr.
  eauto.
  assert (exA0 \in DSub_dom dsub). eauto. crush.
  assert (exA0 \in DSub_dom dsub). eauto. crush.
  rewr*. crush.
Qed.


(** DSub_wf *)
Definition DSub_wf (denv : DEnv) (dsub : DSub) :=
    DSub_WfDTy denv dsub /\ DSub_unique dsub.
#[export] Hint Unfold DSub_wf : core.

(* Conversions *)
Theorem DSub_wf_WfDTy : forall (denv : DEnv) (dsub : DSub),
    DSub_wf denv dsub
  -> DSub_WfDTy denv dsub.
Proof. unfold DSub_wf. crush. Qed.
#[export] Hint Resolve DSub_wf_WfDTy : core.

Theorem DSub_wf_unique : forall (denv : DEnv) (dsub : DSub),
    DSub_wf denv dsub
  -> DSub_unique dsub.
Proof. unfold DSub_wf. crush. Qed.
#[export] Hint Resolve DSub_wf_unique : core.

Theorem DSub_wf_rewr : forall (denv1 denv2 : DEnv) (dsub1 dsub2 : DSub),
    DSub_wf denv1 dsub1
  -> denv1 [<=]de denv2
  -> dsub2 [<=]ds dsub1
  -> DSub_wf denv2 dsub2.
Proof. intros. split; eauto. Qed.
#[export] Hint Resolve DSub_wf_rewr : core.
#[export] Instance DSub_wf_rewr_proper : Proper (DEnv_sub ==> flip DSub_sub ==> impl) DSub_wf.
Proof. eauto. Qed.

Theorem DSub_WfDTy_membership : forall (denv : DEnv) (dsub : DSub) (dty : DTy),
    DSub_WfDTy denv dsub
  -> DTySI.In dty (DSub_codom dsub)
  -> denv |=dty (DS_Mono dty).
Proof. introv WF IN. apply WF. auto. Qed.
#[export] Hint Resolve DSub_WfDTy_membership : core.

Theorem DSub_wf_membership : forall (denv : DEnv) (dsub : DSub) (dty : DTy),
    DSub_wf denv dsub
  -> DTySI.In dty (DSub_codom dsub)
  -> denv |=dty (DS_Mono dty).
Proof. introv WF IN. eauto. Qed.
#[export] Hint Resolve DSub_wf_membership : core.


Theorem DSub_wf_snoc : forall (denv : DEnv) (dsub: DSub) (exA : exvar) (dty : DTy),
    DSub_wf denv dsub
  -> exA \notin DSub_dom dsub
  -> denv |=dty DS_Mono dty
  -> DSub_wf denv (dsub ++ [(exA, dty)]).
Proof.
  introv WF NIS WFDTY. split. apply DSub_WfDTy_app. eauto.
  unfold DSub_WfDTy. introv IN. rewr in IN. crush.
  apply DSub_unique_app_symm. simpl. apply DSub_unique_cons. eauto. eauto.
Qed.

(*** DSub_app(_t) *)
(** Simplification *)
Theorem DSub_app_t_sk_b : forall (dsub : DSub) (n : nat),
  DSub_app_t (T_SkVar_b n) dsub  = T_SkVar_b n.
Proof. induction dsub; crush. Qed.
#[export] Hint Rewrite DSub_app_t_sk_b : core dsub_simpl.

Theorem DSub_app_t_sk_f : forall (dsub : DSub) (skA : skvar),
  DSub_app_t (T_SkVar_f skA) dsub  = T_SkVar_f skA.
Proof. induction dsub; crush. Qed.
#[export] Hint Rewrite DSub_app_t_sk_f : core dsub_simpl.

Theorem DSub_app_t_unit : forall (dsub : DSub),
  DSub_app_t (T_Unit) dsub  = T_Unit.
Proof. induction dsub; crush. Qed.
#[export] Hint Rewrite DSub_app_t_unit : core dsub_simpl.

Theorem DSub_app_t_fun : forall (dsub : DSub) (t1 t2 : Ty),
    DSub_app_t (T_Fun t1 t2) dsub  = T_Fun (DSub_app_t t1 dsub) (DSub_app_t t2 dsub).
Proof.
Proof. induction dsub; crush. Qed.
#[export] Hint Rewrite DSub_app_t_fun : core dsub_simpl.

Theorem DSub_app_forall : forall (dsub : DSub) (sch : Sch),
    DSub_app (S_Forall sch) dsub  = S_Forall (DSub_app sch dsub).
Proof. induction dsub; crush. Qed.
#[export] Hint Rewrite DSub_app_forall : core dsub_simpl.

Theorem DSub_app_nil : forall (sch : Sch),
    DSub_app sch nil = sch.
Proof. induction sch; [induction Ty5|idtac]; crush. Qed.
#[export] Hint Rewrite DSub_app_nil : core dsub_simpl.

Theorem DSub_app_t_nil : forall (ty : Ty),
    DSub_app_t ty nil = ty.
Proof. induction ty; crush. Qed.
#[export] Hint Rewrite DSub_app_t_nil : core dsub_simpl.

Theorem DSub_app_mono : forall (dsub : DSub) (ty : Ty),
    DSub_app (S_Mono ty) dsub  = S_Mono (DSub_app_t ty dsub).
Proof. crush. Qed.
#[export] Hint Rewrite DSub_app_mono : core dsub_simpl.

Theorem DSub_app_t_embed : forall (dsub : DSub) (dty : DTy),
    DSub_app_t (emb_Ty dty) dsub  = emb_Ty dty.
Proof. intros. induction dty; crush. Qed.
#[export] Hint Rewrite DSub_app_t_embed : core dsub_simpl.

Theorem DSub_app_embed : forall (dsub : DSub) (dsch : DSch),
    DSub_app (emb_Sch dsch) dsub  = emb_Sch dsch.
Proof. intros. induction dsch; crush. Qed.
#[export] Hint Rewrite DSub_app_embed : core dsub_simpl.

(** notin sub *)
Theorem DSub_app_t_exA_notinsub : forall (exA : exvar) (dsub : DSub),
    exA \notin DSub_dom dsub
  -> DSub_app_t (T_ExVar exA) dsub  = T_ExVar exA.
Proof. induction dsub. crush. destruct a. intros. crush.
       destruct (exA == e). false. crush. crush. Qed.

(** Subdist *)
Theorem DSub_app_t_singleton : forall (dty : DTy) (exA : exvar) (ty : Ty),
    DSub_app_t ty [(exA, dty)] = subst_exvar_Ty (emb_Ty dty) exA ty.
Proof. crush. Qed.
#[export] Hint Rewrite DSub_app_t_singleton : subdist.

Theorem DSub_app_singleton : forall (dty : DTy) (exA : exvar) (sch : Sch),
    DSub_app sch [(exA, dty)] = subst_exvar_Sch (emb_Ty dty) exA sch.
Proof. induction sch; crush. Qed.
#[export] Hint Rewrite DSub_app_singleton : subdist.

Theorem DSub_app_t_app_distr : forall (dsub1 dsub2 : DSub) (ty : Ty),
    DSub_app_t ty (dsub2 ++ dsub1) = DSub_app_t (DSub_app_t ty dsub1) dsub2.
Proof. induction dsub2; simpl; crush. Qed.
#[export] Hint Rewrite DSub_app_t_app_distr : subdist.

Theorem DSub_app_app_distr : forall (dsub1 dsub2 : DSub) (sch : Sch),
    DSub_app sch (dsub2 ++ dsub1) = DSub_app (DSub_app sch dsub1) dsub2.
Proof.
  induction dsub2; simpl; crush.
  Sch_Ty_ind sch; rewr; crush.
  subdist. reflexivity.
Qed.
#[export] Hint Rewrite DSub_app_app_distr : subdist.

Theorem DSub_app_t_cons_distr : forall (dty : DTy) (exA : exvar) (dsub : DSub) (ty : Ty),
    DSub_app_t ty ((exA, dty) :: dsub) = subst_exvar_Ty (emb_Ty dty) exA (DSub_app_t ty dsub).
Proof. intros. simpl. rewr. reflexivity. Qed.
#[export] Hint Rewrite DSub_app_t_cons_distr : subdist.

Theorem DSub_app_cons_distr : forall (dty : DTy) (exA : exvar) (dsub : DSub) (sch : Sch),
    DSub_app sch ((exA, dty) :: dsub) = subst_exvar_Sch (emb_Ty dty) exA (DSub_app sch dsub).
Proof. induction sch. subdist. reflexivity. crush. Qed.
#[export] Hint Rewrite DSub_app_cons_distr : subdist.

(** exA location *)
Lemma DSub_app_t_exA_decide : forall (dsub : DSub) (exA : exvar),
    ( DSub_app_t (T_ExVar exA) dsub = T_ExVar exA
    /\ exA \notin DSub_dom dsub )
  \/ ( exists dty,
      DSub_app_t (T_ExVar exA) dsub = emb_Ty dty
    /\ DTyPSI.In (exA, dty) (DSub_bindings dsub)
    ).
Proof.
  intros. DSub_ind dsub. left. crush.
  destr.
  - subdist. rewrite H. simpl. ifdec'.
    + right. eexists. splits; jauto. rewr*. fsetdec.
    + left. split. auto. rewr. fsetdec.
  - right. eexists; jauto. split. subdist. crush. crush.
Qed.

Ltac do_DSub_exA_decide DSub exA :=
      let H := fresh "H" in
      forwards H: DSub_app_t_exA_decide DSub exA
      ; destruct H as [[?INV ?NIS] | [?dty [?EMB ?IN]]].

Ltac DSub_exA_decide :=
    match goal with
  | [ H : context[DSub_app_t (T_ExVar ?exA) ?dsub] |- _ ] =>
      do_DSub_exA_decide dsub exA
  | [ |- context[DSub_app_t (T_ExVar ?exA) ?dsub] ] =>
      do_DSub_exA_decide dsub exA
  end.

Definition DSub_full_t (ty : Ty) (dsub : DSub) :=
    free_exvars_Ty ty [<=] DSub_dom dsub.
#[export] Hint Unfold DSub_full_t : core.

Definition DSub_full (sch : Sch) (dsub : DSub) :=
    free_exvars_Sch sch [<=] DSub_dom dsub.
#[export] Hint Unfold DSub_full : core.

Theorem DSub_full_t_fun : forall (ty1 ty2 : Ty) (dsub : DSub),
    DSub_full_t (T_Fun ty1 ty2) dsub
  -> DSub_full_t ty1 dsub
  /\ DSub_full_t ty2 dsub.
Proof. unfold DSub_full_t. intros. rewr in H. split; fsetdec. Qed.
Corollary DSub_full_t_fun1 : forall (ty1 ty2 : Ty) (dsub : DSub),
    DSub_full_t (T_Fun ty1 ty2) dsub
  -> DSub_full_t ty1 dsub.
Proof. apply DSub_full_t_fun. Qed.
Corollary DSub_full_t_fun2 : forall (ty1 ty2 : Ty) (dsub : DSub),
    DSub_full_t (T_Fun ty1 ty2) dsub
  -> DSub_full_t ty2 dsub.
Proof. apply DSub_full_t_fun. Qed.
#[export] Hint Resolve DSub_full_t_fun1 DSub_full_t_fun2 : core.

Theorem DSub_full_t_exA : forall (exA : var) (dsub : DSub),
    DSub_full_t (T_ExVar exA) dsub
  -> exA \in DSub_dom dsub.
Proof. intros. unfold DSub_full_t in H. crush. Qed.
#[export] Hint Resolve DSub_full_t_exA : core.

Theorem in_DSub_emb : forall (exA : exvar) (dsub : DSub),
    exA \in DSub_dom dsub
  <-> exists dty, DSub_app_t (T_ExVar exA) dsub = emb_Ty dty.
Proof.
  rev_DSub_ind dsub. crush. destruct x; inverts H.
  destruct (exA0 == exA).
  - subst; split; intros.
    + exists dty. subdist. crush.
    + rewr. fsetdec.
  - split; intros.
    + subdist. simpl. if_taut. apply IHdsub0.
      rewr in H. forwards>: union_iff. eassumption. destr. assumption. fsetdec.
    + destruct H as [dty' EMB]. rewr in EMB. forwards<: IHdsub0. exists dty'. subdist in EMB. simpl in EMB. if_taut.
      rewr. fsetdec.
Qed.

Theorem DSub_full_t_emb : forall (dsub : DSub) (ty : Ty),
    DSub_full_t ty dsub <-> exists dty, DSub_app_t ty dsub = emb_Ty dty.
Proof.
  induction ty; split; intros. 2,4,8:crush.
  - exists (DT_SkVar_b n). rewr. auto.
  - exists (DT_SkVar_f skA). rewr. auto.
  - apply in_DSub_emb. eauto.
  - unfold DSub_full_t. rewr.
    forwards<: in_DSub_emb. eassumption.
    fsetdec.
  - exists (DT_Unit). rewr. auto.
  - forwards> [dty1 EMB1]: IHty1. eauto.
    forwards> [dty2 EMB2]: IHty2. eauto.
    exists (DT_Fun dty1 dty2). rewr. crush.
  - destruct H as [dty EMB]. emb_auto.
    forwards<: IHty1. eauto.
    forwards<: IHty2. eauto.
    unfold DSub_full_t in *. rewr. fsetdec.
Qed.

Theorem DSub_fullb_emb : forall (dsub : DSub) (sch : Sch),
    DSub_full sch dsub
  -> exists dsch, DSub_app sch dsub = emb_Sch dsch.
Proof.
  introv FULL. induction sch.
  - forwards> [dty EMB]: DSub_full_t_emb. eauto.
    exists (DS_Mono dty). crush.
  - forwards [dsch EMB]: IHsch. auto.
    exists (DS_Forall dsch). crush.
Qed.

(** Rewriting *)
Theorem in_DSub_unique_app : forall (exA : exvar) (dty : DTy) (dsub : DSub),
    DTyPSI.In (exA, dty) (DSub_bindings dsub)
  -> DSub_unique dsub
  -> DSub_app_t (T_ExVar exA) dsub = emb_Ty dty.
Proof.
  introv IN UNI. rev_DSub_ind dsub. crush.
  destruct (exA0 == exA).
  - subst.
    forwards: UNI dty dty0. eassumption. rewr. fsetdec'.
    subdist. crush.
  - subdist. simpl. if_taut. apply IHdsub0. 2:eauto.
    rewr in IN. forwards>: DTyPS_facts.union_iff. eassumption. destr. assumption.
    assert (exA = exA0). crush. crush.
Qed.

Theorem DSub_unique_sub_DSub_app_t : forall (dsub1 dsub2 : DSub) (ty : Ty),
    DSub_full_t ty dsub1
  -> dsub1 [<=]ds dsub2
  -> DSub_unique dsub2
  -> DSub_app_t ty dsub1 = DSub_app_t ty dsub2.
Proof.
  intros. induction ty; try (rewr; reflexivity).
  - DSub_exA_decide. assert (exA \in DSub_dom dsub1). auto. fsetdec.
    forwards: in_DSub_unique_app dsub2. eauto. assumption. crush.
  - rewr.
    forwards: IHty1. eauto.
    forwards: IHty2. eauto.
    crush.
Qed.

Theorem DSub_unique_sub_DSub_app : forall (dsub1 dsub2 : DSub) (sch : Sch),
    DSub_full sch dsub1
  -> dsub1 [<=]ds dsub2
  -> DSub_unique dsub2
  -> DSub_app sch dsub1 = DSub_app sch dsub2.
Proof.
  intros. induction sch; rewr.
  erewrite DSub_unique_sub_DSub_app_t; eauto.
  erewrite IHsch; eauto.
Qed.

Theorem DSub_unique_eq_DSub_app_t : forall (dsub1 dsub2 : DSub) (ty : Ty),
    dsub1 [=]ds dsub2
  -> DSub_unique dsub2
  -> DSub_app_t ty dsub1 = DSub_app_t ty dsub2.
Proof.
  intros. induction ty; try (rewr; reflexivity).
  - DSub_exA_decide.
    + rewrite DSub_app_t_exA_notinsub. rewrite DSub_app_t_exA_notinsub. reflexivity.
      forwards: DSub_eq_dom. eassumption. unfold DSub_dom_eq in H1. rewrite <- H1. eassumption.
      assumption.
    + forwards: in_DSub_unique_app dsub2. unfold DSub_eq in H. rewrite <- H. eassumption. eassumption. crush.
  - rewr.
    forwards: IHty1. eauto.
    forwards: IHty2. eauto.
    crush.
Qed.

Corollary DSub_app_t_app_symm : forall (dsub1 dsub2 : DSub) (ty : Ty),
    DSub_unique (dsub1 ++ dsub2)
  -> DSub_app_t ty (dsub1 ++ dsub2) = DSub_app_t ty (dsub2 ++ dsub1).
Proof. introv UNI. apply DSub_unique_eq_DSub_app_t. rewr_dsrel. fsetdec'. apply DSub_unique_app_symm. assumption. Qed.


(*** DSub open comm *)
Theorem DSub_app_open_comm : forall (dsub: DSub) (sch : Sch) (ty : Ty),
    lc_Ty ty
  -> DSub_lc dsub
  -> DSub_app (open_Sch_wrt_Ty sch ty) dsub = open_Sch_wrt_Ty (DSub_app sch dsub) (DSub_app_t ty dsub).
Proof.
  introv LC. unfold open_Sch_wrt_Ty. unfold open_Sch_wrt_Ty_rec. generalize 0. fold open_Sch_wrt_Ty_rec.
  Sch_Ty_ind sch; intros.
  - simpl. subdist. ltdec.
    + ifdec; simpl; ltdec; crush.
    + unfold open_Sch_wrt_Ty. simpl.
      ltdec; crush.
  - crush.
  - do_DSub_exA_decide dsub exA.
    + crush.
    + assert (lc_DTy dty). eauto.
      crush.
      rewrite open_Ty_wrt_Ty_lc_Ty_rec; crush.
  - crush.
  - forwards IH1: IHTy1 n. assumption. forwards IH2: IHTy2 n. assumption.
    simpl in *. subdist*.
    crush.
  - simpl. crush.
Qed.

(*** DSub + close *)
Theorem close_Ty_wrt_Ty_rec_involuntive : forall (n : nat) (skA : skvar) (ty : Ty),
    lc_Ty ty
  -> skA \notin free_skvars_Ty ty
  -> close_Ty_wrt_Ty_rec n skA ty = ty.
Proof. crush. Qed.



Theorem free_skvars_Ty_DSub_codom_dskvars : forall (dty : DTy) (dsub : DSub),
    DTySI.In dty (DSub_codom dsub)
  -> free_skvars_Ty (emb_Ty dty) [<=] DSub_codom_dskvars dsub.
Proof.
  introv IN. induction dsub. crush. rewr*.
  indestr. transitivity (DSub_codom_dskvars dsub). eauto. rewr. fsetdec'.
  rewrite free_skvars_Ty_embed_Ty. fsetdec.
Qed.

Theorem DSub_app_close_Sch_wrt_Ty : forall (dsub : DSub) (skA : skvar) (sch : Sch),
    skA \notin DSub_codom_dskvars dsub
  -> (exists (denv : DEnv), DSub_wf denv dsub)
  -> DSub_app (close_Sch_wrt_Ty skA sch) dsub = close_Sch_wrt_Ty skA (DSub_app sch dsub).
Proof.
  introv NID WFS. unfold close_Sch_wrt_Ty. generalize 0. Sch_Ty_ind sch; intros.
  4,6:crush.
  - simpl. ltdec; crush; ltdec; crush.
  - simpl. ifdec. crush. if_taut. crush. if_taut.
  - do_DSub_exA_decide dsub exA.
    + crush.
    + crush.
      rewrite close_Ty_wrt_Ty_rec_involuntive. crush.
      apply emb_Ty_lc. eauto.
      unfold not. intro. apply NID. rewrite <- free_skvars_Ty_DSub_codom_dskvars. eassumption. eauto.
  - forwards IH1: IHTy1 n. inverts IH1.
    forwards IH2: IHTy2 n. inverts IH2.
    crush.
Qed.

(*** dskvars_codom *)

Theorem In_DSub_codom_dskvars : forall (dsub : DSub) (dty : DTy),
    DTySI.In dty (DSub_codom dsub)
  -> free_dskvars_DTy dty [<=] DSub_codom_dskvars dsub.
Proof.
  introv IN. DSub_ind dsub. crush.
  rewr in IN. indestr. rewr. rewrite IHdsub0. fsetdec. assumption. rewr. fsetdec.
Qed.

Theorem DSub_app_susbst_skvar_Sch : forall (dsub : DSub) (ty : Ty) (dskA : dskvar) (sch : Sch),
    dskA \notin DSub_codom_dskvars dsub
  -> DSub_app (subst_skvar_Sch ty dskA sch) dsub = subst_skvar_Sch (DSub_app_t ty dsub) dskA (DSub_app sch dsub).
Proof.
  introv NIS. Sch_Ty_ind sch. 1,4,5,6:crush.
  - rewr. simpl. ifdec; crush.
  - rewr. DSub_exA_decide.
    + crush.
    + assert (dskA \notin free_skvars_Ty (emb_Ty dty)).
      { rewrite free_skvars_Ty_embed_Ty.
        rewrite In_DSub_codom_dskvars. eassumption. eauto.
      }
      crush. rewrite subst_skvar_Ty_not_in_Ty_idempotent; auto.
Qed.

(*** Unsorted *)
Theorem DSub_app_lc : forall (sch : Sch) (dsub : DSub),
    lc_Sch sch
  -> (exists (denv : DEnv), DSub_WfDTy denv dsub)
  -> lc_Sch (DSub_app sch dsub).
Proof.
  introv LC [denv WFSUB]. LC_ind LC; inv_LC; subdist; auto.
  - DSub_exA_decide. crush.
    rewrite EMB.
    apply emb_Ty_lc. eauto.
  - forwards: IHLC__ty1. assumption.
    forwards: IHLC__ty2. assumption.
    inv_LC. crush.
  - constructor. intros.
    forwards IH: H0 skA. rewrite DSub_app_open_comm in IH. crush. auto. eauto.
Qed.

Theorem embed_Ty_WfDTy : forall (denv : DEnv) (dsub : DSub) (ty : Ty) (dty : DTy),
    DSub_WfDTy denv dsub
  -> DSub_app_t ty dsub = emb_Ty dty
  -> free_skvars_Ty ty [<=] DEnv_dskvars denv
  -> lc_Ty ty
  -> denv |=dty (DS_Mono dty).
Proof.
  introv SUB__wfdty EMB SUB__sk LC. gen dty; induction ty; intros; emb_auto.
  - inverts LC.
  - constructor. rewr in SUB__sk. fsetdec.
  - DSub_exA_decide. rewrite INV in EMB. emb_auto. crush.
    apply SUB__wfdty. rewrite EMB in EMB0. apply emb_Ty_inj in EMB0. inverts EMB0. eauto.
  - auto.
  - rewr in SUB__sk. inverts LC.
    forwards: IHty1. eauto. fsetdec. auto. eassumption.
    forwards: IHty2. eauto. fsetdec. auto. eassumption.
    crush.
Qed.

Theorem DSub_WfDTy_codom_in_DEnv : forall denv dsub,
    DSub_WfDTy denv dsub
  -> DSub_codom_dskvars dsub [<=] DEnv_dskvars denv.
Proof.
  intros. induction dsub. crush.
  forwards: IHdsub. eauto. rewr. rewrite H0. destruct a.
  forwards: H. rewr. instantiate (1 := d). fsetdec'.
  apply WfDTy_props in H1. destr. rewrite H1. fsetdec.
Qed.

Theorem DSub_unique_app_proj1 : forall (dsub1 dsub2 : DSub),
    DSub_unique (dsub1 ++ dsub2)
  -> DSub_unique  dsub1.
Proof. eauto. Qed.
#[export] Hint Resolve DSub_unique_app_proj1 : core.
Theorem DSub_unique_app_proj2 : forall (dsub1 dsub2 : DSub),
    DSub_unique (dsub1 ++ dsub2)
  -> DSub_unique           dsub2.
Proof. eauto. Qed.
#[export] Hint Resolve DSub_unique_app_proj2 : core.
