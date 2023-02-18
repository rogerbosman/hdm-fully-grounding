
(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Defs.DEnv.
Require Import Defs.DFra.
Require Import Defs.List.

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

  - introv FR MON IH GEN SUB. econstructor.
    (** HOLE! We have quantified over the list of a too strongly, it needs to be
    cofinitely quantified at the minimum *)
    admit. eapply IH. crush. eassumption.
Admitted.

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
