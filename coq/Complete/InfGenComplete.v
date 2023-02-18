(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.
Require Import Defs.Defs.

Require Import Complete.DEnvComplRel.
Require Import Complete.Sch_or_Obj.



Definition Inf_complete__def := forall (denv : DEnv) (e : e) (dty : DTy)   (denv__obj : DEnv) (env__in : Env) (a__in : A),
    denv |=m e ▸ dty
  -> FullEInst (env__in ::a a__in) denv__obj
  -> denv__obj ≦ denv
  -> wf(env__in)
  -> Sch_or_Obj env__in
  -> NonNil a__in
  -> exists env__out a ty denv__obj' da',
      env__in |= e ▸ ⟨a⟩ ty =| env__out
    /\ FullEInst (env__out ::a a ::o ⟦S_Mono ty⟧ ::a a__in) (denv__obj' :::o ⟦DS_Mono dty⟧d :::a da')
    /\ denv__obj = denv__obj' :::a da'.

Definition Inf_complete__prop (denv : DEnv) (e : e) (dty : DTy)
                            (mon : denv |=m e ▸ dty) : Prop := forall  (denv__obj : DEnv) (env__in : Env) (a__in : A),
    FullEInst (env__in ::a a__in) denv__obj
  -> denv__obj ≦ denv
  -> wf(env__in)
  -> Sch_or_Obj env__in
  -> NonNil a__in
  -> exists env__out a ty denv__obj' da',
      env__in |= e ▸ ⟨a⟩ ty =| env__out
    /\ FullEInst (env__out ::a a ::o ⟦S_Mono ty⟧ ::a a__in) (denv__obj' :::o ⟦DS_Mono dty⟧d :::a da')
    /\ denv__obj = denv__obj' :::a da'.
#[export] Hint Unfold Inf_complete__def Inf_complete__prop : core.

Definition Gen_complete__def := forall (denv : DEnv) (e : e) (dsch : DSch)   (denv__obj : DEnv) (env__in : Env) (a__in : A),
    denv |=p e ▸ dsch
  -> denv__obj ≦ denv
  -> FullEInst (env__in ::a a__in) denv__obj
  -> wf(env__in)
  -> Sch_or_Obj env__in
  -> NonNil a__in
  -> exists env__out sch dsch' denv__obj' da',
      env__in |= e ▸ sch =| env__out
    /\ FullEInst (env__out ::o ⟦sch⟧ ::a a__in) (denv__obj' :::o ⟦dsch'⟧d :::a da')
    /\ SubSump denv__obj dsch' dsch
    /\ denv__obj = denv__obj' :::a da'.

Definition Gen_complete__prop (denv : DEnv) (e : e) (dsch : DSch)
                            (gen : denv |=p e ▸ dsch) : Prop := forall (denv__obj : DEnv) (env__in : Env) (a__in : A),
    denv__obj ≦ denv
  -> FullEInst (env__in ::a a__in) denv__obj
  -> wf(env__in)
  -> Sch_or_Obj env__in
  -> NonNil a__in
  -> exists env__out sch dsch' denv__obj' da',
      env__in |= e ▸ sch =| env__out
    /\ FullEInst (env__out ::o ⟦sch⟧ ::a a__in) (denv__obj' :::o ⟦dsch'⟧d :::a da')
    /\ SubSump denv__obj dsch' dsch
    /\ denv__obj = denv__obj' :::a da'.
#[export] Hint Unfold Gen_complete__def Gen_complete__prop : core.
