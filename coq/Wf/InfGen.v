(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.
Require Import Defs.Defs.

Require Import Wf.Inst.
Require Import Wf.U.

(*** Main theorem *)
Definition Inf_Wf__def := forall (env__in : Env) (e : e) (a : A) (ty : Ty) (env__out : Env),
    env__in |= e ▸ ⟨a⟩ ty =| env__out
  -> wf(env__in)
  -> wf(env__out ::o ⟦⟨a⟩ S_Mono ty⟧).

Definition Gen_Wf__def := forall (env__in : Env) (e : e) (sch : Sch) (env__out : Env),
    env__in |= e ▸ sch =| env__out
  -> wf(env__in)
  -> wf(env__out ::o ⟦sch⟧).


Theorem Inf_Gen_Wf :
  Inf_Wf__def /\ Gen_Wf__def.
Proof.
  apply Inf_Gen_mut. 2:auto.

  - introv IN INST WF. eapply Inst_Wf. eassumption. assumption. eapply in_wf_env_impls_wf. eauto. auto.

  - introv FR INF IH WF__in.
    fresh_atom.
    (**)
    forwards WF__out: IH. eassumption. constructor. constructor. assumption. constructor; crush. constructor. crush.
    inv_Wf.
    constructor. assumption. apply FrA_app_split. eauto. constructor.
    eauto. eapply WfTy_Env_sub. eassumption. rewr. unfold_erel. rewr. split; fsetdec.

  - introv FR INFe1 IH__e1 INFe2 IH__e2 UNI WF__in.
    forwards WF1: IH__e1; auto.
    forwards WF2: IH__e2. assumption.
    forwards WF__out: U_Wf. eassumption.
      constructor. constructor. eauto.
      simpl. constructor. 2:crush. inv_Wf. apply FrA_app_split. split. 2: assumption.
      eapply FrA_Obj. eassumption.
      auto. constructor. crush.
    auto using wf_Env_Obj_move_a1.

  - introv GEN IH__e1 INF IH__e2 WF__in.
    forwards WF1: IH__e1. assumption.
    fresh_atom.
    forwards WF2: IH__e2. eassumption. eauto with slow. inv_Wf. constructor. assumption. eauto.
    eapply WfTy_Env_sub. eassumption. unfold_erel. rewr. split; fsetdec.

  - introv MON IH GEN WF__in.
    forwards WF__out: IH. assumption.
    constructor. eauto. auto. rewr. subst. apply generalize_Wf. eauto.
Qed.
