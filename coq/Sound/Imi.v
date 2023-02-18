(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.
Require Import Defs.Defs.

Require Import Wf.Wf.

Require Import Sound.Umi.

Definition inference_maintains_instantiation__def := forall (env__in : Env) (e : e) (a : A) (ty : Ty) (env__out : Env) (n : nat) (denv : DEnv),
    env__in |= e ▸ ⟨a⟩ ty =| env__out
  -> wf(env__in)
  -> FullEInst (Env_drop n env__out) denv
  -> FullEInst (Env_drop n env__in ) denv.

Definition inference_maintains_instantiation__prop (env__in : Env) (e : e) (a : A) (ty : Ty) (env__out : Env)
                                                 (inf : Inf env__in e a ty env__out) : Prop :=
  forall n denv,
    wf(env__in)
  -> FullEInst (Env_drop n env__out) denv
  -> FullEInst (Env_drop n env__in ) denv.
#[export] Hint Unfold inference_maintains_instantiation__def inference_maintains_instantiation__prop : core.

Definition generalization_maintains_instantiation__def := forall (env__in : Env) (e : e) (sch : Sch) (env__out : Env) (n : nat) (denv : DEnv),
    env__in |= e ▸ sch =| env__out
  -> wf(env__in)
  -> FullEInst (Env_drop n env__out) denv
  -> FullEInst (Env_drop n env__in ) denv.
Definition generalization_maintains_instantation__prop (env__in : Env) (e : e) (sch : Sch) (env__out : Env)
                                                      (gen : Gen env__in e sch env__out) : Prop := forall n denv,
    wf(env__in)
  -> FullEInst (Env_drop n env__out) denv
  -> FullEInst (Env_drop n env__in ) denv.
#[export] Hint Unfold generalization_maintains_instantiation__def generalization_maintains_instantation__prop : core.

Theorem imi_gmi :
  inference_maintains_instantiation__def /\ generalization_maintains_instantiation__def.
Proof.
  forwards: (Inf_Gen_mut inference_maintains_instantiation__prop
                         generalization_maintains_instantation__prop)
  ; unfold inference_maintains_instantiation__prop in *; unfold generalization_maintains_instantation__prop in *.

  7:{ jauto. }

  - crush.

  - crush.

  - introv FR INF IH WF__in [Sub INST__out].
    fresh_atom.
    (**)
    forwards INST__in: IH (Nat.add 2 n). eassumption. constructor. constructor. auto.
      constructor. auto. crush. constructor. crush.
      simpl. econstructor. eassumption. simpl in INST__in.
    (**)
    assumption.

  - introv FR INF__e1 IH__e1 INF__e2 IH__e2 UNI WF__in [Sub INST__out].
    forwards WF1: Inf_Wf. eapply INF__e1. assumption.
    forwards WF2: Inf_Wf. eapply INF__e2. assumption.
    (**)
    forwards INST2: unification_maintains_instantiation__drop (Nat.add 2 n). eassumption. simpl.
      eexists. eassumption. constructor. constructor. eauto. norm. apply FrA_app_split. split.
      constructor. auto. crush. inv_Wf. apply FrA_app_split. split. rewrite <- FrA_Obj. eassumption. assumption. auto.
      constructor. crush.
    forwards INST1: IH__e2 (Nat.add 1 n). assumption. simpl. eassumption. simpl in INST1.
    forwards INSTin: IH__e1 n. eauto. eassumption.
    (**)
    assumption.

  - introv GEN IH__e1 INF IH__e2 WF__in [Sub INST__out].
    fresh_atom.
    (**)
    forwards WF: Gen_Wf. eassumption. assumption.
    forwards: Inf_Wf. eapply INF. eassumption. eauto with slow.
    (**)
    forwards INST: IH__e2 (Nat.add 1 n). eassumption. eauto with slow. simpl. exists. eassumption. simpl in INST.
    forwards INST__in: IH__e1 n. eassumption. eassumption.
    (**)
    assumption.

  - crush.
Qed.

Theorem inference_maintains_instantiation : forall (env__in : Env) (e : e) (a : A) (ty : Ty) (env__out : Env) (denv : DEnv),
    env__in |= e ▸ ⟨a⟩ ty =| env__out
  -> wf(env__in)
  -> FullEInst env__out denv
  -> FullEInst env__in  denv.
Proof.
  introv INF WF INST. forwards IMI: proj1 imi_gmi. unfold inference_maintains_instantiation__def in IMI.
  forwards: IMI 0. eassumption. assumption. simpl. eassumption. crush.
Qed.

Theorem generalization_maintains_instantation : forall (env__in : Env) (e : e) (sch : Sch) (env__out : Env) (denv : DEnv),
    env__in |= e ▸ sch =| env__out
  -> wf(env__in)
  -> FullEInst env__out denv
  -> FullEInst env__in  denv.
Proof.
  introv INF WF INST. forwards GMI: proj2 imi_gmi. unfold generalization_maintains_instantiation__def in GMI.
  forwards: GMI 0. eassumption. assumption. simpl. eassumption. crush.
Qed.
