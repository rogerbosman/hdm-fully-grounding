(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.
Require Import Defs.Defs.

(*** Lemmas *)
Lemma inst_props : forall env sch a ty,
    env |= sch ≤ ⟨a⟩ ty
  -> lc_Sch sch
  -> FrA a env
  /\ free_exvars_Ty ty [<=] free_exvars_Sch sch \u varl a
  /\ free_skvars_Ty ty [<=] free_skvars_Sch sch
  /\ lc_Ty ty.
Proof.
  introv INST LC. induction INST. crush.
  fresh_atom' (free_skvars_Sch Sch5 \u L).
  forwards [FRA [IN__ex [IN__sk LC']]]: H x. fsetdec. inverts LC. apply subst_skvar_Sch_lc_Sch; eauto.
  splits.
  - apply FrA_app_split. split. jauto. constructor. auto. rewr. assumption.
  - rewrite IN__ex. simpl.
    rewrite free_exvars_Sch_subst_skvar_Sch_upper. rewrite free_exvars_Sch_open_Sch_wrt_Ty_upper. rewr. fsetdec.
  - rewrite IN__sk. simpl.
    rewrite free_skvars_Sch_subst_skvar_Sch_upper. rewr.
    rewrite free_skvars_Sch_open_Sch_wrt_Ty_upper. rewr.
    fsetdec.
  - assumption.
Qed.

(*** Main theorem *)
Theorem Inst_Wf : forall (env : Env) (sch : Sch) (a : A) (ty : Ty),
    env |= sch ≤ ⟨a⟩ ty
  -> wf(env)
  -> env |=ty sch
  -> wf(env ::o ⟦⟨a⟩ S_Mono ty⟧).
Proof.
  introv INST WF WFTY. apply WfTy_props in WFTY. destruct WFTY as [IN__ex1 [IN__sk1 LC1]].
  (*Remove arg pass to inst_props *)
  forwards [FR [IN__ex2 [IN__sk2 LC2]]]: inst_props. 1,2: eassumption.
  constructor; try assumption. apply WfTy_props. splits.
  - transitivity (free_skvars_Sch sch); crush.
  - rewrite IN__ex2. crush.
  - eauto.
Qed.
