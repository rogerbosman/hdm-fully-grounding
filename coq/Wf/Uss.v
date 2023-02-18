(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.
Require Import Defs.Defs.

(** Unfortunately I did not find a notation that works two ways *)
Notation  "A |= B -> C |= D , E"       := (Uss A B C D E)   (at level 50) : type_scope.

(*** lemmas *)
(** subst *)
Lemma Uss_Wf_subst_WfTy : forall (env2 env1 : Env) (exA : exvar) (a1 a2 : A) (sch : Sch) (ty : Ty),
    (env1 ::a (a2 ++ exA :: a1) +++ env2) |=ty sch
  -> env1 ::a a1 |=ty (S_Mono ty)
  -> (subst_exvar_Env ty exA env1 ::a (a2 ++ a1) +++ subst_exvar_Env ty exA env2) |=ty subst_exvar_Sch ty exA sch.
Proof.
  introv WF__sch WF__ty. forwards: WfTy_subst (subst_exvar_Env ty exA (env1 ::a (a2 ++ a1) +++ env2)) sch exA. eassumption.
  rewr. fsetdec. rewr. fsetdec. apply WfTy_props. apply WfTy_props in WF__ty. rewr*. splits; destr. crush. crush. assumption.
  eapply WfTy_Env_sub. eassumption. rewr. fsetdec.
Qed.

Theorem NoDup'_app_remove : forall (a1 a2 : A) (exA : exvar),
    NoDup' (a2 ++ exA :: a1)
  -> NoDup' (a2 ++ a1).
Proof.
  introv ND. induction a2. inverts ND. crush. inverts ND. constructor.
  rewr. unfold not in *. intros. apply H1. indestr; crush.
  rewr. eauto.
Qed.

Lemma Uss_Wf_subst : forall (env1 : Env) (a1 : A) (exA : exvar) (a2 : A) (env2 : Env) (ty : Ty),
    wf(env1 ::a (a2 ++ exA :: a1) +++ env2)
  -> env1 ::a a1 |=ty (S_Mono ty)
  -> wf(subst_exvar_Env ty exA (env1 ::a (a2 ++ a1) +++ env2)).
Proof.
  introv WF WFTY. simpl in *. induction env2.
  - rewr*. inv_Wf. rewrite subst_exvar_Env_notinenv. constructor. assumption.
    eapply FrA_sublist. eassumption. split. crush. intros. eauto using NoDup'_app_remove.
    inv_FrA. crush. assumption.
  - rewr*. inv_Wf.
  - simpl. constructor. eauto. induction A5.
    + auto.
    + rewr*. inv_Wf. eapply FrA_rewr. eassumption. eauto.
      do 2 rewrite subst_exvar_Env_subset.
      crush.
  - apply WfEnvSch. eauto. fold subst_exvar_Env.
    assert (subst_exvar_Env ty exA (env1::a (a2 ++ a1) +++ env2) |=ty subst_exvar_Sch ty exA Sch5).
    rewr. apply Uss_Wf_subst_WfTy. eauto. eauto.
    crush.
  - rewr*. destruct Obj5. simpl. inv_Wf. constructor.
    + rewr. auto.
    + eapply FrA_Env_sub. eassumption.
      do 2 rewrite subst_exvar_Env_subset.
      crush.
    + fold subst_exvar_Env. fold Env_app.
      forwards: Uss_Wf_subst_WfTy (env2 ::a A5). eassumption. eauto. rewr*. assumption.
Qed.

(** split *)
Lemma Uss_Wf_split_WfTy : forall (env2 env1 : Env) (sch : Sch) (exA exA1 exA2 : exvar) (a1 a2 : A),
    (env1 ::a (a2 ++ exA :: a1) +++ env2) |=ty sch
  -> (subst_exvar_Env (T_Fun (T_ExVar exA1) (T_ExVar exA2)) exA env1 ::a (a2 ++ exA2 :: exA1 :: a1)
         +++ subst_exvar_Env (T_Fun (T_ExVar exA1) (T_ExVar exA2)) exA env2)
      |=ty subst_exvar_Sch (T_Fun (T_ExVar exA1) (T_ExVar exA2)) exA sch.
Proof.
  introv WFTY.
  eapply WfTy_subst. eassumption.
  rewr. fsetdec. rewr. fsetdec. constructor; constructor; rewr; fsetdec.
Qed.

Lemma Uss_Wf_split_FrA : forall (a a1 a2 : A) (exA exA1 exA2 : exvar) (env1 env2 : Env),
    FrA a (env1 ::a (a2 ++ exA :: a1) +++ env2)
  -> FrA (exA2 :: [exA1]) ((env1 ::a (a2 ++ exA :: a1) +++ env2) ::a a)
  -> FrA a (subst_exvar_Env (T_Fun (T_ExVar exA1) (T_ExVar exA2)) exA env1 ::a (a2 ++ exA2 :: exA1 :: a1)
             +++ subst_exvar_Env (T_Fun (T_ExVar exA1) (T_ExVar exA2)) exA env2).
Proof.
  introv FRA1 FRA2. listind a. auto.
  constructor.
  - apply IHa. eauto. eapply FrA_Env_sub. eassumption.
    crush.
  - eauto. rewr.
    intro NIE. inv_FrA. indestr in NIE. rewr*; destr; eauto 7.
Qed.

Lemma Uss_Wf_split: forall (env1 : Env) (a1 : A) (exA : exvar) (a2 : A) (env2 : Env) (exA1 exA2 : exvar),
    wf(env1 ::a (a2 ++ exA :: a1) +++ env2)
  -> FrA (exA2 :: [exA1]) (env1 ::a (a2 ++ exA :: a1) +++ env2)
  -> wf(subst_exvar_Env (T_Fun (T_ExVar exA1) (T_ExVar exA2)) exA (env1 ::a (a2 ++ exA2 :: exA1 :: a1) +++ env2)).
Proof.
  introv WF FRA. induction env2.
  - rewr*. inv_Wf. rewrite subst_exvar_Env_notinenv.
    + constructor. assumption. induction a2.
      * norm. rep_app_assoc. apply FrA_app_split; simpl. split. eapply FrA_Env_sub. eassumption. eauto. eauto.
      * simpl. constructor. apply IHa2. eapply FrA_Env_sub. eassumption. crush.
        eauto. inv_FrA. intros.
        indestr in H. destr.
        1,2,3: apply FR3; rewr; fsetdec.
        -- rewr in H. subst. apply FR1. rewr. fsetdec.
        -- rewr in H. subst. apply FR0. rewr. fsetdec.
    + inv_FrA. crush.
    + eauto.
  - rewr*. inv_Wf.
  - rewr*. constructor. eauto. inv_Wf. eauto using Uss_Wf_split_FrA.
  - simpl. constructor. eauto. apply IHenv2; eauto.
    rewr*. inv_Wf. eauto using Uss_Wf_split_WfTy.
  - destruct Obj5. simpl. constructor. apply IHenv2; eauto.
    + rewr*. inv_Wf.  apply Uss_Wf_split_FrA. eassumption. rewrite <- FrA_Obj. eassumption.
    + rewr*. inv_Wf.
      forwards WFTY': Uss_Wf_split_WfTy (env2 ::a A5). rewr. eassumption. rewr in WFTY'. eassumption.
Qed.

(*** Main theorem *)
Theorem Uss_Wf : forall (env__in : Env) (eqs__in : Eqs) (env__out : Env) (eqs__out : Eqs) (sub : Sub),
    Uss env__in eqs__in env__out eqs__out sub
  -> wf(env__in)
  -> wf(Sub_app_Env env__out sub).
Proof.
  introv Uss WF__in. inverts Uss. 1,2,3: crush. all: simpl; unfold flip; auto using Uss_Wf_split, Uss_Wf_subst.
Qed.
