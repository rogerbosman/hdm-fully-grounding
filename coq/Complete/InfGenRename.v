(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.
Require Import Defs.Defs.

Require Import Complete.SameShape.

Definition subst_name (x__in x__out x : termvar) : termvar := (if eq_var x x__out then x__in else x).
#[export] Hint Unfold subst_name : core.

Fixpoint subst_name_Env (x__in x__out : termvar) (env:Env) : Env :=
  match env with
  | Env_Empty            => Env_Empty
  | (Env_Skol env' skA ) => Env_Skol (subst_name_Env x__in x__out env') skA
  | (Env_A env' a      ) => Env_A (subst_name_Env x__in x__out env') a
  | (Env_Var env' x sch) => Env_Var (subst_name_Env x__in x__out env') (subst_name x__in x__out x) sch
  | (Env_Obj env' obj  ) => Env_Obj (subst_name_Env x__in x__out env') obj
end.
#[export] Hint Unfold subst_name_Env : core.

Definition Inf_rename_binding__def := forall (env__in : Env) (e : e) (a : A) (ty : Ty) (env__out : Env),
    env__in |= e ▸ ⟨a⟩ ty =| env__out
  -> forall x__in x__out,
    (subst_name_Env x__in x__out env__in) |= subst_tm_e (e_Var_f x__in) x__out e ▸ ⟨a⟩ ty =| (subst_name_Env x__in x__out env__out).

Definition Gen_rename_binding__def := forall (env__in : Env) (e : e) (sch : Sch) (env__out : Env),
    env__in |= e ▸ sch =| env__out
  -> forall x__in x__out,
    (subst_name_Env x__in x__out env__in) |= subst_tm_e (e_Var_f x__in) x__out e ▸ sch =| (subst_name_Env x__in x__out env__out).

Theorem subst_name_Env_lookup: forall (env : Env) (x__in x__out x : termvar) (sch : Sch),
    SchPSI.In (x, sch) (Env_bindings env)
  -> SchPSI.In (subst_name x__in x__out x, sch) (Env_bindings (subst_name_Env x__in x__out env)).
Proof.
  introv IN. induction env.
  - crush.
  - simpl. rewr in IN. rewr. eauto.
  - simpl. rewr in IN. rewr. eauto.
  - simpl. rewr in IN. rewr. indestr.
    + eauto.
    + rewr in H. crush.
  - simpl. rewr in IN. rewr. eauto.
Qed.

Theorem Inst_Env_sub : forall env1 env2 sch a ty,
    Inst env1 sch a ty
  -> env1 [=]e# env2
  -> Inst env2 sch a ty.
Proof.
  intros. gen env2. induction H; intros. crush.
  econstructor. unfold Env_fr_eq in H0. fsetdec. intros.
  eapply H. eassumption. crush.
Qed.

Theorem subst_name_Env_Env_eq : forall x__in x__out env,
    subst_name_Env x__in x__out env [=]e env.
Proof.
  induction env. 1,2,3,5: crush.
  rewr_erel. unfold Env_eq in IHenv. destr. split.
  simpl. rewr. assumption.
  simpl. rewr. assumption.
Qed.
#[export] Hint Resolve subst_name_Env_Env_eq : core.

Theorem subst_name_Env_Env_fr_eq : forall x__in x__out env,
    subst_name_Env x__in x__out env [=]e# env.
Proof.
  induction env. 1,2,3,5: crush.
  rewr_erel. unfold Env_fr_eq in IHenv. destr. split.
  simpl. rewr. assumption.
  simpl. rewr. assumption.
Qed.
#[export] Hint Resolve subst_name_Env_Env_fr_eq : core.

Theorem subst_name_Env_cons_o : forall env obj x__in x__out,
    subst_name_Env x__in x__out (env ::o obj) = subst_name_Env x__in x__out env ::o obj.
Proof. reflexivity. Qed.
#[export] Hint Rewrite subst_name_Env_cons_o : core.

Theorem subst_name_Env_app : forall x__in x__out env1 env2,
    subst_name_Env x__in x__out (env1 +++ env2)
  = subst_name_Env x__in x__out env1 +++ subst_name_Env x__in x__out env2.
Proof. induction env2; crush. Qed.
#[export] Hint Rewrite subst_name_Env_app : core.

Theorem subst_name_Envsubst_exvar_Env : forall x__in x__out ty exA env,
    subst_name_Env x__in x__out (subst_exvar_Env ty exA env)
  = subst_exvar_Env ty exA (subst_name_Env x__in x__out env).
Proof. induction env; rewr; crush. Qed.

Theorem subst_name_Env_Sub_app_Env : forall x__in x__out env sub,
    subst_name_Env x__in x__out (Sub_app_Env env sub)
  = Sub_app_Env (subst_name_Env x__in x__out env) sub.
Proof.
  intros. induction sub. crush.
  destruct a. simpl. rewr.
  rewrite <- IHsub. rewrite subst_name_Envsubst_exvar_Env. reflexivity.
Qed.

Theorem subst_name_Env_U : forall (x__in x__out : termvar) (env__in env__out : Env) (E : Eqs),
    U env__in E env__out
  -> U (subst_name_Env x__in x__out env__in) E (subst_name_Env x__in x__out env__out).
Proof.
  introv U. destruct U. econstructor.
  induction Us. crush.
  forwards: subst_name_Env_Sub_app_Env. rewrite H in IHUs.
  econstructor. 2:eassumption. clear H. destruct UNI. 1,2,3: auto.
  - assert (FrA [exA2; exA1] (subst_name_Env x__in x__out (Env1 ::a (A2 ++ exA :: A1) +++ Env2))). eauto.
    rewr. rewr in H2. simpl. applys_eq UssSplitL. rewr in H3. eassumption. rewr. eassumption.
  - assert (FrA [exA2; exA1] (subst_name_Env x__in x__out (Env1 ::a (A2 ++ exA :: A1) +++ Env2))). eauto.
    rewr. rewr in H2. simpl. applys_eq UssSplitR. rewr in H3. eassumption. rewr. eassumption.
  - rewr. applys_eq UssSubExL. fold subst_name_Env.
    assert (subst_name_Env x__in x__out (Env1 ::a A1) [=]e Env1 ::a A1). eauto. unfold Env_eq in H1. destr. rewrite H2. assumption.
  - assert (exA `in` Env_exvars (subst_name_Env x__in x__out Env1 ::a A1)).
      assert (subst_name_Env x__in x__out (Env1 ::a A1) [=]e Env1 ::a A1). eauto. unfold Env_eq in H1. destr. rewrite H2. assumption.
    rewr. applys_eq UssSubExR. eassumption.
  - rewr. applys_eq UssSubUnitAL.
  - rewr. applys_eq UssSubUnitAR.
Qed.

Theorem Inf_Gen_Wf :
  Inf_rename_binding__def /\ Gen_rename_binding__def.
Proof.
  apply Inf_Gen_mut.

  - introv IN SS. intros x__in x__out.
    forwards IN': subst_name_Env_lookup x__in x__out. eassumption.
    unfold subst_name in IN'. destruct (x == x__out).
    + simpl. if_taut. intros. econstructor. eassumption.
      eapply Inst_Env_sub. eassumption. auto using subst_name_Env_Env_fr_eq.
    + simpl. if_taut. intros. econstructor. eassumption.
      eapply Inst_Env_sub. eassumption. auto using subst_name_Env_Env_fr_eq.

  - intros. simpl. crush.

  - introv NIE INF IH. intros.
    forwards EQ: subst_name_Env_Env_fr_eq x__in x__out Envin.
    simpl. applys InfAbs (L \u singleton x__out). unfold Env_fr_eq in EQ. destr. rewrite e0. eassumption.
    intros y NI__y.
    forwards: IH y x__in x__out. fsetdec.
    assert (y <> x__out). unfold not. intros. apply NI__y. fsetdec.
    asserts_rewrite ( subst_tm_e (e_Var_f x__in) x__out (open_e_wrt_e e5 (e_Var_f y))
                    = open_e_wrt_e (subst_tm_e (e_Var_f x__in) x__out e5) (e_Var_f y)) in H.
      rewrite subst_tm_e_open_e_wrt_e. simpl. ifdec. contradiction. reflexivity. auto.
    asserts_rewrite (subst_name x__in x__out y = y) in H.
      unfold subst_name. ifdec. contradiction. reflexivity.
    assumption.

  - introv NIE INF__e1 IH__e1 INF__e2 IH__e2 U. intros.
    simpl.
    forwards IH1: IH__e1 x__in x__out.
    forwards IH2: IH__e2 x__in x__out.
    applys InfApp exB.
    2:apply IH1.
    2:apply IH2.
    + forwards EQ: subst_name_Env_Env_fr_eq x__in x__out (Env2 ::a (A2 ++ A1')).
      unfold Env_fr_eq in EQ. destr. rewrite H0. eassumption.
    + forwards U': subst_name_Env_U x__in x__out. eassumption.
      rewr in U'. assumption.

  - introv GEN IH__gen MON IH__mon. intros.
    forwards: IH__gen.
    simpl. applys InfLet (L \u singleton x__out).
    + eassumption.
    + intros y NI__y. forwards: IH__mon y x__in x__out. fsetdec.
      assert (y <> x__out). unfold not. intros. apply NI__y. fsetdec.
      asserts_rewrite ( subst_tm_e (e_Var_f x__in) x__out (open_e_wrt_e e2 (e_Var_f y))
                      = open_e_wrt_e (subst_tm_e (e_Var_f x__in) x__out e2) (e_Var_f y)) in H0.
        rewrite subst_tm_e_open_e_wrt_e. simpl. ifdec. contradiction. reflexivity. auto.
      asserts_rewrite (subst_name x__in x__out y = y) in H0.
        unfold subst_name. ifdec. contradiction. reflexivity.
      eassumption.

  - introv INF IH__inf GEN. intros.
    forwards: IH__inf.
    econstructor. eassumption. assumption.
Qed.

Theorem subst_name_Env_notin_involuntive : forall (x__out x__in : termvar) (env : Env),
    x__out \notin Env_boundvars env
  -> subst_name_Env x__in x__out env = env.
Proof.
  induction env.
  - crush.
  - crush.
  - crush.
  - intros. simpl. unfold subst_name. ifdec; crush.
  - crush.
Qed.

Theorem SameShape_boundvars : forall env1 env2,
    SameShape env1 env2
  -> Env_boundvars env1 = Env_boundvars env2.
Proof. introv SS. induction SS; crush. Qed.

Theorem Inf_rename_binding' : forall y env__in x sch e a ty env__out sch',
    (env__in ::x x :- sch) |=                          e ▸ ⟨a⟩ ty =| (env__out ::x x :- sch')
  -> x \notin (Env_boundvars env__in)
  -> (env__in ::x y :- sch) |= subst_tm_e (e_Var_f y) x e ▸ ⟨a⟩ ty =| (env__out ::x y :- sch').
Proof.
  introv INF NIE. destruct (x == y).
  - subst.
    asserts_rewrite (subst_tm_e (e_Var_f y) y e = e). rewrite subst_tm_e_spec. crush.
    assumption.
  - forwards: proj1 Inf_Gen_Wf. unfold Inf_rename_binding__def in H. forwards: H y x. eassumption.
    simpl in H0. unfold subst_name in H0. if_taut.
    assert (x \notin Env_boundvars env__out).
      forwards: Inf_SameShape. apply INF. inverts H1. apply SameShape_boundvars in H4. crush.
    forwards REWR1: subst_name_Env_notin_involuntive x env__in.  fsetdec. rewrite REWR1 in H0.
    forwards REWR2: subst_name_Env_notin_involuntive x env__out. fsetdec. rewrite REWR2 in H0.
    assumption.
Qed.
