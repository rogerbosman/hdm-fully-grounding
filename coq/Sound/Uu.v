(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.
Require Import Defs.Defs.
Require Import Wf.Wf.

Lemma FrA_helper : forall (exA exA1 exA2 : exvar) (env : Env),
    FrA (exA2 :: [exA1]) env
  -> exA \in Env_exvars env
  -> exA <> exA1 /\ exA <> exA2 /\ exA1 <> exA2.
Proof. introv FR IN. inv_FrA. crush. Qed.

Lemma In_Eqs_subst_exvar: forall (exA : exvar) (eqs : Eqs) (ty ty1 ty2 : Ty),
    In (ty1, ty2) eqs
  -> In (subst_exvar_Ty ty exA ty1, subst_exvar_Ty ty exA ty2)
      (subst_exvar_Eqs ty exA eqs).
Proof. introv IN. induction eqs. crush. simpl in IN. destr; crush. Qed.

Lemma Env_sub_fr_subst_exvar_Env : forall (env1 env2 : Env) (ty : Ty) (exA : exvar),
    env1 [<=]e# env2
  -> subst_exvar_Env ty exA env1 [<=]e# subst_exvar_Env ty exA env2.
Proof.
  autounfold. introv SUB. split.
  do 2 rewrite Env_skvars_subst_exvar_Env. crush.
  do 2 rewrite Env_exvars_Obj_subst_exvar_Env. crush.
Qed.

Lemma Us_add_Obj : forall (sch : Sch) (env__in env__out : Env) (eqs : Eqs) (sub : Sub),
    Us  env__in           eqs  env__out                       sub
  -> Us (env__in ::o ⟦sch⟧) eqs (env__out ::o ⟦Sub_app sch sub⟧) sub.
Proof.
  introv Us. gen sch. induction Us; intros. rewr. auto.
  inverts UNI.
  - econstructor; eauto. crush.
  - econstructor; eauto. crush.
  - econstructor; eauto. crush.
  - econstructor. rewrite Env_cons_app_o_one. econstructor. 2,3,4:tauto.
    eapply FrA_Env_sub. eassumption. autounfold. rewr. crush. eassumption.
    forwards IH: IHUs (Sub_app sch [(exA, T_Fun (T_ExVar exA1) (T_ExVar exA2))]). simpl. subdist in IH. subdist. eassumption.
  - econstructor. rewrite Env_cons_app_o_one. econstructor. 2,3,4:tauto.
    eapply FrA_Env_sub. eassumption. autounfold. rewr. crush. eassumption.
    forwards IH: IHUs (Sub_app sch [(exA, T_Fun (T_ExVar exA1) (T_ExVar exA2))]). simpl. subdist in IH. subdist. eassumption.
  - econstructor. rewrite Env_cons_app_o_one. econstructor. tauto. assumption.
    forwards IH: IHUs (Sub_app sch [(exB, T_ExVar exA)]). simpl. subdist in IH. subdist. eassumption.
  - econstructor. rewrite Env_cons_app_o_one. econstructor. tauto. assumption.
    forwards IH: IHUs (Sub_app sch [(exB, T_ExVar exA)]). simpl. subdist in IH. subdist. eassumption.
  - econstructor. rewrite Env_cons_app_o_one. econstructor. tauto. assumption.
    forwards IH: IHUs (Sub_app sch [(exA, T_Unit)]). simpl. subdist in IH. subdist. eassumption.
  - econstructor. rewrite Env_cons_app_o_one. econstructor. tauto. assumption.
    forwards IH: IHUs (Sub_app sch [(exA, T_Unit)]). simpl. subdist in IH. subdist. eassumption.
Qed.

Lemma Us_unifies : forall env__in eqs env__out sub ty1 ty2,
    Us env__in eqs env__out sub
  -> In (ty1, ty2) eqs
  -> Sub_app_t ty1 sub = Sub_app_t ty2 sub.
Proof.
  introv Us IN. gen ty1 ty2. induction Us; intros. crush.
  inverts UNI.
  - crush.
  - crush.
  - rewr*. destr. 2:crush. rewr. inv_Wf'. inv_WfTy.
    rewrite (IHUs Ty1 Ty3). rewrite (IHUs Ty2 Ty4). reflexivity. all:crush.
  - subdist. apply IHUs.
    simpl in IN. destr. 2:{ simpl. eauto using In_Eqs_subst_exvar. }
    simpl. forwards [? [? ?]]: FrA_helper exA. eassumption. rewr. fsetdec.
    if_taut. crush.
  - subdist. apply IHUs.
    simpl in IN. destr. 2:{ simpl. eauto using In_Eqs_subst_exvar. }
    simpl. forwards [? [? ?]]: FrA_helper exA. eassumption. rewr. fsetdec.
    if_taut. crush.

  - subdist. rewr*. destr. simpl. unfold flip. simpl. if_taut.
    simpl. erewrite IHUs. reflexivity. simpl. eauto using In_Eqs_subst_exvar.
  - subdist. rewr*. destr. simpl. unfold flip. simpl. if_taut.
    simpl. erewrite IHUs. reflexivity. simpl. eauto using In_Eqs_subst_exvar.

  - subdist. rewr*. destr. simpl. unfold flip. simpl. if_taut.
    simpl. erewrite IHUs. reflexivity. simpl. eauto using In_Eqs_subst_exvar.
  - subdist. rewr*. destr. simpl. unfold flip. simpl. if_taut.
    simpl. erewrite IHUs. reflexivity. simpl. eauto using In_Eqs_subst_exvar.
Qed.

Theorem U_unifies : forall env__in env__out ty1 ty2,
    U env__in [(ty1, ty2)] env__out
  -> exists ty,
      ((env__in ::o ⟦S_Mono ty1⟧) ::o ⟦S_Mono ty2⟧) |= [(ty1, ty2)] =| ((env__out ::o ⟦S_Mono ty⟧) ::o ⟦S_Mono ty⟧).
Proof.
  introv U. inverts U. apply (Us_add_Obj (S_Mono ty1)) in Us. apply (Us_add_Obj (S_Mono ty2)) in Us. rewr in Us.
  forwards EQ: Us_unifies. eassumption. simpl. eauto.
  exists (Sub_app_t ty2 Sub5). econstructor. rewrite EQ in Us. rewr. eassumption.
Qed.
