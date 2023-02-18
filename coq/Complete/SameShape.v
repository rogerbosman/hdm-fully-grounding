(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.
Require Import Defs.Defs.


Inductive SameShapeSch : Sch -> Sch -> Prop :=
  | SameShapeSch_Mono : forall (ty1 ty2 : Ty),
      SameShapeSch (S_Mono ty1) (S_Mono ty2)
  | SameShapeSch_Poly : forall (sch1 sch2 : Sch),
      SameShapeSch  sch1                     sch2
    -> SameShapeSch (S_Forall sch1) (S_Forall sch2).
#[export] Hint Constructors SameShapeSch : core.

Theorem SameShapeSch_refl : Reflexive SameShapeSch.
Proof. autounfold. intros sch. induction sch; crush. Qed.

Theorem SameShapeSch_trans : Transitive SameShapeSch.
Proof.
  autounfold. intros sch1 sch2 sch3 SS1 SS2. gen sch3. induction SS1; intros.
  - inverts SS2. auto.
  - inverts SS2. auto.
Qed.
#[export] Hint Resolve SameShapeSch_refl : core.

#[export] Instance SameShapeSch_preorder : PreOrder SameShapeSch :=
  { PreOrder_Reflexive  := SameShapeSch_refl
  ; PreOrder_Transitive := SameShapeSch_trans
  }.

Inductive SameShapeA : A -> A -> Prop :=
  | SameShapeA_Empty :
      SameShapeA [] []
  | SameShapeA_NN : forall (a1 a2 : A),
      NonNil a1
    -> SameShapeA a1 a2.
#[export] Hint Constructors SameShapeA : core.

Theorem SameShapeA_refl : Reflexive SameShapeA.
Proof. autounfold. intros. destruct x. auto. constructor. crush. Qed.

Theorem SameShapeA_trans : Transitive SameShapeA.
Proof.
  autounfold. intros a1 a2 a3 SS1 SS2. gen a3. induction SS1; intros.
  - inverts SS2. auto. unfold NonNil in H. contradiction.
  - inverts SS2. auto. constructor. assumption.
Qed.
#[export] Hint Resolve SameShapeA_refl : core.

#[export] Instance SameShapeA_preorder : PreOrder SameShapeA :=
  { PreOrder_Reflexive  := SameShapeA_refl
  ; PreOrder_Transitive := SameShapeA_trans
  }.

Inductive SameShapeObj : Obj -> Obj -> Prop :=
  | SameShapeObj_Obj : forall (a1 a2 : A) (sch1 sch2 : Sch),
      SameShapeSch sch1 sch2
    -> SameShapeA     a1   a2
    -> SameShapeObj (Obj_Sch a1 sch1) (Obj_Sch a2 sch2).
#[export] Hint Constructors SameShapeObj : core.

Inductive SameShape : Env -> Env -> Prop :=
  | SameShape_E   : SameShape Env_Empty Env_Empty
  | SameShape_Sk  : forall (skA skB : skvar) (env1 env2 : Env),
      SameShape env1 env2
    -> SameShape (env1 ::s skA) (env2 ::s skB)
  | SameShape_A   : forall (a1 a2 : A) (env1 env2 : Env),
      SameShape env1 env2
    -> SameShape (env1 ::a a1) (env2 ::a a2)
  | SameShape_Var : forall (x : termvar) (sch1 sch2 : Sch) (env1 env2 : Env),
      SameShape env1 env2
    -> SameShapeSch sch1 sch2
    -> SameShape (env1 ::x x :- sch1) (env2 ::x x :- sch2)
  | SameShape_Obj : forall (obj1 obj2 : Obj) (env1 env2 : Env),
      SameShape env1 env2
    -> SameShapeObj obj1 obj2
    -> SameShape (env1 ::o obj1) (env2 ::o obj2).
#[export] Hint Constructors SameShape : core.

Theorem SameShape_refl : Reflexive SameShape.
Proof. autounfold. intros env. induction env; crush. destruct Obj5. constructor; auto. Qed.
Theorem SameShape_trans : Transitive SameShape.
Proof.
  autounfold. intros env1 env2 env3 SS1 SS2. gen env3. induction SS1; intros; inverts SS2.
  - crush.
  - crush.
  - crush.
  - constructor. eauto. etransitivity. eassumption. auto.
  - constructor. eauto. inverts H. inverts H4. constructor.
    etransitivity. eassumption. assumption.
    etransitivity. eassumption. assumption.
Qed.
#[export] Hint Resolve SameShape_refl  : core.

#[export] Instance SameShape_preorder : PreOrder SameShape :=
  { PreOrder_Reflexive  := SameShape_refl
  ; PreOrder_Transitive := SameShape_trans
  }.

Theorem SameShape_app : forall (env1 env1' env2 env2' : Env),
    SameShape env1 env1'
  -> SameShape env2 env2'
  -> SameShape (env1 +++ env2) (env1' +++ env2').
Proof.
  introv SS1 SS2. induction SS2; rewr; auto. Qed.
#[export] Hint Resolve SameShape_app : core.

#[export] Instance SameShape_app_proper : Proper (SameShape ==> SameShape ==> SameShape) Env_app.
Proof. crush. Qed.

Lemma SameShapeA_nil_inv : forall a,
    SameShapeA [] a
  -> a = [].
Proof. intros. inverts H. reflexivity. unfold NonNil in *. contradiction. Qed.

Ltac inv_SS_ :=
  match goal with
    | [ H : SameShapeSch (S_Mono _  ) _  |- _ ] => inverts H
    | [ H : SameShapeSch (S_Forall _) _  |- _ ] => inverts H

    | [ H : SameShapeSch _ (S_Mono _  )  |- _ ] => inverts H
    | [ H : SameShapeSch _ (S_Forall _)  |- _ ] => inverts H

    | [ H : SameShapeA [] ?a  |- _ ] => apply SameShapeA_nil_inv in H; subst a

    | [ H : SameShapeObj _ _  |- _ ] => inverts H

    | [ H : SameShape (_ ::s _)      _  |- _ ] => inverts H
    | [ H : SameShape (_ ::a _)      _  |- _ ] => inverts H
    | [ H : SameShape (_ ::x _ :- _) _  |- _ ] => inverts H
    | [ H : SameShape (_ ::o _)      _  |- _ ] => inverts H

    | [ H : SameShape _ (_ ::s _)       |- _ ] => inverts H
    | [ H : SameShape _ (_ ::a _)       |- _ ] => inverts H
    | [ H : SameShape _ (_ ::x _ :- _)  |- _ ] => inverts H
    | [ H : SameShape _ (_ ::o _)       |- _ ] => inverts H
  end.
Ltac inv_SS := repeat inv_SS_.

Theorem Sub_app_Env_Empty : forall sub,
    Sub_app_Env • sub = •.
Proof. induction sub; crush. Qed.
#[export] Hint Rewrite Sub_app_Env_Empty : core.

Theorem Sub_app_Env_sk : forall env skA sub,
    Sub_app_Env (env ::s skA) sub = Sub_app_Env env sub ::s skA.
Proof. induction sub; crush. Qed.
#[export] Hint Rewrite Sub_app_Env_sk : core.

Theorem Sub_app_Env_a : forall env a sub,
    Sub_app_Env (env ::a a) sub = Sub_app_Env env sub ::a a.
Proof. induction sub; crush. Qed.
#[export] Hint Rewrite Sub_app_Env_a : core.

Theorem Sub_app_Env_x : forall env x sch sub,
    Sub_app_Env (env ::x x :- sch) sub = Sub_app_Env env sub ::x x :- (Sub_app sch sub).
Proof. induction sub; crush. subdist. reflexivity. Qed.
#[export] Hint Rewrite Sub_app_Env_x : core.

Theorem Sub_app_Env_o : forall env a sch sub,
    Sub_app_Env (env ::o ⟦⟨a⟩ sch⟧) sub = Sub_app_Env env sub ::o ⟦⟨a⟩ Sub_app sch sub⟧.
Proof. induction sub; crush. subdist. reflexivity. Qed.
#[export] Hint Rewrite Sub_app_Env_o : core.

Theorem Sub_app_SameShapeSch : forall sch sub,
    SameShapeSch sch (Sub_app sch sub).
Proof. intros. induction sch. econstructor. simpl. econstructor. eassumption. Qed.

Theorem Sub_app_SameShapeObj : forall a sch sub,
    SameShapeObj (⟦⟨a⟩ sch⟧) (⟦⟨a⟩ Sub_app sch sub⟧).
Proof. intros. constructor. auto using Sub_app_SameShapeSch. destruct a. auto. econstructor. unfold NonNil. crush. Qed.

Theorem Sub_app_Env_SameShape : forall env sub,
    SameShape env (Sub_app_Env env sub).
Proof.
  introv. induction env.
  - crush.
  - norm. eauto.
  - norm. eauto.
  - norm. apply SameShape_app. eassumption. constructor. auto. eauto using Sub_app_SameShapeSch.
  - destruct Obj5.
    norm. apply SameShape_app. eassumption. constructor. auto. eauto using Sub_app_SameShapeObj.
Qed.

Theorem Uss_SameShape : forall env__in e__in env__out e__out sub,
    Uss env__in e__in env__out e__out sub
  -> SameShape env__in env__out.
Proof. intros. inverts H; crush. Qed.

Theorem U_SameShape : forall env__in E env__out,
    U env__in E env__out
  -> SameShape env__in env__out.
Proof.
  intros. inverts H. induction Us. auto.
  forwards: Uss_SameShape. eassumption.
  etransitivity. eassumption.
  etransitivity. eapply Sub_app_Env_SameShape. eassumption.
Qed.

Definition Inf_SameShape__def := forall (env__in : Env) (e : e) (a : A) (ty : Ty) (env__out : Env),
    env__in |= e ▸ ⟨a⟩ ty =| env__out
  -> SameShape env__in env__out.

Definition Gen_SameShape__def := forall (env__in : Env) (e : e) (sch : Sch) (env__out : Env),
    env__in |= e ▸ sch =| env__out
  -> SameShape env__in env__out.

Theorem Inf_Gen_SameShape :
  Inf_SameShape__def /\ Gen_SameShape__def.
Proof.
  apply Inf_Gen_mut. 2:auto.
  - crush.
  - intros. fresh_atom. forwards: H. eassumption.
    inv_SS. crush.
  - intros. apply U_SameShape in UNI. inv_SS.
    transitivity Env1. auto.
    transitivity Env2. auto.
    assumption.
  - intros. transitivity Env_5. auto.
    fresh_atom. forwards: H0. eassumption.
    inv_SS. assumption.
  - intros. eauto.
Qed.

Theorem Inf_SameShape : Inf_SameShape__def.
Proof. apply Inf_Gen_SameShape. Qed.

Theorem Gen_SameShape : Gen_SameShape__def.
Proof. apply Inf_Gen_SameShape. Qed.
