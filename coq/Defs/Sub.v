(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Defs.DSub.
Require Import Defs.Env.
Require Import Defs.List.

(*** Notation, tactics etc*)
Ltac Sub_ind sub :=
    let sub' := fresh "sub" in
    (* let DTY := fresh "dty" in *)
    (* let exA := fresh "exA" in *)
    induction sub as [|[?ty ?exA] sub'].

(*** Sub_app(_t) *)
(** Simplification *)
Theorem Sub_app_t_sk_b : forall (sub : Sub) (n : nat),
  Sub_app_t (T_SkVar_b n) sub = T_SkVar_b n.
Proof. induction sub; crush. Qed.
#[export] Hint Rewrite Sub_app_t_sk_b : core.

Theorem Sub_app_t_sk_f : forall (sub : Sub) (skA : skvar),
  Sub_app_t (T_SkVar_f skA) sub = T_SkVar_f skA.
Proof. induction sub; crush. Qed.
#[export] Hint Rewrite Sub_app_t_sk_f : core.

Theorem Sub_app_t_unit : forall (sub : Sub),
  Sub_app_t (T_Unit) sub = T_Unit.
Proof. induction sub; crush. Qed.
#[export] Hint Rewrite Sub_app_t_unit : core.

Theorem Sub_app_t_fun : forall (sub : Sub) (t1 t2 : Ty),
    Sub_app_t (T_Fun t1 t2) sub = T_Fun (Sub_app_t t1 sub) (Sub_app_t t2 sub).
Proof.
Proof. induction sub; crush. Qed.
#[export] Hint Rewrite Sub_app_t_fun : core.

Theorem Sub_app_forall : forall (sub : Sub) (sch : Sch),
    Sub_app (S_Forall sch) sub = S_Forall (Sub_app sch sub).
Proof. induction sub; crush. Qed.
#[export] Hint Rewrite Sub_app_forall : core.

Theorem Sub_app_nil : forall (sch : Sch),
    Sub_app sch nil = sch.
Proof. induction sch; [induction Ty5|idtac]; crush. Qed.
#[export] Hint Rewrite Sub_app_nil : core.

Theorem Sub_app_t_nil : forall (ty : Ty),
    Sub_app_t ty nil = ty.
Proof. induction ty; crush. Qed.
#[export] Hint Rewrite Sub_app_t_nil : core.

Theorem Sub_app_mono : forall (sub : Sub) (ty : Ty),
    Sub_app (S_Mono ty) sub = S_Mono (Sub_app_t ty sub).
Proof. crush. Qed.
#[export] Hint Rewrite Sub_app_mono : core.

(** Distrubution *)
Theorem Sub_app_t_app_distr : forall (sub1 sub2 : Sub) (ty : Ty),
    Sub_app_t ty (sub2 ++ sub1) = Sub_app_t (Sub_app_t ty sub1) sub2.
Proof. induction sub2; simpl; crush. Qed.
#[export] Hint Rewrite Sub_app_t_app_distr : subdist.

Theorem Sub_app_app_distr : forall (sub1 sub2 : Sub) (sch : Sch),
    Sub_app sch (sub2 ++ sub1) = Sub_app (Sub_app sch sub1) sub2.
Proof.
  induction sub2; simpl; crush.
  Sch_Ty_ind sch; rewr; crush.
  subdist. reflexivity.
Qed.
#[export] Hint Rewrite Sub_app_app_distr : subdist.

Theorem Sub_app_Env_app_distr : forall (sub1 sub2 : Sub) (env : Env),
    Sub_app_Env env (sub2 ++ sub1) = Sub_app_Env (Sub_app_Env env sub1) sub2.
Proof.
  induction sub2; simpl; crush.
Qed.
#[export] Hint Rewrite Sub_app_Env_app_distr : subdist.

Theorem Sub_app_t_cons_distr : forall (ty ty__sub : Ty) (exA : exvar) (sub : Sub),
    Sub_app_t ty ((exA, ty__sub) :: sub) = subst_exvar_Ty ty__sub exA (Sub_app_t ty sub).
Proof. reflexivity. Qed.
#[export] Hint Rewrite Sub_app_t_cons_distr : subdist.

Theorem Sub_app_cons_distr : forall (sch : Sch) (ty__sub : Ty) (exA : exvar) (sub : Sub),
    Sub_app sch ((exA, ty__sub) :: sub) = subst_exvar_Sch ty__sub exA (Sub_app sch sub).
Proof. induction sch; crush. Qed.
#[export] Hint Rewrite Sub_app_cons_distr : subdist.

Corollary Sub_app_cons_distr' : forall (sch : Sch) (ty__sub : Ty) (exA : exvar),
    Sub_app sch [(exA, ty__sub)] = subst_exvar_Sch ty__sub exA sch.
Proof. intros. unfold one. rewrite Sub_app_cons_distr. crush. Qed.
#[export] Hint Rewrite Sub_app_cons_distr' : subdist.

Theorem Sub_app_Env_nil : forall (env : Env),
  Sub_app_Env env []  = env.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Sub_app_Env_nil : core.

Theorem Sub_app_Eqs_nil : forall (eqs : Eqs),
  Sub_app_Eqs eqs [] = eqs.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Sub_app_Eqs_nil : core.

(*** Sub/DSub *)

Fixpoint DSub_to_Sub (dsub : DSub) : Sub :=
  match dsub with
  | []                 => []
  | (exA, dty) :: dsub' => (exA, emb_Ty dty) :: DSub_to_Sub dsub'
end.

Theorem DSub_to_Sub_cons : forall (exA : exvar) (dty : DTy) (dsub : DSub),
    DSub_to_Sub ((exA, dty) :: dsub) = (exA, emb_Ty dty) :: DSub_to_Sub dsub.
Proof. reflexivity. Qed.
#[export] Hint Rewrite DSub_to_Sub_cons : core.

Theorem DSub_to_Sub_app : forall (dsub1 dsub2 : DSub),
    DSub_to_Sub (dsub1 ++ dsub2) = DSub_to_Sub dsub1 ++ DSub_to_Sub dsub2.
Proof. induction dsub1; crush. Qed.
#[export] Hint Rewrite DSub_to_Sub_app : core.

Theorem DSub_app_t_Sub_app_t : forall (dsub : DSub) (ty1 ty2 : Ty),
    DSub_app_t ty1 dsub = DSub_app_t ty2 dsub
  -> Sub_app_t ty1 (DSub_to_Sub dsub) = Sub_app_t ty2 (DSub_to_Sub dsub).
Proof.
  intros. gen ty1 ty2. rev_DSub_ind dsub. crush. intros.
  subdist*. forwards: IHdsub0. eassumption. crush.
Qed.
