(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.
Require Import Defs.Defs.

Require Export Wf.InfGen.
Require Export Wf.Inst.
Require Export Wf.U.
Require Export Wf.Uss.

Theorem Inst_wf : forall (env : Env) (sch : Sch) (a : A) (ty : Ty),
    env |= sch ≤ ⟨a⟩ ty
  -> wf(env)
  -> env |=ty sch
  -> wf(env ::o ⟦⟨a⟩ S_Mono ty⟧).
Proof. exact Wf.Inst.Inst_Wf. Qed.

Theorem U_Wf : forall (env__in : Env) (eqs : Eqs) (env__out : Env),
    U env__in eqs env__out
  -> wf(env__in)
  -> wf(env__out).
Proof. exact Wf.U.U_Wf. Qed.

Theorem Us_Wf : forall (env__in : Env) (eqs : Eqs) (env__out : Env) (sub : Sub),
    Us env__in eqs env__out sub
  -> wf(env__in)
  -> wf(env__out).
Proof. exact Wf.U.Us_Wf. Qed.

Theorem Uss_Wf : forall (env__in : Env) (eqs__in : Eqs) (env__out : Env) (eqs__out : Eqs) (sub : Sub),
    Uss env__in eqs__in env__out eqs__out sub
  -> wf(env__in)
  -> wf(Sub_app_Env env__out sub).
Proof. exact Wf.Uss.Uss_Wf. Qed.

Theorem Inf_Wf : forall (env__in : Env) (e : e) (a : A) (ty : Ty) (env__out : Env),
    env__in |= e ▸ ⟨a⟩ ty =| env__out
  -> wf(env__in)
  -> wf(env__out ::o ⟦⟨a⟩ S_Mono ty⟧).
Proof. exact (proj1 Inf_Gen_Wf). Qed.

Theorem Gen_Wf : forall (env__in : Env) (e : e) (sch : Sch) (env__out : Env),
    env__in |= e ▸ sch =| env__out
  -> wf(env__in)
  -> wf(env__out ::o ⟦sch⟧).
Proof. exact (proj2 Inf_Gen_Wf). Qed.
