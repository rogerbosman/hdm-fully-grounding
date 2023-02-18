(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.
Require Import Defs.Defs.

Require Export Wf.Uss.

(** Unfortunately I did not find a notation that works two ways *)
Notation  "A |= B =| C , D"       := (Us A B C D)   (at level 50) : type_scope.
Notation  "A |= B =| C"           := (U  A B C  )   (at level 50) : type_scope.

Theorem Us_Wf : forall (env__in : Env) (eqs : Eqs) (env__out : Env) (sub : Sub),
    Us env__in eqs env__out sub
  -> wf(env__in)
  -> wf(env__out).
Proof.
  introv US WF. induction US. auto.
  eauto using Uss_Wf.
Qed.

Theorem U_Wf : forall (env__in : Env) (eqs : Eqs) (env__out : Env),
    U env__in eqs env__out
  -> wf(env__in)
  -> wf(env__out).
Proof. introv U WF. inverts U. eauto using Us_Wf. Qed.
