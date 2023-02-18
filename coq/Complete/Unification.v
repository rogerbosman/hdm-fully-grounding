(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.
Require Import Defs.Defs.

Theorem make_unification : forall (sub : Sub) (env__in : Env) (ty1 ty2 : Ty) (denv : DEnv),
    Sub_app_t ty1 sub = Sub_app_t ty2 sub
  -> FullEInst env__in denv
  -> exists env__out,
      U env__in [(ty1, ty2)] env__out
    /\ FullEInst env__out denv.
Admitted.
