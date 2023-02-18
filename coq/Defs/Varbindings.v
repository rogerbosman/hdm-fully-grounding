(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Defs.DEnv.
Require Import Defs.Env.
Require Import Defs.DObj.

(*** Notation, tactics etc*)

(*** Simplification *)
(* (** DEnv_bindings *) *)
(* Theorem varbindings_DEnv_da : forall (denv : DEnv) (da : DA), *)
(*     DEnv_bindings (denv :::a da) = DEnv_bindings denv. *)
(* Proof. induction da; crush. Qed. *)
(* #[export] Hint Rewrite varbindings_DEnv_da : core. *)

(* (** Env_bindings *) *)
(* Theorem Env_bindings_a : forall (env : Env) (a : A), *)
(*     Env_bindings (env ::a a) = Env_bindings env. *)
(* Proof. reflexivity. Qed. *)
(* #[export] Hint Rewrite Env_bindings_a : core. *)

(* Theorem Env_bindings_x : forall (env : Env) (x : termvar) (sch : Sch), *)
(*     Env_bindings (env ::x x :- sch) = (x, sch) :: Env_bindings env. *)
(* Proof. reflexivity. Qed. *)
(* #[export] Hint Rewrite Env_bindings_x : core. *)

(* Theorem varbindings_DEnv_dobj : forall (denv : DEnv) (da : DA) (dsch : DSch), *)
(*     DEnv_bindings (denv :::o ⟦⟨da⟩ dsch⟧d) = DEnv_bindings denv. *)
(* Proof. reflexivity. Qed. *)
(* #[export] Hint Rewrite varbindings_DEnv_dobj : core. *)
