(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

(*** Notation, tactics etc*)
Notation  "A |= B ▸ C =| D" := (Gen A B C D) (at level 50) : type_scope.

(** For Combined Scheme Inf_Gen_mut see Inf.v *)
