(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

(*** Notation, tactics etc*)
Notation  "A |= B ≤ ⟨ C ⟩ D" := (Inst A B C D) (at level 50, format "A  |=  B  ≤  ⟨ C ⟩  D" ) : type_scope.
