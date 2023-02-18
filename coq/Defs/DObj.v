(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

(*** Notation, tactics etc*)
Notation  "⟦ ⟨ A ⟩ B ⟧d" := (DObj_DSch A B) (at level 49, format "⟦ ⟨ A ⟩  B ⟧d" ) : type_scope.
Notation  "⟦ B ⟧d" := (DObj_DSch (nil:A) B) (at level 49, format "⟦ B ⟧d" ) : type_scope.
