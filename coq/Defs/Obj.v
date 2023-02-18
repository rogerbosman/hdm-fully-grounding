(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

(*** Notation, tactics etc*)
Notation  "⟦ ⟨ A ⟩ B ⟧" := (Obj_Sch A B) (at level 49, format "⟦ ⟨ A ⟩  B ⟧" ) : type_scope.
Notation  "⟦ B ⟧" := (Obj_Sch (nil:A) B) (at level 49, format "⟦ B ⟧" ) : type_scope.
