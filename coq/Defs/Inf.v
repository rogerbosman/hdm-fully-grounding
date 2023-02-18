(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

(*** Notation, tactics etc*)
Notation  "A |= B ▸ ⟨ C ⟩ D =| E" := (Inf A B C D E) (at level 50, format "A  |=  B  ▸  ⟨ C ⟩  D  =|  E" ) : type_scope.

Scheme Inf_mut := Induction for Inf Sort Prop
  with Gen_mut := Induction for Gen Sort Prop.
Combined Scheme Inf_Gen_mut
         from Inf_mut, Gen_mut.
