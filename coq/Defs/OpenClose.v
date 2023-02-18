(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

(*** Simplification *)
Theorem open_Sch_wrt_Ty_rec_mono : forall (n : nat) (ty1 ty2 : Ty),
    open_Sch_wrt_Ty_rec n ty2 (S_Mono ty1) = S_Mono (open_Ty_wrt_Ty_rec n ty2 ty1).
Proof. reflexivity. Qed.
#[export] Hint Rewrite open_Sch_wrt_Ty_rec_mono : core.

(*** openening lc terms *)
(* Lemma open_Ty_wrt_Ty_lc_Ty : forall Ty2 Ty1, lc_Ty Ty2 -> open_Ty_wrt_Ty Ty2 Ty1 = Ty2. *)
Theorem open_Ty_wrt_Ty_lc_Ty_rec : forall (n : nat) (ty1 ty2 : Ty),
    lc_Ty ty1
  -> open_Ty_wrt_Ty_rec n ty2 ty1 = ty1.
Proof. introv LC. induction LC; crush. Qed.
