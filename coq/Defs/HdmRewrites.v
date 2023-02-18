(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Coq.Program.Basics.

Require Import Cpdtlib.CpdtTactics.

#[export] Hint Unfold flip : core.
Theorem flip_rewr : forall (A B C : Type) (f : A -> B -> C) (x : A) (y : B),
    flip (A := A) (B := B) (C := C) f y x = f x y.
Proof. crush. Qed.
#[export] Hint Rewrite flip_rewr : core.

Theorem compose_rewr : forall (A B C : Type) (g : B -> C) (f : A -> B) (x : A),
    (compose g f) x = g (f x).
Proof. crush. Qed.
#[export] Hint Rewrite compose_rewr : core.

Theorem fst_rewr : forall (A B : Type) (x : A) (y : B),
    fst (x, y) = x.
Proof. crush. Qed.
#[export] Hint Rewrite fst_rewr : core.

Theorem snd_rewr : forall (A B : Type) (x : A) (y : B),
    snd (x, y) = y.
Proof. crush. Qed.
#[export] Hint Rewrite snd_rewr : core.
