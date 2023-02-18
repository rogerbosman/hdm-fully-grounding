Set Warnings "-notation-overridden".

Require Import Sound.Sound.
Require Import Complete.Complete.

Example no_axioms : True.
  idtac "Verifying Assumptions Soundness__mono".
  Print Assumptions Soundness__mono.
  idtac "Verifying Assumptions Soundness__poly".
  Print Assumptions Soundness__poly.

  idtac "Print Assumptions Completeness__mono".
  Print Assumptions Completeness__mono.
  idtac "Print Assumptions Completeness__poly".
  Print Assumptions Completeness__poly.

  tauto.
Qed.
