(* -*- company-coq-local ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Decidable.

(*** Notation, tactics etc*)
Notation inter := AtomSetImpl.inter.

#[export] Hint Unfold Proper respectful Reflexive Symmetric Transitive impl flip : core.

Theorem proj1_sig_fresh : forall (L : vars),
    proj1_sig (atom_fresh L) `notin` L.
Proof. intro L. destruct (atom_fresh L). crush. Qed.
Ltac fresh_assert :=
  match goal with
    | [ |- context[proj1_sig (atom_fresh ?L)] ] => forwards: proj1_sig_fresh L
  end.

Theorem dec_In : forall (x : var) (s : vars),
  decidable (x \in s).
Proof. unfold decidable. fsetdec. Qed.

Ltac dec_In x L :=
  forwards [?IL|?NIL]: dec_In x L.

(*** disjoint *)
(** Potentially we move this to some extension of WSFun if we actually need it
for non-atom sets *)
#[export] Hint Unfold AtomSetImpl.disjoint : core.

Notation "A [><] B" := (AtomSetImpl.disjoint A B) (at level 80, format "A  [><]  B").

#[export] Instance disjoint_symm_inst : Symmetric AtomSetImpl.disjoint.
Proof. autounfold. intros. fsetdec. Qed.

#[export] Instance disj_subset_proper : Proper (flip AtomSetImpl.Subset ==> flip AtomSetImpl.Subset ==> impl) AtomSetImpl.disjoint.
Proof. autounfold. intros. fsetdec. Qed.
#[export] Instance disj_equiv_proper : Proper (AtomSetImpl.Equal ==> AtomSetImpl.Equal ==> impl) AtomSetImpl.disjoint.
Proof. autounfold. intros. fsetdec. Qed.

Theorem disjoint_extend : forall (x : var) (s1 s2 : vars),
    x \notin s2
  -> s1 [><] s2
  -> singleton x \u s1 [><] s2.
Proof. autounfold. intros. fsetdec. Qed.
Theorem disjoint_extend' : forall (x : var) (s1 s2 : vars),
    x \notin s2
  -> s1 [><] s2
  -> s1 \u singleton x [><] s2.
Proof. autounfold. intros. fsetdec. Qed.
Theorem disjoint_extend'' : forall (s1 s2 s2' : vars),
    s1 [><] (s2 \u s2')
  -> s2 [><] s2'
  -> s2 \u s1 [><] s2'.
Proof.
  unfold AtomSetImpl.disjoint. intros.
  rewrite <- H0. fsetdec.
Qed.

Theorem in_disjoint_impl : forall (x : var) (s1 s2: vars),
    s1 [><] s2
  -> x \in s1
  -> x \in s2
  -> False.
Proof. autounfold. intros. assert (x \in inter s1 s2). eauto using inter_iff. fsetdec. Qed.

Corollary in_disjoint_impl_notin1 : forall (x : var) (s1 s2: vars),
    s1 [><] s2
  -> x \in s2
  -> x \notin s1.
Proof. unfold not. intros. eauto using in_disjoint_impl. Qed.

Corollary in_disjoint_impl_notin2 : forall (x : var) (s1 s2: vars),
    s1 [><] s2
  -> x \in s1
  -> x \notin s2.
Proof. unfold not. intros. eauto using in_disjoint_impl. Qed.

#[export] Hint Extern 10 (?x \notin ?s1) =>
       match goal with
         | H : s1 [><] ?s2 |- _ => apply (in_disjoint_impl_notin1 x s1 s2 H)
       end : core.
#[export] Hint Extern 10 (?x \notin ?s2) =>
       match goal with
         | H : ?s1 [><] s2 |- _ => apply (in_disjoint_impl_notin2 x s1 s2 H)
       end : core.

(*** Simplification *)
Theorem remove_subset : forall (x : var) (V : vars),
    Metatheory.remove x V [<=] V.
Proof. fsetdec. Qed.

(*** WFacts_fun_plus *)
Module WFacts_fun_plus (Import E : DecidableType)(Import M : WSfun E).
  Include WFacts_fun E M.
  Module Import Dec := WDecide_fun E M.

  Theorem union_empty_l : forall (S : t),
      union empty S [=] S.
  Proof. fsetdec. Qed.
  #[export] Hint Rewrite union_empty_l : core WFacts_fun_plus.
  #[export] Hint Resolve union_empty_l : core WFacts_fun_plus.

  Theorem union_empty_r : forall (S : t),
      union S empty [=] S.
  Proof. fsetdec. Qed.
  #[export] Hint Rewrite union_empty_r : core WFacts_fun_plus.
  #[export] Hint Resolve union_empty_r : core WFacts_fun_plus.

  Theorem singleton_subset_empty : forall (e : elt) (s : t),
      union (singleton e) s [<=] empty
    -> False.
  Proof. unfold Subset. intros. forwards: H e. fsetdec. fsetdec. Qed.

  Theorem singleton_subset_empty' : forall (e : elt),
      singleton e [<=] empty
    -> False.
  Proof. intros. applys singleton_subset_empty e empty. fsetdec. Qed.

  (* Hints from WFacts_fun *)
  #[export] Hint Rewrite empty_iff singleton_iff : core WFacts_fun.
  #[export] Hint Rewrite union_iff : in_disj.
End WFacts_fun_plus.



Module Export Atom_facts   := WFacts_fun_plus Atom              AtomSetImpl.

Module Export DTyS_facts   := WFacts_fun_plus DecidableDTy      DTySI.
Module Export DSchS_facts  := WFacts_fun_plus DecidableDSch     DSchSI.
Module Export DTyPS_facts  := WFacts_fun_plus DecidableDTyPair  DTyPSI.
Module Export DSchPS_facts := WFacts_fun_plus DecidableDSchPair DSchPSI.

Module Export TyS_facts    := WFacts_fun_plus DecidableTy       TySI.
Module Export SchS_facts   := WFacts_fun_plus DecidableSch      SchSI.
Module Export TyPS_facts   := WFacts_fun_plus DecidableTyPair   TyPSI.
Module Export SchPS_facts  := WFacts_fun_plus DecidableSchPair  SchPSI.
(** Repeat the import of AtomSetFacts to make it the most recently imported such
that names default to the AtomSet ones *)
Export AtomSetFacts.

(** In *)
(* Hint Extern 2 (DTySI.In _ (DTySI.singleton _)) => destr_singleton : core. *)

Ltac indestr := autorewrite with core in_disj in *; destr.
Tactic Notation "indestr" "in" hyp(H) := autorewrite with core in_disj in H.

Ltac indestr' := indestr; crush.
Tactic Notation "indestr'" "in" hyp(H) := indestr in H; crush.

(* Ltac indestr' H := *)
(*   rewr in H; *)
(*   match type of H with *)
(*        (* AtomSetImpl.In *) *)
(*   | DTySI.In _ (DTySI.union ?s1 ?s2) => apply DTyS_facts.union_iff in H *)
(*        (* DSchSI.In *) *)
(*        (* DTyPSI.In *) *)
(*        (* DSchPSI.In *) *)
(*        (* TySI.In *) *)
(*        (* SchSI.In *) *)
(*        (* TyPSI.In *) *)
(*        (* SchPSI.In *) *)
(*   end; *)
(*   destr. *)

(* Ltac destr_singleton := *)
(*   match goal with *)
(*        (* AtomSetImpl.In *) *)
(*   | [ H: DTySI.In _ (DTySI.singleton _) |- _ ] => apply DTyS_facts.singleton_iff in H *)
(*        (* DSchSI.In *) *)
(*        (* DTyPSI.In *) *)
(*        (* DSchPSI.In *) *)
(*        (* TySI.In *) *)
(*        (* SchSI.In *) *)
(*        (* TyPSI.In *) *)
(*        (* SchPSI.In *) *)
(*   end; *)
(*   subst. *)
(* Ltac destr_singleton' H := *)
(*   match type of H with *)
(*        (* AtomSetImpl.In *) *)
(*   |  DTySI.In _ (DTySI.singleton _) => apply DTyS_facts.singleton_iff in H *)
(*        (* DSchSI.In *) *)
(*        (* DTyPSI.In *) *)
(*        (* DSchPSI.In *) *)
(*        (* TySI.In *) *)
(*        (* SchSI.In *) *)
(*        (* TyPSI.In *) *)
(*        (* SchPSI.In *) *)
(*   end; *)
(*   subst. *)
