(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Defs.Set.

(*** Notation, tactics etc*)
Ltac listind a := induction a as [|?exA ?a].
Ltac instnil := instantiate (1 := nil).

Theorem list_rev_destr : forall {X : Type} (xs : list X), xs = nil \/ exists (x : X) (xs' : list X), xs = xs' ++ [x].
Proof. intros. destruct xs. crush. forwards: exists_last (x :: xs). crush. destruct H. destruct s. right. exists. rewrite e. reflexivity. Qed.

Definition one {X:Type} (x:X) : list X := x :: nil.

Notation "[ ]" := nil (format "[ ]").
Notation "[ x ]" := (one x).
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : list_scope.
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : list_scope.

(*** Stuff from modules *)
Theorem fold_singleton_varl : forall (a : A),
    fold_right (union ∘ singleton) empty a [=] varl a.
Proof. unfold varl. intros a. listind a; crush. Qed.
#[export] Hint Rewrite fold_singleton_varl : core.

(*** Inversion *)
Ltac inv_list :=
  repeat match goal with
    | [ H : _ = [] ++ _ |- _ ] => inverts H
    | [ H : _ = _ :: _ |- _ ] => inverts H
  end.

(*** Simplification *)
(** Associativity *)
Theorem app_assoc' : forall [X:Type] (l m n: list X),
    (l ++ m) ++ n = l ++ m ++ n.
Proof. symmetry. auto using app_assoc. Qed.
#[export] Hint Rewrite app_assoc' : core.
Ltac rep_app_assoc := repeat (rewrite app_assoc).
Tactic Notation "rep_app_assoc" "in" hyp(H) := repeat (rewrite app_assoc in H).
Tactic Notation "rep_app_assoc*" := repeat (rewrite app_assoc in *).

(** app-empty simplifications *)
#[export] Hint Rewrite app_nil_r app_nil_l : core.

(** one *)
Theorem one_rewrite : forall [X:Type] (x : X),
    x :: nil = [x].
Proof. reflexivity. Qed.
#[export] Hint Rewrite one_rewrite : core.

(** cons-app comm *)
Lemma cons_app_comm : forall [X:Type] (l1 a2 : list X) (x : X),
  (x :: l1) ++ a2 = x :: l1 ++ a2.
Proof. reflexivity. Qed.
#[export] Hint Rewrite cons_app_comm : core.

(** empty-to-one rewrites *)
Theorem list_one : forall [X:Type] (x:X),
    x :: [] = [x].
Proof. reflexivity. Qed.
#[export] Hint Rewrite list_one : core.

(** Cons-to-one rewrites (norm) *)
Lemma list_cons_one [X:Type] (l:list X) (x:X) :
    x :: l = one x ++ l.
Proof. reflexivity. Qed.
#[export] Hint Rewrite list_cons_one : norm.

(** Unsorted simplification*)
Theorem list_in_cons : forall (X : Type) (elem x : X) (xs : list X),
    In elem (x :: xs) = (x = elem \/ In elem xs).
Proof. reflexivity. Qed.
#[export] Hint Rewrite list_in_cons : core.

(*** Resoning over app *)
Theorem list_app_eq_share_head : forall (da1 da2 da1' da2' : DA),
    da1 ++ da2 = da1' ++ da2'
  -> (exists da1__rest, da1 = da1' ++ da1__rest) \/ (exists da1'__rest, da1' = da1 ++ da1'__rest).
Proof.
  intros. gen da1' da2 da2'. induction da1.
  - intros. right. exists. crush.
  - intros. destruct da1'.
    + rewr in H. subst. left. exists. crush.
    + rewr in H. inverts H.
      forwards: IHda1. eassumption. destr.
      * left. exists. crush.
      * right. exists. crush.
Qed.


(*** Membership *)
(** In *)
#[export] Hint Rewrite in_app_or : in_disj.
#[export] Hint Resolve in_or_app : core.

(*** Remove *)
Theorem remove_list_set_remove : forall (exA : exvar) (a : A),
    varl (remove eq_exvar exA a) [=] AtomSetImpl.remove exA (varl a).
Proof.
  introv. induction a. crush. simpl. ifdec.
  - subst. rewrite IHa. rewr. fsetdec.
  - simpl. rewrite IHa. rewr. fsetdec.
Qed.
#[export] Hint Rewrite remove_list_set_remove : core.

Theorem list_remove_notin : forall (exA : exvar) (a : A),
    exA \notin varl a
  -> remove eq_exvar exA a = a.
Proof. introv NIA. listind a. crush. simpl. ifdec; crush. Qed.

(*** NonNil *)
Definition NonNil (xs : list skvar) := xs <> [].


(*** List_rels *)

Module Type list_rel.
  Parameter elt : Type.
  Parameter R : list elt -> list elt -> Prop.

  Parameter refl : Reflexive R.
  Parameter trans : Transitive R.

  Parameter proper : Proper (R ==> R ==> R) (app (A := elt)).
End list_rel.

Module Type list_subrel.
  Include list_rel.
  Parameter R_empty : forall (l : list elt), R [] l.
End list_subrel.

Module Type list_eqrel.
  Include list_rel.
  Parameter symm : Symmetric R.
End list_eqrel.

Module Type atomlist_rel.
  Parameter R : list atom -> list atom -> Prop.
End atomlist_rel.
Module Type atomlist_subrel.
  Include atomlist_rel.
  Parameter R_empty : forall (l : list atom), R [] l.
End atomlist_subrel.

(** Trivial list rel *)
Module Trivial_List_rel <: atomlist_subrel.
  Definition R : list atom -> list atom -> Prop := const (const True).

  Definition refl : Reflexive R. unfold Reflexive, R. crush. Qed.
  Definition trans : Transitive R. unfold Transitive, R. crush. Qed.

  Definition proper : Proper (R ==> R ==> R) (app (A := atom)). autounfold. unfold R. crush. Qed.

  Definition R_empty : forall (l : list atom), R [] l. unfold R, const. crush. Qed.
End Trivial_List_rel.

(*** list_rel facts *)
(** list_subrel_facts *)
Module list_subrel_facts  (Import Rel : list_subrel).
  #[export] Hint Resolve refl : core.
  #[export] Hint Resolve R_empty : core.

  #[export] Instance list_subrel_preorder : PreOrder R :=
    { PreOrder_Reflexive  := refl
    ; PreOrder_Transitive := trans
    }.

  #[export] Instance list_subrel_cons_proper : Proper (eq ==> R ==> R) (cons (A:=elt)).
  Proof. autounfold. intros. subst. norm. apply proper. reflexivity. assumption. Qed.

  Corollary list_subrel_app : forall (l1 l1' l2 l2' : list elt),
      R l1 l1'
    -> R l2 l2'
    -> R (l1 ++ l2) (l1' ++ l2').
  Proof. intros. apply proper; auto. Qed.
  #[export] Hint Resolve list_subrel_app: core.

  Theorem list_subrel_app_r : forall (l1 l1' l2 : list elt),
      R l1 l1'
    -> R l1 (l1' ++ l2).
  Proof. intros. rewrite <- (app_nil_r l1). apply proper. assumption. apply R_empty. Qed.
  Theorem list_subrel_app_l : forall (l1 l2 l2': list elt),
      R l2 l2'
    -> R l2 (l1 ++ l2').
  Proof. intros. rewrite <- (app_nil_l l2). apply proper. apply R_empty. assumption. Qed.
  #[export] Hint Resolve list_subrel_app_r list_subrel_app_l : core.

  Corollary list_subrel_app_r' : forall (l1 l2 : list elt),
      R l1 (l1 ++ l2).
  Proof. intros. apply list_subrel_app_r. reflexivity. Qed.
  Corollary list_subrel_app_l' : forall (l1 l2 : list elt),
      R l2 (l1 ++ l2).
  Proof. intros. apply list_subrel_app_l. reflexivity. Qed.
  #[export] Hint Resolve list_subrel_app_r' list_subrel_app_l' : core.

  Theorem list_subrel_cons : forall (l1 l2 : list elt) (x : elt),
      R l1 l2
    -> R l1 (x :: l2).
  Proof. intros. norm. rewrite <- app_nil_l at 1. apply proper. apply R_empty. assumption. Qed.
  #[export] Hint Resolve list_subrel_cons : core.

  Corollary list_subrel_cons' : forall (l : list elt) (x : elt),
      R l (x :: l).
  Proof. intros. apply list_subrel_cons. reflexivity. Qed.
  #[export] Hint Resolve list_subrel_cons' : core.
End list_subrel_facts.

(** list_eqrel_facts *)
Module list_eqrel_facts  (Import Rel : list_eqrel).
  #[export] Hint Resolve refl : core.
  #[export] Hint Resolve symm : core.

  #[export] Instance list_subrel_preorder : Equivalence R :=

    { Equivalence_Reflexive  := refl
    ; Equivalence_Transitive := trans
    ; Equivalence_Symmetric  := symm
    }.

  #[export] Instance list_subrel_cons_proper : Proper (eq ==> R ==> R) (cons (A:=elt)).
  Proof. autounfold. intros. subst. norm. apply proper. reflexivity. assumption. Qed.

  Theorem list_eqrel_app : forall (l1 l1' l2 l2' : list elt),
      R l1 l1'
    -> R l2 l2'
    -> R (l1 ++ l2) (l1' ++ l2').
  Proof. intros. apply proper; assumption. Qed.
  #[export] Hint Resolve list_eqrel_app : core.

  Corollary list_eqrel_app_r : forall (l1 l1' l2 : list elt),
      R l1 l1'
    -> R (l1 ++ l2) (l1' ++ l2).
  Proof. intros. apply list_eqrel_app. assumption. reflexivity. Qed.
  Corollary list_eqrel_app_l : forall (l1 l2 l2' : list elt),
      R l2 l2'
    -> R (l1 ++ l2) (l1 ++ l2').
  Proof. intros. apply list_eqrel_app. reflexivity. assumption. Qed.
  #[export] Hint Resolve list_eqrel_app_r list_eqrel_app_l : core.

  Theorem list_eqrel_cons : forall (x : elt) (l l' : list elt),
      R l l'
    -> R (x :: l) (x :: l').
  Proof. intros. norm. apply proper. reflexivity. assumption. Qed.
  #[export] Hint Resolve list_eqrel_cons : core.

End list_eqrel_facts.

(*** list_(sub/eq) *)
(** list_sub *)
(* Def *)
Definition list_sub (a1 a2 : A) :=
    varl a1 [<=] varl a2.
#[export] Hint Unfold list_sub : core.

Notation "A [<=]l B" := (list_sub A B) (at level 65, format "A  [<=]l  B").

Theorem list_sub_inv : forall (a1 a2 : A),
    a1 [<=]l a2
  -> varl a1 [<=] varl a2.
Proof. auto. Qed.
#[export] Hint Resolve list_sub_inv : core.

(* Instance *)
Lemma list_sub_refl : Reflexive list_sub.
Proof. autounfold. crush. Qed.
#[export] Hint Resolve list_sub_refl : core.
Lemma list_sub_trans : Transitive list_sub.
Proof. autounfold. crush. Qed.

Theorem list_sub_app : forall (a1 a1' a2 a2' : A),
    a1 [<=]l a1'
  -> a2 [<=]l a2'
  -> a2 ++ a1 [<=]l a2' ++ a1'.
Proof. autounfold. intros. rewr. fsetdec. Qed.
#[export] Hint Resolve list_sub_app : core.
#[export] Instance list_sub_app_proper : Proper (list_sub ==> list_sub ==> list_sub) (app (A:=var)).
Proof. crush. Qed.

Module list_sub_subrel <: list_subrel.
  Definition elt : Type := atom.
  Definition R : list atom -> list atom -> Prop := list_sub.

  Definition refl  : Reflexive  R := list_sub_refl.
  Definition trans : Transitive R := list_sub_trans.

  Theorem R_empty : forall (l : list atom), R [] l. unfold R. crush. Qed.

  Definition proper : Proper (R ==> R ==> R) (app (A := atom)) := list_sub_app_proper.
End list_sub_subrel.

Module Export list_sub_subrel_facts := list_subrel_facts list_sub_subrel.
#[export]Hint Extern 1 (list_sub _ _) => fold list_sub_subrel.R : core.

(** list_eq *)
Definition list_eq (a1 a2 : A) :=
    varl a1 [=] varl a2.
#[export] Hint Unfold list_eq : core.

Notation "A [=]l B" := (list_eq A B) (at level 65, format "A  [=]l  B").

Theorem list_eq_sub : forall (a1 a2 : A),
    a1 [=]l a2
  -> a1 [<=]l a2.
Proof. autounfold. crush. Qed.
#[export] Hint Resolve list_eq_sub : core.

(* Instance *)
Lemma list_eq_refl : Reflexive list_eq.
Proof. autounfold. crush. Qed.
Lemma list_eq_trans : Transitive list_eq.
Proof. autounfold. crush. Qed.
Lemma list_eq_symm : Symmetric list_eq.
Proof. autounfold. crush. Qed.
#[export] Hint Resolve list_eq_refl list_eq_symm : core.

Theorem list_eq_app : forall (a1 a1' a2 a2' : A),
    a1 [=]l a1'
  -> a2 [=]l a2'
  -> a2 ++ a1 [=]l a2' ++ a1'.
Proof. autounfold. intros. rewr. fsetdec. Qed.
#[export] Hint Resolve list_eq_app : core.
#[export] Instance list_eq_app_proper : Proper (list_eq ==> list_eq ==> list_eq) (app (A:=var)).
Proof. crush. Qed.

Module list_eq_eqrel <: list_eqrel.
  Definition elt := atom.
  Definition R : list elt -> list elt -> Prop := list_eq.

  Definition refl  : Reflexive  R := list_eq_refl.
  Definition trans : Transitive R := list_eq_trans.
  Definition symm  : Symmetric  R := list_eq_symm.

  Definition proper : Proper (R ==> R ==> R) (app (A := elt)) := list_eq_app_proper.
End list_eq_eqrel.

Module Export list_eq_eqrel_facts := list_eqrel_facts list_eq_eqrel.
#[export]Hint Extern 1 (list_eq _ _) => fold list_eq_eqrel.R : core.

(* (*** list_uni_(sub/eq) *) *)
(* (** list_uni_sub *) *)
(* (* Def *) *)
(* Definition list_uni_sub (a1 a2 : A) := *)
(*     varl a1 [<=] varl a2. *)
(* #[export] Hint Unfold list_sub : core. *)

(* Notation "A [<=]l B" := (list_sub A B) (at level 65, format "A  [<=]l  B"). *)

(* (* Instance *) *)
(* Lemma list_sub_refl : Reflexive list_sub. *)
(* Proof. autounfold. crush. Qed. *)
(* #[export] Hint Resolve list_sub_refl : core. *)
(* Lemma list_sub_trans : Transitive list_sub. *)
(* Proof. autounfold. crush. Qed. *)

(* #[export] Instance list_sub_app_proper : Proper (list_sub ==> list_sub ==> list_sub) (app (A:=var)). *)
(* Proof. autounfold. intros. rewr. fsetdec. Qed. *)

(* Module list_sub_subrel <: list_subrel. *)
(*   Definition elt : Type := atom. *)
(*   Definition R : list atom -> list atom -> Prop := list_sub. *)

(*   Definition refl  : Reflexive  R := list_sub_refl. *)
(*   Definition trans : Transitive R := list_sub_trans. *)

(*   Theorem R_empty : forall (l : list atom), R [] l. unfold R. crush. Qed. *)

(*   Definition proper : Proper (R ==> R ==> R) (app (A := atom)) := list_sub_app_proper. *)
(* End list_sub_subrel. *)

(* Module Export list_sub_subrel_facts := list_subrel_facts list_sub_subrel. *)
(* #[export]Hint Extern 1 (list_sub _ _) => fold list_sub_subrel.R : core. *)

(* (** list_eq *) *)
(* Definition list_eq (a1 a2 : A) := *)
(*     varl a1 [=] varl a2. *)
(* #[export] Hint Unfold list_eq : core. *)

(* Notation "A [=]l B" := (list_eq A B) (at level 65, format "A  [=]l  B"). *)

(* Theorem list_eq_sub : forall (a1 a2 : A), *)
(*     a1 [=]l a2 *)
(*   -> a1 [<=]l a2. *)
(* Proof. autounfold. crush. Qed. *)
(* #[export] Hint Resolve list_eq_sub : core. *)

(* (* Instance *) *)
(* Lemma list_eq_refl : Reflexive list_eq. *)
(* Proof. autounfold. crush. Qed. *)
(* Lemma list_eq_trans : Transitive list_eq. *)
(* Proof. autounfold. crush. Qed. *)
(* Lemma list_eq_symm : Symmetric list_eq. *)
(* Proof. autounfold. crush. Qed. *)
(* #[export] Hint Resolve list_eq_refl list_eq_symm : core. *)

(* #[export] Instance list_eq_app_proper : Proper (list_eq ==> list_eq ==> list_eq) (app (A:=var)). *)
(* Proof. autounfold. intros. rewr. fsetdec. Qed. *)

(* Module list_eq_eqrel <: list_eqrel. *)
(*   Definition elt := atom. *)
(*   Definition R : list elt -> list elt -> Prop := list_eq. *)

(*   Definition refl  : Reflexive  R := list_eq_refl. *)
(*   Definition trans : Transitive R := list_eq_trans. *)
(*   Definition symm  : Symmetric  R := list_eq_symm. *)

(*   Definition proper : Proper (R ==> R ==> R) (app (A := elt)) := list_eq_app_proper. *)
(* End list_eq_eqrel. *)

(* Module Export list_eq_eqrel_facts := list_eqrel_facts list_eq_eqrel. *)
(* #[export]Hint Extern 1 (list_eq _ _) => fold list_eq_eqrel.R : core. *)

(*** list_unique *)
(* (* Inductive NoDup : list A -> Prop := *) *)
(* (*   | NoDup_nil : NoDup nil *) *)
(* (*   | NoDup_cons : forall x l, ~ In x l -> NoDup l -> NoDup (x::l). *) *)
(* #[export] Hint Constructors NoDup : core. *)

(* (** Refactor these to use NoDup lemmas *) *)
(* Theorem list_unique_inv : forall (exA : var) (a : A), *)
(*     list_unique (exA :: a) *)
(*   -> exA \notin varl a *)
(*   /\ list_unique a. *)
(* Proof. inversion 1. crush. Qed. *)
(* Corollary list_unique_inv1 : forall (x : var) (a : A), *)
(*     list_unique (x :: a) *)
(*   -> x \notin varl a. *)
(* Proof. apply list_unique_inv. Qed. *)
(* Corollary list_unique_inv2 : forall (x : var) (a : A), *)
(*     list_unique (x :: a) *)
(*   -> list_unique a. *)
(* Proof. apply list_unique_inv. Qed. *)
(* #[export] Hint Resolve list_unique_inv1 list_unique_inv2 : core. *)

(* Theorem list_unique_list_remove: forall (exA : atom) (a1 a2 : list atom), *)
(*     list_unique (a2 ++ a1) *)
(*   -> list_unique (remove eq_exvar exA a2 ++ a1). *)
(* Proof. *)
(*   introv LU. induction a2. crush. *)
(*   simpl. ifdec. *)
(*   - apply IHa2. eauto. *)
(*   - simpl in *. inverts LU. constructor. rewr*. fsetdec. crush. *)
(* Qed. *)

(* Theorem list_unique_app : forall (a1 a2 : A), *)
(*     list_unique (a1 ++ a2) *)
(*   -> list_unique a1 /\ list_unique a2. *)
(* Proof. *)
(*   introv UNI. listind a1. rewr*. split; simpl; auto. rewr*. *)
(*   forwards: IHa1. eauto. *)
(*   split; jauto. constructor. inverts UNI. rewr*. eauto. *)
(*   crush. *)
(* Qed. *)
(* Corollary list_unique_app1 : forall (a1 a2 : A), *)
(*     list_unique (a1 ++ a2) *)
(*   -> list_unique a1. *)
(* apply list_unique_app. Qed. *)
(* Corollary list_unique_app2 : forall (a1 a2 : A), *)
(*     list_unique (a1 ++ a2) *)
(*   -> list_unique a2. *)
(* apply list_unique_app. Qed. *)
(* #[export] Hint Resolve list_unique_app1 list_unique_app2 : core. *)


(*** NoDup' *)
Inductive NoDup' : A -> Prop :=
  | NoDup'_nil : NoDup' nil
  | NoDup'_cons : forall (exA : exvar) (a : A), exA \notin varl a -> NoDup' a -> NoDup' (exA :: a).
#[export] Hint Constructors NoDup' : core.

Theorem NoDup'_inv : forall (exA : exvar) (a : A),
    NoDup' (exA :: a)
  -> exA \notin varl a
  /\ NoDup' a.
Proof. inversion 1. crush. Qed.
Corollary NoDup'_inv1 : forall (exA : exvar) (a : A),
    NoDup' (exA :: a)
  -> exA \notin varl a.
Proof. apply NoDup'_inv. Qed.
Corollary NoDup'_inv2 : forall (exA : exvar) (a : A),
    NoDup' (exA :: a)
  -> NoDup' a.
Proof. apply NoDup'_inv. Qed.
#[export] Hint Resolve NoDup'_inv1 NoDup'_inv2 : core.

Theorem NoDup'_app : forall (a1 a2 : A),
    NoDup' (a1 ++ a2)
  -> NoDup' a1
  /\ NoDup' a2.
Proof.
  introv UNI. listind a1. rewr*. split; simpl; auto. rewr*.
  forwards: IHa1. eauto.
  split; jauto. constructor. inverts UNI. rewr*. eauto.
  crush.
Qed.
Corollary NoDup'_app1 : forall (a1 a2 : A),
    NoDup' (a1 ++ a2)
  -> NoDup' a1.
Proof. apply NoDup'_app. Qed.
Corollary NoDup'_app2 : forall (a1 a2 : A),
    NoDup' (a1 ++ a2)
  -> NoDup' a2.
Proof. apply NoDup'_app. Qed.
#[export] Hint Resolve NoDup'_app1 NoDup'_app2 : core.

Theorem NoDup'_twice_in : forall (a1 a2 : A) (exA : exvar),
    NoDup' (a2 ++ a1)
  -> exA \in varl a1
  -> exA \in varl a2
  -> False.
Proof.
  introv UNI NI1 NI2. listind a2. crush. rewr*.
  inverts UNI. rewr*. crush. fsetdec.
Qed.

Theorem NoDup'_remove: forall (exA : atom) (a1 a2 : list atom),
    NoDup' (a2 ++ a1)
  -> NoDup' (remove eq_exvar exA a2 ++ a1).
Proof.
  introv LU. induction a2. crush.
  simpl. ifdec.
  - apply IHa2. eauto.
  - simpl in *. inverts LU. constructor. rewr. rewrite remove_subset. rewr*. fsetdec.
    eauto.
Qed.

Lemma list_uni_sub_rem_helper : forall (exA : atom) (a1 a2 : A),
    a1 [<=]l a2
  -> remove eq_exvar exA a1 [<=]l remove eq_exvar exA a2.
Proof. autounfold. introv SL. autounfold. rewr. fsetdec. Qed.

Theorem list_uni_sub_rem : forall (exA : atom) (a1 a2 : A),
    (exA :: a1) [<=]l a2
  -> NoDup' (exA :: a1)
  -> a1 [<=]l remove eq_exvar exA a2.
Proof.
  introv SL UNI. forwards SL': list_uni_sub_rem_helper exA. eassumption.
  simpl in SL'. if_taut. rewrite list_remove_notin in SL'. assumption.
  inverts UNI. assumption.
Qed.

(*** list_uni_(sub/eq) *)
(** list_uni_subque *)
(* Def *)
Definition list_uni_sub (a1 a2 : list var) :=
    a1 [<=]l a2
  /\ (NoDup' a2 -> NoDup' a1).
#[export] Hint Unfold list_uni_sub : core.

Notation "A [<=]lu B" := (list_uni_sub A B) (at level 65, format "A  [<=]lu  B").

(*Conversion to list_sub *)
Theorem list_uni_sub_list_sub : forall (a1 a2 : A),
    a1 [<=]lu a2
  -> a1 [<=]l a2.
Proof. autounfold. crush. Qed.
#[export] Hint Resolve list_uni_sub_list_sub : core.

Theorem list_uni_sub_NoDup' : forall (a1 a2 : A),
    a1 [<=]lu a2
  -> NoDup' a2
  -> NoDup' a1.
Proof. autounfold. crush. Qed.
#[export] Hint Resolve list_uni_sub_NoDup' : core.


(* Instance *)
Lemma list_uni_sub_refl : Reflexive list_uni_sub.
Proof. autounfold. crush. Qed.
Lemma list_uni_sub_trans : Transitive list_uni_sub.
Proof. autounfold. crush. Qed.
#[export] Hint Resolve list_uni_sub_refl : core.

Theorem list_uni_sub_app : forall (a1 a1' a2 a2' : A),
    a1 [<=]lu a1'
  -> a2 [<=]lu a2'
  -> a2 ++ a1 [<=]lu a2' ++ a1'.
Proof.
  autounfold. introv [SL1 LU1] [SL2 LU2]. split. rewr. fsetdec.
  introv LU. gen a2'. listind a2; intros. rewr. eauto.
  rewr. constructor.
  - rewr. unfold not. intros. indestr.
    + forwards NIA: LU2. eauto. inverts NIA. crush.
    + eapply NoDup'_twice_in. apply LU. rewrite <- SL1. eassumption. rewrite <- SL2. rewr. fsetdec.
  - forwards SL': list_uni_sub_rem. apply SL2. eauto.
    apply (IHa2 (remove eq_exvar exA a2')). eauto. intros. eauto.
    eauto using NoDup'_remove.
Qed.
#[export] Hint Resolve list_uni_sub_app : core.

#[export] Instance list_uni_sub_app_proper : Proper (list_uni_sub ==> list_uni_sub ==> list_uni_sub) (app (A:=var)).
Proof. crush. Qed.

Module list_uni_sub_subrel <: list_subrel.
  Definition elt : Type := atom.
  Definition R : list atom -> list atom -> Prop := list_uni_sub.

  Definition refl  : Reflexive  R := list_uni_sub_refl.
  Definition trans : Transitive R := list_uni_sub_trans.

  Theorem R_empty : forall (l : list atom), R [] l. unfold R. crush. Qed.

  Definition proper : Proper (R ==> R ==> R) (app (A := atom)) := list_uni_sub_app_proper.
End list_uni_sub_subrel.

Module Export list_uni_subrel_facts := list_subrel_facts list_sub_subrel.
#[export] Hint Extern 1 (list_uni_sub _ _) => fold list_sub_subrel.R : core.

(** list_uni_eq *)
Definition list_uni_eq (a1 a2 : A) :=
    varl a1 [=] varl a2
  /\ (NoDup' a1 <-> NoDup' a2).
#[export] Hint Unfold list_uni_eq : core.

Notation "A [=]lu B" := (list_uni_eq A B) (at level 65, format "A  [=]lu  B").

Theorem list_uni_eq_sub : forall (a1 a2 : A),
    a1 [=]lu a2
  -> a1 [<=]lu a2.
Proof. autounfold. crush. Qed.
#[export] Hint Resolve list_uni_eq_sub : core.

Theorem list_uni_eq_eq : forall (a1 a2 : A),
    a1 [=]lu a2
  -> a1 [=]l a2.
Proof. intros. unfold list_uni_eq in H. jauto. Qed.
#[export] Hint Resolve list_uni_eq_eq : core.

(* Instance *)
Lemma list_uni_eq_refl : Reflexive list_uni_eq.
Proof. autounfold. crush. Qed.
Lemma list_uni_eq_trans : Transitive list_uni_eq.
Proof. autounfold. crush. Qed.
Lemma list_uni_eq_symm : Symmetric list_uni_eq.
Proof. autounfold. crush. Qed.
#[export] Hint Resolve list_uni_eq_refl list_uni_eq_symm : core.

Theorem list_uni_eq_app : forall (a1 a1' a2 a2' : A),
    a1 [=]lu a1'
  -> a2 [=]lu a2'
  -> a2 ++ a1 [=]lu a2' ++ a1'.
Proof.
  introv SUB1 SUB2. split. apply list_eq_app; auto. split.
  forwards: list_uni_sub_app a1' a1 a2' a2. auto. auto. unfold list_uni_sub in H. crush.
  forwards: list_uni_sub_app a1 a1' a2 a2'. auto. auto. unfold list_uni_sub in H. crush.
Qed.
#[export] Hint Resolve list_uni_eq_app : core.
#[export] Instance list_uni_eq_app_proper : Proper (list_uni_eq ==> list_uni_eq ==> list_uni_eq) (app (A:=var)).
Proof. crush. Qed.

Module list_uni_eq_eqrel <: list_eqrel.
  Definition elt := atom.
  Definition R : list elt -> list elt -> Prop := list_uni_eq.

  Definition refl  : Reflexive  R := list_uni_eq_refl.
  Definition trans : Transitive R := list_uni_eq_trans.
  Definition symm  : Symmetric  R := list_uni_eq_symm.

  Definition proper : Proper (R ==> R ==> R) (app (A := elt)) := list_uni_eq_app_proper.
End list_uni_eq_eqrel.

Module Export list_uni_eq_eqrel_facts := list_eqrel_facts list_uni_eq_eqrel.
#[export]Hint Extern 1 (list_uni_eq _ _) => fold list_uni_eq_eqrel.R : core.

(*** Unsorted *)
Theorem fold_right_varl : forall (a : list atom),
    (fold_right (compose AtomSetImpl.union AtomSetImpl.singleton) AtomSetImpl.empty a) [=] varl a.
Proof. intros. induction a. crush. rewr. fsetdec. Qed.
