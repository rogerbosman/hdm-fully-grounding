(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Import Prelude.Prelude.

Require Import Defs.List.
Require Import Defs.Set.
Require Import Defs.GEnv.

(*** Notation, tactics etc*)
Notation "▪" := DEnv_Empty (at level 1).

Notation "A :::s B"        := (DEnv_DSkol A B)   (at level 50).
Notation "A :::a B"        := (DEnv_DA   A B)    (at level 50).
Notation "A :::x B ':-' C" := (DEnv_DVar  A B C) (at level 50).
Notation "A :::o B"        := (DEnv_DObj  A B)   (at level 50).

Notation "< A >da"      := (oneDA A)   (at level 1, format "< A >da").
Notation "< A >ds"      := (oneDS A)   (at level 1, format "< A >ds").
Notation "< B :- C >dx" := (oneDX B C) (at level 1, format "< B  :-  C >dx").
Notation "< B >do"      := (oneDO B)   (at level 1, format "< B >do").

Notation "A ++++ B" := (DEnv_app A B) (at level 61, left associativity).

(*** Simplification *)
(** Associativity *)
Theorem DEnv_app_assoc (denv1 denv2 denv3 : DEnv) : denv1 ++++ denv2 ++++ denv3 = denv1 ++++ (denv2 ++++ denv3).
Proof. induction denv3; crush. Qed.
Theorem DEnv_app_assoc' (denv1 denv2 denv3 : DEnv) : denv1 ++++ (denv2 ++++ denv3) = denv1 ++++ denv2 ++++ denv3.
Proof. symmetry. gen denv1 denv2 denv3. exact DEnv_app_assoc. Qed.
#[export] Hint Rewrite DEnv_app_assoc' : core.

Ltac rep_DEnv_app_assoc := repeat (rewrite DEnv_app_assoc).
Tactic Notation "rep_DEnv_app_assoc" "in" hyp(H) := repeat (rewrite DEnv_app_assoc in H).
Tactic Notation "rep_DEnv_app_assoc*" := repeat (rewrite DEnv_app_assoc in *).


(** app-empty simplifications *)
Theorem DEnv_app_nil_l denv :
    ▪ ++++ denv = denv.
Proof. induction denv; crush. Qed.
Theorem DEnv_app_nil_r denv :
    denv ++++ ▪ = denv.
Proof. reflexivity. Qed.
#[export] Hint Rewrite DEnv_app_nil_l DEnv_app_nil_r : core.

(** cons-empty simplifications *)
Theorem DEnv_cons_anil : forall (denv : DEnv),
    denv :::a [] = denv.
Proof. reflexivity. Qed.

(** empty-to-one rewrites *)
Theorem DEnv_Empty_s (dskA : dskvar) :
    ▪ :::s dskA = <dskA>ds.
Proof. crush. Qed.
Theorem DEnv_Empty_a (a : A) :
    ▪ :::a a = <a>da.
Proof. crush. Qed.
Theorem DEnv_Empty_x (x : termvar) (dsch : DSch) :
    ▪ :::x x :- dsch = <x :- dsch>dx.
Proof. crush. Qed.
Theorem DEnv_Empty_o (dobj : DObj) :
    ▪ :::o dobj = <dobj>do.
Proof. crush. Qed.
#[export] Hint Rewrite DEnv_Empty_a DEnv_Empty_s DEnv_Empty_x DEnv_Empty_o : core.

Theorem DEnv_app_cons_s : forall (denv1 denv2 : DEnv) (skA : skvar),
    denv1 ++++ denv2 :::s skA = (denv1 ++++ denv2) :::s skA.
Proof. reflexivity. Qed.
Theorem DEnv_app_cons_a : forall (denv1 denv2 : DEnv) (da : DA),
    denv1 ++++ denv2 :::a da = (denv1 ++++ denv2) :::a da.
Proof. induction da; crush. Qed.
Theorem DEnv_app_cons_x : forall (denv1 denv2 : DEnv) (x : termvar) (dsch : DSch),
    denv1 ++++ denv2 :::x x :- dsch = (denv1 ++++ denv2) :::x x :- dsch.
Proof. reflexivity. Qed.
Theorem DEnv_app_cons_o : forall (denv1 denv2 : DEnv) (dobj : DObj),
    denv1 ++++ denv2 :::o dobj = (denv1 ++++ denv2) :::o dobj.
Proof. reflexivity. Qed.
#[export] Hint Rewrite DEnv_app_cons_s DEnv_app_cons_a DEnv_app_cons_x DEnv_app_cons_o : core.

(** Cons-to-one rewrites (norm) *)
Theorem DEnv_cons_s_one (denv : DEnv) (dskA : dskvar) :
    denv :::s dskA = denv ++++ <dskA>ds.
Proof. crush. Qed.
Theorem DEnv_cons_a_one (denv : DEnv) (a : A) :
    denv :::a a = denv ++++ <a>da.
Proof. induction a; crush. Qed.
Theorem DEnv_cons_x_one (denv : DEnv) (x : termvar) (dsch : DSch) :
    denv :::x x :- dsch = denv ++++ <x :- dsch>dx.
Proof. crush. Qed.
Theorem DEnv_cons_o_one (denv : DEnv) (dobj : DObj) :
    denv :::o dobj = denv ++++ <dobj>do.
Proof. crush. Qed.
#[export] Hint Rewrite DEnv_cons_s_one DEnv_cons_a_one DEnv_cons_x_one DEnv_cons_o_one : norm.

Theorem DEnv_onea_app_split (da1 da2 : DA) :
    <da2 ++ da1>da = <da1>da ++++ <da2>da.
Proof. induction da2; crush. Qed.
#[export] Hint Rewrite DEnv_onea_app_split : norm.

Theorem DEnv_cons_da_app_split : forall (da1 da2 : DA) (denv : DEnv),
    denv :::a (da2 ++ da1) = denv :::a da1 :::a da2.
Proof. induction da2; crush. Qed.

(*** GEnv instance *)
Module DEnv_E <: GEnv.
  Definition E : Type := DEnv.
  Definition S : Type := DSch.
  Definition O : Type := DObj.

  Definition Empty :                 E := DEnv_Empty.
  Definition Skol  : E -> atom ->      E := DEnv_DSkol.
  Definition Aa    : E -> list atom -> E := DEnv_DA.
  Definition Var   : E -> atom -> S ->  E := DEnv_DVar.
  Definition Obj   : E -> O ->         E := DEnv_DObj.

  Definition oneS : atom ->      E := oneDS.
  Definition oneA : list atom -> E := oneDA.
  Definition oneX : atom -> S ->  E := oneDX.
  Definition oneO : O ->         E := oneDO.

  Definition app : E -> E -> E := DEnv_app.

  Definition E_cons_one_s : forall (e : E) (skA : atom),
      Skol e skA = app e (oneS skA) := DEnv_cons_s_one.
  Definition E_cons_one_a : forall (e : E) (a : list atom),
      Aa e a = app e (oneA a) := DEnv_cons_a_one.
  Definition E_cons_one_x : forall (e : E) (x : atom) (s : S),
      Var e x s = app e (oneX x s) := DEnv_cons_x_one.
  Definition E_cons_one_o : forall (e : E) (o : O),
      Obj e o = app e (oneO o) := DEnv_cons_o_one.

  Definition E_app_nil_r : forall (e : E),
      app e Empty = e := DEnv_app_nil_r.
  Definition E_app_nil_l : forall (e : E),
      app Empty e = e := DEnv_app_nil_l.
End DEnv_E.

(*** DEnv_(sub/eq) *)
(* Def *)
Definition DEnv_sub (denv1 denv2 : DEnv) :=
    DEnv_dskvars denv1 [<=] DEnv_dskvars denv2.
#[export] Hint Unfold DEnv_sub : core.

Notation "A [<=]de B" := (DEnv_sub A B) (at level 65, format "A  [<=]de  B").

(* Instance *)
Theorem DEnv_sub_refl : Reflexive DEnv_sub.
Proof. crush. Qed.
Theorem DEnv_sub_trans : Transitive DEnv_sub.
Proof. unfold Transitive, DEnv_sub. crush. Qed.
#[export] Hint Resolve DEnv_sub_refl : core.

Theorem DEnv_sub_app : forall (denv1 denv1' denv2 denv2' : DEnv),
    denv1 [<=]de denv1'
  -> denv2 [<=]de denv2'
  -> denv1 ++++ denv2 [<=]de denv1' ++++ denv2'.
Proof. autounfold. intros. rewr. subst. fsetdec. Qed.
#[export] Hint Resolve DEnv_sub_app : core.
#[export] Instance DEnv_sub_app_proper : Proper (DEnv_sub ==> DEnv_sub ==> DEnv_sub) DEnv_app.
Proof. crush. Qed.

Module DEnv_sub_subrel <: GE_subrel list_sub_subrel DEnv_E.
  Definition R : DEnv -> DEnv -> Prop := DEnv_sub.

  Definition refl  : Reflexive  R := DEnv_sub_refl.
  Definition trans : Transitive R := DEnv_sub_trans.

  Theorem R_empty : forall (denv : DEnv), R ▪ denv. unfold R. crush. Qed.
  Theorem R_emptyA : forall (denv : DEnv), R (oneDA []) denv. unfold R. unfold DEnv_sub. crush. Qed.

  Definition proper : Proper (R ==> R ==> R) DEnv_app := DEnv_sub_app_proper.

  Theorem R_oneAa : forall (da1 da2 : DA), list_sub_subrel.R da1 da2 -> R (oneDA da1) (oneDA da2).
    unfold R, DEnv_sub, list_sub_subrel.R, DEnv_dskvars. intros. rewr. assumption.
  Qed.

  Definition E_cons_anil : forall (denv : DEnv),
      R denv (denv :::a []). intros. rewrite DEnv_cons_anil. apply DEnv_sub_refl. Qed.
End DEnv_sub_subrel.

Module Export DEnv_sub_subrel_facts := GE_subrel_facts list_sub_subrel DEnv_E DEnv_sub_subrel.
#[export] Hint Extern 1 (DEnv_sub _ _) => fold DEnv_sub_subrel.R : core.

(** DEnv_eq *)
(* Def *)
Definition DEnv_eq (denv1 denv2 : DEnv) :=
    DEnv_dskvars denv1 [=] DEnv_dskvars denv2.
#[export] Hint Unfold DEnv_eq : core.

Notation "A [=]de B" := (DEnv_eq A B) (at level 65, format "A  [=]de  B").

(* Instance *)
Theorem DEnv_eq_refl : Reflexive DEnv_eq.
Proof. crush. Qed.
Theorem DEnv_eq_trans : Transitive DEnv_eq.
Proof. unfold Transitive, DEnv_eq. crush. Qed.
Theorem DEnv_eq_symm : Symmetric DEnv_eq.
Proof. crush. Qed.
#[export] Hint Resolve DEnv_eq_refl DEnv_eq_symm : core.

Theorem DEnv_eq_app : forall (denv1 denv1' denv2 denv2' : DEnv),
    denv1 [=]de denv1'
  -> denv2 [=]de denv2'
  -> denv1 ++++ denv2 [=]de denv1' ++++ denv2'.
Proof. autounfold. intros. rewr. subst. fsetdec. Qed.
#[export] Hint Resolve DEnv_eq_app : core.
#[export] Instance DEnv_eq_app_proper : Proper (DEnv_eq ==> DEnv_eq ==> DEnv_eq) DEnv_app.
Proof. crush. Qed.

Module DEnv_eq_eqrel <: GE_eqrel list_eq_eqrel DEnv_E.
  Definition R : DEnv -> DEnv -> Prop := DEnv_eq.

  Definition refl  : Reflexive  R := DEnv_eq_refl.
  Definition trans : Transitive R := DEnv_eq_trans.
  Definition symm  : Symmetric  R := DEnv_eq_symm.

  Definition proper : Proper (R ==> R ==> R) DEnv_app := DEnv_eq_app_proper.

  Theorem R_oneAa : forall (da1 da2 : DA), list_eq_eqrel.R da1 da2 -> R (oneDA da1) (oneDA da2).
    unfold R, DEnv_eq, list_eq_eqrel.R, DEnv_dskvars. intros. rewr. assumption.
  Qed.
End DEnv_eq_eqrel.

Module Export DEnv_eq_eqrel_facts := GE_eqrel_facts list_eq_eqrel DEnv_E DEnv_eq_eqrel.
#[export] Hint Extern 1 (DEnv_eq _ _) => fold DEnv_eq_eqrel.R : core.

(* Conversions *)
Theorem DEnv_eq_sub : forall (denv1 denv2 : DEnv),
    denv1 [=]de denv2
  -> denv1 [<=]de denv2.
Proof. crush. Qed.
Theorem DEnv_eq_sub' : forall (denv1 denv2 : DEnv),
    denv1 [=]de denv2
  -> denv2 [<=]de denv1.
Proof. crush. Qed.
#[export] Hint Resolve DEnv_eq_sub DEnv_eq_sub' : core.

(*** DEnv_dx_(sub/eq) *)
(** DEnv_dx_sub *)
(* Def *)
Definition DEnv_dx_sub (denv1 denv2 : DEnv) :=
    DEnv_bindings denv1 ⟪<=⟫ DEnv_bindings denv2.
#[export] Hint Unfold DEnv_dx_sub : core.
Notation "A [<=]dx B" := (DEnv_dx_sub A B) (at level 65, format "A  [<=]dx  B").

(* Instance *)
Theorem DEnv_dx_sub_refl : Reflexive DEnv_dx_sub.
Proof. crush. Qed.
Theorem DEnv_dx_sub_trans : Transitive DEnv_dx_sub.
Proof. unfold Transitive, DEnv_dx_sub. crush. Qed.
#[export] Hint Resolve DEnv_dx_sub_refl : core.

Theorem DEnv_dx_sub_app : forall (denv1 denv1' denv2 denv2' : DEnv),
    denv1 [<=]dx denv1'
  -> denv2 [<=]dx denv2'
  -> denv1 ++++ denv2 [<=]dx denv1' ++++ denv2'.
Proof. autounfold. intros. rewr. fsetdec'. Qed.
#[export] Hint Resolve DEnv_dx_sub_app : core.
#[export] Instance DEnv_dx_sub_app_proper :    Proper (DEnv_dx_sub ==> DEnv_dx_sub ==> DEnv_dx_sub) DEnv_app.
Proof. crush. Qed.

Module DEnv_dx_sub_subrel <: GE_subrel Trivial_List_rel DEnv_E.
  Definition R : DEnv -> DEnv -> Prop := DEnv_dx_sub.

  Definition refl  : Reflexive  R := DEnv_dx_sub_refl.
  Definition trans : Transitive R := DEnv_dx_sub_trans.

  Theorem R_empty : forall (denv : DEnv), R ▪ denv. unfold R, DEnv_dx_sub. rewr. intros. fsetdec'. Qed.
  Theorem R_emptyA : forall (denv : DEnv), R (oneDA []) denv. intros. unfold R. autounfold. rewr. fsetdec'. Qed.

  Definition proper : Proper (R ==> R ==> R) DEnv_app := DEnv_dx_sub_app_proper.

  Theorem R_oneAa : forall (da1 da2 : DA), Trivial_List_rel.R da1 da2 -> R (oneDA da1) (oneDA da2).
    unfold R, DEnv_dx_sub, list_sub_subrel.R, DEnv_dskvars. intros. rewr. reflexivity.
  Qed.

  Definition E_cons_anil : forall (denv : DEnv),
      R denv (denv :::a []). intros. rewrite DEnv_cons_anil. apply DEnv_dx_sub_refl. Qed.
End DEnv_dx_sub_subrel.

Module Export DEnv_dx_sub_subrel_facts := GE_subrel_facts Trivial_List_rel DEnv_E DEnv_dx_sub_subrel.
#[export] Hint Extern 1 (DEnv_dx_sub _ _) => fold DEnv_dx_sub_subrel.R : core.

(** DEnv_dx_eq *)
Definition DEnv_dx_eq (denv1 denv2 : DEnv) :=
    DEnv_bindings denv1 ⟪=⟫ DEnv_bindings denv2.
#[export] Hint Unfold DEnv_dx_eq : core.
Notation "A [=]dx B" := (DEnv_dx_eq A B) (at level 65, format "A  [=]dx  B").

(* Instance *)
Theorem DEnv_dx_eq_refl : Reflexive DEnv_dx_eq.
Proof. crush. Qed.
Theorem DEnv_dx_eq_trans : Transitive DEnv_dx_eq.
Proof. unfold Transitive, DEnv_dx_eq. crush. Qed.
Theorem DEnv_dx_eq_symm : Symmetric DEnv_dx_eq.
Proof. crush. Qed.
#[export] Hint Resolve DEnv_dx_eq_refl : core.

Theorem DEnv_dx_eq_app : forall (denv1 denv1' denv2 denv2' : DEnv),
    denv1 [=]dx denv1'
  -> denv2 [=]dx denv2'
  -> denv1 ++++ denv2 [=]dx denv1' ++++ denv2'.
Proof. autounfold. intros. rewr. fsetdec'. Qed.
#[export] Hint Resolve DEnv_dx_eq_app : core.
#[export] Instance DEnv_dx_eq_app_proper :    Proper (DEnv_dx_eq ==> DEnv_dx_eq ==> DEnv_dx_eq) DEnv_app.
Proof. crush. Qed.

Module DEnv_dx_eq_eqrel <: GE_eqrel Trivial_List_rel DEnv_E.
  Definition R : DEnv -> DEnv -> Prop := DEnv_dx_eq.

  Definition refl  : Reflexive  R := DEnv_dx_eq_refl.
  Definition trans : Transitive R := DEnv_dx_eq_trans.
  Definition symm  : Symmetric  R := DEnv_dx_eq_symm.

  Definition proper : Proper (R ==> R ==> R) DEnv_app := DEnv_dx_eq_app_proper.

  Theorem R_oneAa : forall (da1 da2 : DA), Trivial_List_rel.R da1 da2 -> R (oneDA da1) (oneDA da2).
    unfold R, DEnv_dx_eq, list_sub_subrel.R, DEnv_dskvars. intros. rewr. reflexivity.
  Qed.
End DEnv_dx_eq_eqrel.

Module Export DEnv_dx_eq_eqrel_facts := GE_eqrel_facts Trivial_List_rel DEnv_E DEnv_dx_eq_eqrel.
#[export] Hint Extern 1 (DEnv_dx_eq _ _) => fold DEnv_dx_eq_eqrel.R : core.

(* Conversions *)
Theorem DEnv_dx_eq_sub : forall (denv1 denv2 : DEnv),
    denv1 [=]dx denv2
  -> denv1 [<=]dx denv2.
Proof. autounfold. crush. Qed.
Theorem DEnv_dx_eq_sub' : forall (denv1 denv2 : DEnv),
    denv1 [=]dx denv2
  -> denv2 [<=]dx denv1.
Proof. autounfold. crush. Qed.
#[export] Hint Resolve DEnv_dx_eq_sub DEnv_dx_eq_sub' : core.

(*** DEnv_dex_(sub/eq) *)
(** DEnv_dex_sub *)
(* Def *)
Definition DEnv_dex_sub (denv1 denv2 : DEnv) :=
    denv1 [<=]de denv2
  /\ denv1 [<=]dx denv2.
#[export] Hint Unfold DEnv_dex_sub : core.
Notation "A [<=]dex B" := (DEnv_dex_sub A B) (at level 65, format "A  [<=]dex  B").

(* Instance *)
Theorem DEnv_dex_sub_refl : Reflexive DEnv_dex_sub.
Proof. crush. Qed.
Theorem DEnv_dex_sub_trans : Transitive DEnv_dex_sub.
Proof. unfold Transitive, DEnv_dex_sub. crush. Qed.
#[export] Hint Resolve DEnv_dex_sub_refl : core.

Theorem DEnv_dex_sub_app : forall (denv1 denv1' denv2 denv2' : DEnv),
    denv1 [<=]dex denv1'
  -> denv2 [<=]dex denv2'
  -> denv1 ++++ denv2 [<=]dex denv1' ++++ denv2'.
Proof.
  unfold DEnv_dex_sub. intros. split.
  apply DEnv_sub_app_proper; crush.
  apply DEnv_dx_sub_app_proper; crush.
Qed.
#[export] Hint Resolve DEnv_dex_sub_app : core.
#[export] Instance DEnv_dex_sub_app_proper : Proper (DEnv_dex_sub ==> DEnv_dex_sub ==> DEnv_dex_sub) DEnv_app.
Proof. crush. Qed.

Module DEnv_dex_sub_subrel <: GE_subrel list_sub_subrel DEnv_E.
  Definition R : DEnv -> DEnv -> Prop := DEnv_dex_sub.

  Definition refl  : Reflexive  R := DEnv_dex_sub_refl.
  Definition trans : Transitive R := DEnv_dex_sub_trans.

  Theorem R_empty : forall (denv : DEnv), R ▪ denv. unfold R, DEnv_dex_sub, DEnv_sub, DEnv_dx_sub. rewr. intros. split; fsetdec'. Qed.
  Theorem R_emptyA : forall (denv : DEnv), R (oneDA []) denv. intros. unfold R. autounfold. rewr. split. crush. fsetdec'. Qed.

  Definition proper : Proper (R ==> R ==> R) DEnv_app := DEnv_dex_sub_app_proper.

  Theorem R_oneAa : forall (da1 da2 : DA), list_sub_subrel.R da1 da2 -> R (oneDA da1) (oneDA da2).
    unfold R, DEnv_dex_sub, DEnv_dx_sub, DEnv_sub, list_sub_subrel.R, DEnv_dskvars. intros. rewr. crush.
  Qed.

  Definition E_cons_anil : forall (denv : DEnv),
      R denv (denv :::a []). intros. rewrite DEnv_cons_anil. apply DEnv_dex_sub_refl. Qed.
End DEnv_dex_sub_subrel.

Module Export DEnv_dex_sub_subrel_facts := GE_subrel_facts list_sub_subrel DEnv_E DEnv_dex_sub_subrel.
#[export] Hint Extern 1 (DEnv_dex_sub _ _) => fold DEnv_dex_sub_subrel.R : core.

(* Conversion *)
Theorem DEnv_dex_sub_sub : forall (denv1 denv2 : DEnv),
    denv1 [<=]dex denv2
  -> denv1 [<=]de  denv2.
Proof. intros. unfold DEnv_dex_sub in H. jauto. Qed.
#[export] Hint Resolve DEnv_dex_sub_sub : core.

Theorem DEnv_dex_sub_dx_sub : forall (denv1 denv2 : DEnv),
    denv1 [<=]dex denv2
  -> denv1 [<=]dx  denv2.
Proof. intros. unfold DEnv_dex_sub in H. jauto. Qed.
#[export] Hint Resolve DEnv_dex_sub_dx_sub : core.

(** DEnv_dex_eq *)
(* Def *)
Definition DEnv_dex_eq (denv1 denv2 : DEnv) :=
    denv1 [=]de denv2
  /\ denv1 [=]dx denv2.
#[export] Hint Unfold DEnv_dex_eq : core.
Notation "A [=]dex B" := (DEnv_dex_eq A B) (at level 65, format "A  [=]dex  B").

(* Conversion to others *)
Theorem DEnv_dex_eq_sub : forall (denv1 denv2 : DEnv),
    denv1 [=]dex denv2
  -> denv1 [<=]dex denv2.
Proof. autounfold. crush. Qed.
Theorem DEnv_dex_eq_sub' : forall (denv1 denv2 : DEnv),
    denv1 [=]dex denv2
  -> denv2 [<=]dex denv1.
Proof. autounfold. crush. Qed.
#[export] Hint Resolve DEnv_dex_eq_sub DEnv_dex_eq_sub' : core.

(* Instance *)
Theorem DEnv_dex_eq_refl : Reflexive DEnv_dex_eq.
Proof. crush. Qed.
Theorem DEnv_dex_eq_trans : Transitive DEnv_dex_eq.
Proof. unfold Transitive, DEnv_dex_eq. crush. Qed.
Theorem DEnv_dex_eq_symm : Symmetric DEnv_dex_eq.
Proof. unfold Symmetric, DEnv_dex_eq. crush. Qed.
#[export] Hint Resolve DEnv_dex_eq_refl : core.

Theorem DEnv_dex_eq_app : forall (denv1 denv1' denv2 denv2' : DEnv),
    denv1 [=]dex denv1'
  -> denv2 [=]dex denv2'
  -> denv1 ++++ denv2 [=]dex denv1' ++++ denv2'.
Proof.
  unfold DEnv_dex_eq. intros. split.
  apply DEnv_eq_app_proper; crush.
  apply DEnv_dx_eq_app_proper; crush.
Qed.
#[export] Hint Resolve DEnv_dex_eq_app : core.
#[export] Instance DEnv_dex_eq_app_proper : Proper (DEnv_dex_eq ==> DEnv_dex_eq ==> DEnv_dex_eq) DEnv_app.
Proof. crush. Qed.

Module DEnv_dex_eq_eqrel <: GE_eqrel list_eq_eqrel DEnv_E.
  Definition R : DEnv -> DEnv -> Prop := DEnv_dex_eq.

  Definition refl  : Reflexive  R := DEnv_dex_eq_refl.
  Definition trans : Transitive R := DEnv_dex_eq_trans.
  Definition symm  : Symmetric  R := DEnv_dex_eq_symm.

  Definition proper : Proper (R ==> R ==> R) DEnv_app := DEnv_dex_eq_app_proper.

  Theorem R_oneAa : forall (da1 da2 : DA), list_eq_eqrel.R da1 da2 -> R (oneDA da1) (oneDA da2).
    unfold R, DEnv_dex_eq, DEnv_dx_eq, DEnv_eq, list_eq_eqrel.R, DEnv_dskvars. intros. rewr. crush.
  Qed.
End DEnv_dex_eq_eqrel.

Module Export DEnv_dex_eq_eqrel_facts := GE_eqrel_facts list_eq_eqrel DEnv_E DEnv_dex_eq_eqrel.
#[export] Hint Extern 1 (DEnv_dex_eq _ _) => fold DEnv_dex_eq_eqrel.R : core.

(*** rewr_derel *)
Ltac unfold_derel :=
           ( (try unfold DEnv_dex_sub     ); (try unfold DEnv_dx_sub     ); (try unfold DEnv_sub     )
           ; (try unfold DEnv_dex_eq      ); (try unfold DEnv_dx_eq      ); (try unfold DEnv_eq      ) ).
Tactic Notation "unfold_derel" "in" hyp(H) :=
           ( (try unfold DEnv_dex_sub in H); (try unfold DEnv_dx_sub in H); (try unfold DEnv_sub in H)
           ; (try unfold DEnv_dex_eq  in H); (try unfold DEnv_dx_eq  in H); (try unfold DEnv_eq  in H) ).
Tactic Notation "unfold_derel*" :=
           ( (try unfold DEnv_dex_sub in *); (try unfold DEnv_dx_sub in *); (try unfold DEnv_sub in *)
           ; (try unfold DEnv_dex_eq  in *); (try unfold DEnv_dx_eq  in *); (try unfold DEnv_eq  in *) ).

Ltac   fold_derel :=
           ( (try   fold DEnv_dex_sub     ); (try   fold DEnv_dx_sub     ); (try   fold DEnv_sub     )
           ; (try   fold DEnv_dex_eq      ); (try   fold DEnv_dx_eq      ); (try   fold DEnv_eq      ) ).
Tactic Notation   "fold_derel" "in" hyp(H) :=
           ( (try   fold DEnv_dex_sub in H); (try   fold DEnv_dx_sub in H); (try   fold DEnv_sub in H)
           ; (try   fold DEnv_dex_eq  in H); (try   fold DEnv_dx_eq  in H); (try   fold DEnv_eq  in H) ).
Tactic Notation   "fold_derel*" :=
           ( (try   fold DEnv_dex_sub in *); (try   fold DEnv_dx_sub in *); (try   fold DEnv_sub in *)
           ; (try   fold DEnv_dex_eq  in *); (try   fold DEnv_dx_eq  in *); (try   fold DEnv_eq  in *) ).

Ltac rewr_derel :=
  unfold_derel     ; progress rewr     ; fold_derel     .
Tactic Notation "rewr_derel" "in" hyp(H) :=
  unfold_derel in H; progress rewr in H; fold_derel in H.
Tactic Notation "rewr_derel*" :=
  unfold_derel*    ; progress rewr*    ; fold_derel*.

(*** Bindings to dschs *)
Theorem DEnv_bindings_DSchs_DEnv : forall (dsch : DSch) (denv : DEnv),
    (exists (x : termvar), DSchPSI.In (x, dsch) (DEnv_bindings denv)) <-> DSchSI.In dsch (DEnv_DSchs denv).
Proof.
  introv. induction denv; rewr*.
  - crush.
  - split; intros; destr. apply IHdenv. exists x. crush. forwards<: IHdenv. eassumption. destr. exists x. crush.
  - split; intros; destr.
    + rewr in H. indestr in H. destr.
      * forwards>: IHdenv. exists x0. assumption. fsetdec'.
      * fsetdec'.
    + indestr in H. destr.
      * forwards<: IHdenv. eassumption. destr. exists x0. crush.
      * exists x. rewr. fsetdec.
  - split; intros; destr. apply IHdenv. exists x. crush. forwards<: IHdenv. eassumption. destr. exists x. crush.
Qed.

Corollary DEnv_bindings_DSchs_DEnv1 : forall (dsch : DSch) (denv : DEnv) (x : termvar),
    DSchPSI.In (x, dsch) (DEnv_bindings denv)
  -> DSchSI.In dsch (DEnv_DSchs denv).
Proof. intros. apply DEnv_bindings_DSchs_DEnv. exists x. assumption. Qed.
#[export] Hint Resolve DEnv_bindings_DSchs_DEnv1 : core.
