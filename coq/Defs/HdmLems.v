Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export Defs.HdmDefs.

Local Set Warnings "-non-recursive". 

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme DTy_ind' := Induction for DTy Sort Prop.

Combined Scheme DTy_mutind from DTy_ind'.

Scheme DTy_rec' := Induction for DTy Sort Set.

Combined Scheme DTy_mutrec from DTy_rec'.

Scheme DSch_ind' := Induction for DSch Sort Prop.

Combined Scheme DSch_mutind from DSch_ind'.

Scheme DSch_rec' := Induction for DSch Sort Set.

Combined Scheme DSch_mutrec from DSch_rec'.

Scheme Ty_ind' := Induction for Ty Sort Prop.

Combined Scheme Ty_mutind from Ty_ind'.

Scheme Ty_rec' := Induction for Ty Sort Set.

Combined Scheme Ty_mutrec from Ty_rec'.

Scheme Sch_ind' := Induction for Sch Sort Prop.

Combined Scheme Sch_mutind from Sch_ind'.

Scheme Sch_rec' := Induction for Sch Sort Set.

Combined Scheme Sch_mutrec from Sch_rec'.

Scheme e_ind' := Induction for e Sort Prop.

Combined Scheme e_mutind from e_ind'.

Scheme e_rec' := Induction for e Sort Set.

Combined Scheme e_mutrec from e_rec'.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_DTy (DTy1 : DTy) {struct DTy1} : nat :=
  match DTy1 with
    | DT_SkVar_f dskA1 => 1
    | DT_SkVar_b n1 => 1
    | DT_Unit => 1
    | DT_Fun DTy2 DTy3 => 1 + (size_DTy DTy2) + (size_DTy DTy3)
  end.

Fixpoint size_DSch (DSch1 : DSch) {struct DSch1} : nat :=
  match DSch1 with
    | DS_Mono DTy1 => 1 + (size_DTy DTy1)
    | DS_Forall DSch2 => 1 + (size_DSch DSch2)
  end.

Fixpoint size_Ty (Ty1 : Ty) {struct Ty1} : nat :=
  match Ty1 with
    | T_SkVar_f skA1 => 1
    | T_SkVar_b n1 => 1
    | T_ExVar exA1 => 1
    | T_Unit => 1
    | T_Fun Ty2 Ty3 => 1 + (size_Ty Ty2) + (size_Ty Ty3)
  end.

Fixpoint size_Sch (Sch1 : Sch) {struct Sch1} : nat :=
  match Sch1 with
    | S_Mono Ty1 => 1 + (size_Ty Ty1)
    | S_Forall Sch2 => 1 + (size_Sch Sch2)
  end.

Fixpoint size_e (e1 : e) {struct e1} : nat :=
  match e1 with
    | e_Var_f x1 => 1
    | e_Var_b n1 => 1
    | e_Unit => 1
    | e_App e2 e3 => 1 + (size_e e2) + (size_e e3)
    | e_Lam e2 => 1 + (size_e e2)
    | e_Let e2 e3 => 1 + (size_e e2) + (size_e e3)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_DTy_wrt_DTy : nat -> DTy -> Prop :=
  | degree_wrt_DTy_DT_SkVar_f : forall n1 dskA1,
    degree_DTy_wrt_DTy n1 (DT_SkVar_f dskA1)
  | degree_wrt_DTy_DT_SkVar_b : forall n1 n2,
    lt n2 n1 ->
    degree_DTy_wrt_DTy n1 (DT_SkVar_b n2)
  | degree_wrt_DTy_DT_Unit : forall n1,
    degree_DTy_wrt_DTy n1 (DT_Unit)
  | degree_wrt_DTy_DT_Fun : forall n1 DTy1 DTy2,
    degree_DTy_wrt_DTy n1 DTy1 ->
    degree_DTy_wrt_DTy n1 DTy2 ->
    degree_DTy_wrt_DTy n1 (DT_Fun DTy1 DTy2).

Scheme degree_DTy_wrt_DTy_ind' := Induction for degree_DTy_wrt_DTy Sort Prop.

Combined Scheme degree_DTy_wrt_DTy_mutind from degree_DTy_wrt_DTy_ind'.

#[export] Hint Constructors degree_DTy_wrt_DTy : core lngen.

Inductive degree_DSch_wrt_DTy : nat -> DSch -> Prop :=
  | degree_wrt_DTy_DS_Mono : forall n1 DTy1,
    degree_DTy_wrt_DTy n1 DTy1 ->
    degree_DSch_wrt_DTy n1 (DS_Mono DTy1)
  | degree_wrt_DTy_DS_Forall : forall n1 DSch1,
    degree_DSch_wrt_DTy (S n1) DSch1 ->
    degree_DSch_wrt_DTy n1 (DS_Forall DSch1).

Scheme degree_DSch_wrt_DTy_ind' := Induction for degree_DSch_wrt_DTy Sort Prop.

Combined Scheme degree_DSch_wrt_DTy_mutind from degree_DSch_wrt_DTy_ind'.

#[export] Hint Constructors degree_DSch_wrt_DTy : core lngen.

Inductive degree_Ty_wrt_Ty : nat -> Ty -> Prop :=
  | degree_wrt_Ty_T_SkVar_f : forall n1 skA1,
    degree_Ty_wrt_Ty n1 (T_SkVar_f skA1)
  | degree_wrt_Ty_T_SkVar_b : forall n1 n2,
    lt n2 n1 ->
    degree_Ty_wrt_Ty n1 (T_SkVar_b n2)
  | degree_wrt_Ty_T_ExVar : forall n1 exA1,
    degree_Ty_wrt_Ty n1 (T_ExVar exA1)
  | degree_wrt_Ty_T_Unit : forall n1,
    degree_Ty_wrt_Ty n1 (T_Unit)
  | degree_wrt_Ty_T_Fun : forall n1 Ty1 Ty2,
    degree_Ty_wrt_Ty n1 Ty1 ->
    degree_Ty_wrt_Ty n1 Ty2 ->
    degree_Ty_wrt_Ty n1 (T_Fun Ty1 Ty2).

Scheme degree_Ty_wrt_Ty_ind' := Induction for degree_Ty_wrt_Ty Sort Prop.

Combined Scheme degree_Ty_wrt_Ty_mutind from degree_Ty_wrt_Ty_ind'.

#[export] Hint Constructors degree_Ty_wrt_Ty : core lngen.

Inductive degree_Sch_wrt_Ty : nat -> Sch -> Prop :=
  | degree_wrt_Ty_S_Mono : forall n1 Ty1,
    degree_Ty_wrt_Ty n1 Ty1 ->
    degree_Sch_wrt_Ty n1 (S_Mono Ty1)
  | degree_wrt_Ty_S_Forall : forall n1 Sch1,
    degree_Sch_wrt_Ty (S n1) Sch1 ->
    degree_Sch_wrt_Ty n1 (S_Forall Sch1).

Scheme degree_Sch_wrt_Ty_ind' := Induction for degree_Sch_wrt_Ty Sort Prop.

Combined Scheme degree_Sch_wrt_Ty_mutind from degree_Sch_wrt_Ty_ind'.

#[export] Hint Constructors degree_Sch_wrt_Ty : core lngen.

Inductive degree_e_wrt_e : nat -> e -> Prop :=
  | degree_wrt_e_e_Var_f : forall n1 x1,
    degree_e_wrt_e n1 (e_Var_f x1)
  | degree_wrt_e_e_Var_b : forall n1 n2,
    lt n2 n1 ->
    degree_e_wrt_e n1 (e_Var_b n2)
  | degree_wrt_e_e_Unit : forall n1,
    degree_e_wrt_e n1 (e_Unit)
  | degree_wrt_e_e_App : forall n1 e1 e2,
    degree_e_wrt_e n1 e1 ->
    degree_e_wrt_e n1 e2 ->
    degree_e_wrt_e n1 (e_App e1 e2)
  | degree_wrt_e_e_Lam : forall n1 e1,
    degree_e_wrt_e (S n1) e1 ->
    degree_e_wrt_e n1 (e_Lam e1)
  | degree_wrt_e_e_Let : forall n1 e1 e2,
    degree_e_wrt_e n1 e1 ->
    degree_e_wrt_e (S n1) e2 ->
    degree_e_wrt_e n1 (e_Let e1 e2).

Scheme degree_e_wrt_e_ind' := Induction for degree_e_wrt_e Sort Prop.

Combined Scheme degree_e_wrt_e_mutind from degree_e_wrt_e_ind'.

#[export] Hint Constructors degree_e_wrt_e : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_DTy : DTy -> Set :=
  | lc_set_DT_SkVar_f : forall dskA1,
    lc_set_DTy (DT_SkVar_f dskA1)
  | lc_set_DT_Unit :
    lc_set_DTy (DT_Unit)
  | lc_set_DT_Fun : forall DTy1 DTy2,
    lc_set_DTy DTy1 ->
    lc_set_DTy DTy2 ->
    lc_set_DTy (DT_Fun DTy1 DTy2).

Scheme lc_DTy_ind' := Induction for lc_DTy Sort Prop.

Combined Scheme lc_DTy_mutind from lc_DTy_ind'.

Scheme lc_set_DTy_ind' := Induction for lc_set_DTy Sort Prop.

Combined Scheme lc_set_DTy_mutind from lc_set_DTy_ind'.

Scheme lc_set_DTy_rec' := Induction for lc_set_DTy Sort Set.

Combined Scheme lc_set_DTy_mutrec from lc_set_DTy_rec'.

#[export] Hint Constructors lc_DTy : core lngen.

#[export] Hint Constructors lc_set_DTy : core lngen.

Inductive lc_set_DSch : DSch -> Set :=
  | lc_set_DS_Mono : forall DTy1,
    lc_set_DTy DTy1 ->
    lc_set_DSch (DS_Mono DTy1)
  | lc_set_DS_Forall : forall DSch1,
    (forall dskA1 : dskvar, lc_set_DSch (open_DSch_wrt_DTy DSch1 (DT_SkVar_f dskA1))) ->
    lc_set_DSch (DS_Forall DSch1).

Scheme lc_DSch_ind' := Induction for lc_DSch Sort Prop.

Combined Scheme lc_DSch_mutind from lc_DSch_ind'.

Scheme lc_set_DSch_ind' := Induction for lc_set_DSch Sort Prop.

Combined Scheme lc_set_DSch_mutind from lc_set_DSch_ind'.

Scheme lc_set_DSch_rec' := Induction for lc_set_DSch Sort Set.

Combined Scheme lc_set_DSch_mutrec from lc_set_DSch_rec'.

#[export] Hint Constructors lc_DSch : core lngen.

#[export] Hint Constructors lc_set_DSch : core lngen.

Inductive lc_set_Ty : Ty -> Set :=
  | lc_set_T_SkVar_f : forall skA1,
    lc_set_Ty (T_SkVar_f skA1)
  | lc_set_T_ExVar : forall exA1,
    lc_set_Ty (T_ExVar exA1)
  | lc_set_T_Unit :
    lc_set_Ty (T_Unit)
  | lc_set_T_Fun : forall Ty1 Ty2,
    lc_set_Ty Ty1 ->
    lc_set_Ty Ty2 ->
    lc_set_Ty (T_Fun Ty1 Ty2).

Scheme lc_Ty_ind' := Induction for lc_Ty Sort Prop.

Combined Scheme lc_Ty_mutind from lc_Ty_ind'.

Scheme lc_set_Ty_ind' := Induction for lc_set_Ty Sort Prop.

Combined Scheme lc_set_Ty_mutind from lc_set_Ty_ind'.

Scheme lc_set_Ty_rec' := Induction for lc_set_Ty Sort Set.

Combined Scheme lc_set_Ty_mutrec from lc_set_Ty_rec'.

#[export] Hint Constructors lc_Ty : core lngen.

#[export] Hint Constructors lc_set_Ty : core lngen.

Inductive lc_set_Sch : Sch -> Set :=
  | lc_set_S_Mono : forall Ty1,
    lc_set_Ty Ty1 ->
    lc_set_Sch (S_Mono Ty1)
  | lc_set_S_Forall : forall Sch1,
    (forall skA1 : skvar, lc_set_Sch (open_Sch_wrt_Ty Sch1 (T_SkVar_f skA1))) ->
    lc_set_Sch (S_Forall Sch1).

Scheme lc_Sch_ind' := Induction for lc_Sch Sort Prop.

Combined Scheme lc_Sch_mutind from lc_Sch_ind'.

Scheme lc_set_Sch_ind' := Induction for lc_set_Sch Sort Prop.

Combined Scheme lc_set_Sch_mutind from lc_set_Sch_ind'.

Scheme lc_set_Sch_rec' := Induction for lc_set_Sch Sort Set.

Combined Scheme lc_set_Sch_mutrec from lc_set_Sch_rec'.

#[export] Hint Constructors lc_Sch : core lngen.

#[export] Hint Constructors lc_set_Sch : core lngen.

Inductive lc_set_e : e -> Set :=
  | lc_set_e_Var_f : forall x1,
    lc_set_e (e_Var_f x1)
  | lc_set_e_Unit :
    lc_set_e (e_Unit)
  | lc_set_e_App : forall e1 e2,
    lc_set_e e1 ->
    lc_set_e e2 ->
    lc_set_e (e_App e1 e2)
  | lc_set_e_Lam : forall e1,
    (forall x1 : termvar, lc_set_e (open_e_wrt_e e1 (e_Var_f x1))) ->
    lc_set_e (e_Lam e1)
  | lc_set_e_Let : forall e1 e2,
    lc_set_e e1 ->
    (forall x1 : termvar, lc_set_e (open_e_wrt_e e2 (e_Var_f x1))) ->
    lc_set_e (e_Let e1 e2).

Scheme lc_e_ind' := Induction for lc_e Sort Prop.

Combined Scheme lc_e_mutind from lc_e_ind'.

Scheme lc_set_e_ind' := Induction for lc_set_e Sort Prop.

Combined Scheme lc_set_e_mutind from lc_set_e_ind'.

Scheme lc_set_e_rec' := Induction for lc_set_e Sort Set.

Combined Scheme lc_set_e_mutrec from lc_set_e_rec'.

#[export] Hint Constructors lc_e : core lngen.

#[export] Hint Constructors lc_set_e : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_DTy_wrt_DTy DTy1 := forall dskA1, lc_DTy (open_DTy_wrt_DTy DTy1 (DT_SkVar_f dskA1)).

#[export] Hint Unfold body_DTy_wrt_DTy : core.

Definition body_DSch_wrt_DTy DSch1 := forall dskA1, lc_DSch (open_DSch_wrt_DTy DSch1 (DT_SkVar_f dskA1)).

#[export] Hint Unfold body_DSch_wrt_DTy : core.

Definition body_Ty_wrt_Ty Ty1 := forall skA1, lc_Ty (open_Ty_wrt_Ty Ty1 (T_SkVar_f skA1)).

#[export] Hint Unfold body_Ty_wrt_Ty : core.

Definition body_Sch_wrt_Ty Sch1 := forall skA1, lc_Sch (open_Sch_wrt_Ty Sch1 (T_SkVar_f skA1)).

#[export] Hint Unfold body_Sch_wrt_Ty : core.

Definition body_e_wrt_e e1 := forall x1, lc_e (open_e_wrt_e e1 (e_Var_f x1)).

#[export] Hint Unfold body_e_wrt_e : core.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

(** Roger: changed out pluss_le_compat for Nat.add_le_mono because of *)
(** deprecation, see CoqLNOutputDefinitions.hs *)

(*#[export] Hint Resolve plus_le_compat : *)
#[export] Hint Resolve Nat.add_le_mono : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_DTy_min_mutual :
(forall DTy1, 1 <= size_DTy DTy1).
Proof.
apply_mutual_ind DTy_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_DTy_min :
forall DTy1, 1 <= size_DTy DTy1.
Proof.
pose proof size_DTy_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_DTy_min : lngen.

(* begin hide *)

Lemma size_DSch_min_mutual :
(forall DSch1, 1 <= size_DSch DSch1).
Proof.
apply_mutual_ind DSch_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_DSch_min :
forall DSch1, 1 <= size_DSch DSch1.
Proof.
pose proof size_DSch_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_DSch_min : lngen.

(* begin hide *)

Lemma size_Ty_min_mutual :
(forall Ty1, 1 <= size_Ty Ty1).
Proof.
apply_mutual_ind Ty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_Ty_min :
forall Ty1, 1 <= size_Ty Ty1.
Proof.
pose proof size_Ty_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Ty_min : lngen.

(* begin hide *)

Lemma size_Sch_min_mutual :
(forall Sch1, 1 <= size_Sch Sch1).
Proof.
apply_mutual_ind Sch_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_Sch_min :
forall Sch1, 1 <= size_Sch Sch1.
Proof.
pose proof size_Sch_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Sch_min : lngen.

(* begin hide *)

Lemma size_e_min_mutual :
(forall e1, 1 <= size_e e1).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_e_min :
forall e1, 1 <= size_e e1.
Proof.
pose proof size_e_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_e_min : lngen.

(* begin hide *)

Lemma size_DTy_close_DTy_wrt_DTy_rec_mutual :
(forall DTy1 dskA1 n1,
  size_DTy (close_DTy_wrt_DTy_rec n1 dskA1 DTy1) = size_DTy DTy1).
Proof.
apply_mutual_ind DTy_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_DTy_close_DTy_wrt_DTy_rec :
forall DTy1 dskA1 n1,
  size_DTy (close_DTy_wrt_DTy_rec n1 dskA1 DTy1) = size_DTy DTy1.
Proof.
pose proof size_DTy_close_DTy_wrt_DTy_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_DTy_close_DTy_wrt_DTy_rec : lngen.
#[export] Hint Rewrite size_DTy_close_DTy_wrt_DTy_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_DSch_close_DSch_wrt_DTy_rec_mutual :
(forall DSch1 dskA1 n1,
  size_DSch (close_DSch_wrt_DTy_rec n1 dskA1 DSch1) = size_DSch DSch1).
Proof.
apply_mutual_ind DSch_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_DSch_close_DSch_wrt_DTy_rec :
forall DSch1 dskA1 n1,
  size_DSch (close_DSch_wrt_DTy_rec n1 dskA1 DSch1) = size_DSch DSch1.
Proof.
pose proof size_DSch_close_DSch_wrt_DTy_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_DSch_close_DSch_wrt_DTy_rec : lngen.
#[export] Hint Rewrite size_DSch_close_DSch_wrt_DTy_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Ty_close_Ty_wrt_Ty_rec_mutual :
(forall Ty1 skA1 n1,
  size_Ty (close_Ty_wrt_Ty_rec n1 skA1 Ty1) = size_Ty Ty1).
Proof.
apply_mutual_ind Ty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Ty_close_Ty_wrt_Ty_rec :
forall Ty1 skA1 n1,
  size_Ty (close_Ty_wrt_Ty_rec n1 skA1 Ty1) = size_Ty Ty1.
Proof.
pose proof size_Ty_close_Ty_wrt_Ty_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Ty_close_Ty_wrt_Ty_rec : lngen.
#[export] Hint Rewrite size_Ty_close_Ty_wrt_Ty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Sch_close_Sch_wrt_Ty_rec_mutual :
(forall Sch1 skA1 n1,
  size_Sch (close_Sch_wrt_Ty_rec n1 skA1 Sch1) = size_Sch Sch1).
Proof.
apply_mutual_ind Sch_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Sch_close_Sch_wrt_Ty_rec :
forall Sch1 skA1 n1,
  size_Sch (close_Sch_wrt_Ty_rec n1 skA1 Sch1) = size_Sch Sch1.
Proof.
pose proof size_Sch_close_Sch_wrt_Ty_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Sch_close_Sch_wrt_Ty_rec : lngen.
#[export] Hint Rewrite size_Sch_close_Sch_wrt_Ty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_e_close_e_wrt_e_rec_mutual :
(forall e1 x1 n1,
  size_e (close_e_wrt_e_rec n1 x1 e1) = size_e e1).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_e_close_e_wrt_e_rec :
forall e1 x1 n1,
  size_e (close_e_wrt_e_rec n1 x1 e1) = size_e e1.
Proof.
pose proof size_e_close_e_wrt_e_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_e_close_e_wrt_e_rec : lngen.
#[export] Hint Rewrite size_e_close_e_wrt_e_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_DTy_close_DTy_wrt_DTy :
forall DTy1 dskA1,
  size_DTy (close_DTy_wrt_DTy dskA1 DTy1) = size_DTy DTy1.
Proof.
unfold close_DTy_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve size_DTy_close_DTy_wrt_DTy : lngen.
#[export] Hint Rewrite size_DTy_close_DTy_wrt_DTy using solve [auto] : lngen.

Lemma size_DSch_close_DSch_wrt_DTy :
forall DSch1 dskA1,
  size_DSch (close_DSch_wrt_DTy dskA1 DSch1) = size_DSch DSch1.
Proof.
unfold close_DSch_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve size_DSch_close_DSch_wrt_DTy : lngen.
#[export] Hint Rewrite size_DSch_close_DSch_wrt_DTy using solve [auto] : lngen.

Lemma size_Ty_close_Ty_wrt_Ty :
forall Ty1 skA1,
  size_Ty (close_Ty_wrt_Ty skA1 Ty1) = size_Ty Ty1.
Proof.
unfold close_Ty_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve size_Ty_close_Ty_wrt_Ty : lngen.
#[export] Hint Rewrite size_Ty_close_Ty_wrt_Ty using solve [auto] : lngen.

Lemma size_Sch_close_Sch_wrt_Ty :
forall Sch1 skA1,
  size_Sch (close_Sch_wrt_Ty skA1 Sch1) = size_Sch Sch1.
Proof.
unfold close_Sch_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve size_Sch_close_Sch_wrt_Ty : lngen.
#[export] Hint Rewrite size_Sch_close_Sch_wrt_Ty using solve [auto] : lngen.

Lemma size_e_close_e_wrt_e :
forall e1 x1,
  size_e (close_e_wrt_e x1 e1) = size_e e1.
Proof.
unfold close_e_wrt_e; default_simp.
Qed.

#[export] Hint Resolve size_e_close_e_wrt_e : lngen.
#[export] Hint Rewrite size_e_close_e_wrt_e using solve [auto] : lngen.

(* begin hide *)

Lemma size_DTy_open_DTy_wrt_DTy_rec_mutual :
(forall DTy1 DTy2 n1,
  size_DTy DTy1 <= size_DTy (open_DTy_wrt_DTy_rec n1 DTy2 DTy1)).
Proof.
apply_mutual_ind DTy_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_DTy_open_DTy_wrt_DTy_rec :
forall DTy1 DTy2 n1,
  size_DTy DTy1 <= size_DTy (open_DTy_wrt_DTy_rec n1 DTy2 DTy1).
Proof.
pose proof size_DTy_open_DTy_wrt_DTy_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_DTy_open_DTy_wrt_DTy_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_DSch_open_DSch_wrt_DTy_rec_mutual :
(forall DSch1 DTy1 n1,
  size_DSch DSch1 <= size_DSch (open_DSch_wrt_DTy_rec n1 DTy1 DSch1)).
Proof.
apply_mutual_ind DSch_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_DSch_open_DSch_wrt_DTy_rec :
forall DSch1 DTy1 n1,
  size_DSch DSch1 <= size_DSch (open_DSch_wrt_DTy_rec n1 DTy1 DSch1).
Proof.
pose proof size_DSch_open_DSch_wrt_DTy_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_DSch_open_DSch_wrt_DTy_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Ty_open_Ty_wrt_Ty_rec_mutual :
(forall Ty1 Ty2 n1,
  size_Ty Ty1 <= size_Ty (open_Ty_wrt_Ty_rec n1 Ty2 Ty1)).
Proof.
apply_mutual_ind Ty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Ty_open_Ty_wrt_Ty_rec :
forall Ty1 Ty2 n1,
  size_Ty Ty1 <= size_Ty (open_Ty_wrt_Ty_rec n1 Ty2 Ty1).
Proof.
pose proof size_Ty_open_Ty_wrt_Ty_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Ty_open_Ty_wrt_Ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Sch_open_Sch_wrt_Ty_rec_mutual :
(forall Sch1 Ty1 n1,
  size_Sch Sch1 <= size_Sch (open_Sch_wrt_Ty_rec n1 Ty1 Sch1)).
Proof.
apply_mutual_ind Sch_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Sch_open_Sch_wrt_Ty_rec :
forall Sch1 Ty1 n1,
  size_Sch Sch1 <= size_Sch (open_Sch_wrt_Ty_rec n1 Ty1 Sch1).
Proof.
pose proof size_Sch_open_Sch_wrt_Ty_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Sch_open_Sch_wrt_Ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_e_open_e_wrt_e_rec_mutual :
(forall e1 e2 n1,
  size_e e1 <= size_e (open_e_wrt_e_rec n1 e2 e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_e_open_e_wrt_e_rec :
forall e1 e2 n1,
  size_e e1 <= size_e (open_e_wrt_e_rec n1 e2 e1).
Proof.
pose proof size_e_open_e_wrt_e_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_e_open_e_wrt_e_rec : lngen.

(* end hide *)

Lemma size_DTy_open_DTy_wrt_DTy :
forall DTy1 DTy2,
  size_DTy DTy1 <= size_DTy (open_DTy_wrt_DTy DTy1 DTy2).
Proof.
unfold open_DTy_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve size_DTy_open_DTy_wrt_DTy : lngen.

Lemma size_DSch_open_DSch_wrt_DTy :
forall DSch1 DTy1,
  size_DSch DSch1 <= size_DSch (open_DSch_wrt_DTy DSch1 DTy1).
Proof.
unfold open_DSch_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve size_DSch_open_DSch_wrt_DTy : lngen.

Lemma size_Ty_open_Ty_wrt_Ty :
forall Ty1 Ty2,
  size_Ty Ty1 <= size_Ty (open_Ty_wrt_Ty Ty1 Ty2).
Proof.
unfold open_Ty_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve size_Ty_open_Ty_wrt_Ty : lngen.

Lemma size_Sch_open_Sch_wrt_Ty :
forall Sch1 Ty1,
  size_Sch Sch1 <= size_Sch (open_Sch_wrt_Ty Sch1 Ty1).
Proof.
unfold open_Sch_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve size_Sch_open_Sch_wrt_Ty : lngen.

Lemma size_e_open_e_wrt_e :
forall e1 e2,
  size_e e1 <= size_e (open_e_wrt_e e1 e2).
Proof.
unfold open_e_wrt_e; default_simp.
Qed.

#[export] Hint Resolve size_e_open_e_wrt_e : lngen.

(* begin hide *)

Lemma size_DTy_open_DTy_wrt_DTy_rec_var_mutual :
(forall DTy1 dskA1 n1,
  size_DTy (open_DTy_wrt_DTy_rec n1 (DT_SkVar_f dskA1) DTy1) = size_DTy DTy1).
Proof.
apply_mutual_ind DTy_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_DTy_open_DTy_wrt_DTy_rec_var :
forall DTy1 dskA1 n1,
  size_DTy (open_DTy_wrt_DTy_rec n1 (DT_SkVar_f dskA1) DTy1) = size_DTy DTy1.
Proof.
pose proof size_DTy_open_DTy_wrt_DTy_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_DTy_open_DTy_wrt_DTy_rec_var : lngen.
#[export] Hint Rewrite size_DTy_open_DTy_wrt_DTy_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_DSch_open_DSch_wrt_DTy_rec_var_mutual :
(forall DSch1 dskA1 n1,
  size_DSch (open_DSch_wrt_DTy_rec n1 (DT_SkVar_f dskA1) DSch1) = size_DSch DSch1).
Proof.
apply_mutual_ind DSch_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_DSch_open_DSch_wrt_DTy_rec_var :
forall DSch1 dskA1 n1,
  size_DSch (open_DSch_wrt_DTy_rec n1 (DT_SkVar_f dskA1) DSch1) = size_DSch DSch1.
Proof.
pose proof size_DSch_open_DSch_wrt_DTy_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_DSch_open_DSch_wrt_DTy_rec_var : lngen.
#[export] Hint Rewrite size_DSch_open_DSch_wrt_DTy_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Ty_open_Ty_wrt_Ty_rec_var_mutual :
(forall Ty1 skA1 n1,
  size_Ty (open_Ty_wrt_Ty_rec n1 (T_SkVar_f skA1) Ty1) = size_Ty Ty1).
Proof.
apply_mutual_ind Ty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Ty_open_Ty_wrt_Ty_rec_var :
forall Ty1 skA1 n1,
  size_Ty (open_Ty_wrt_Ty_rec n1 (T_SkVar_f skA1) Ty1) = size_Ty Ty1.
Proof.
pose proof size_Ty_open_Ty_wrt_Ty_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Ty_open_Ty_wrt_Ty_rec_var : lngen.
#[export] Hint Rewrite size_Ty_open_Ty_wrt_Ty_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Sch_open_Sch_wrt_Ty_rec_var_mutual :
(forall Sch1 skA1 n1,
  size_Sch (open_Sch_wrt_Ty_rec n1 (T_SkVar_f skA1) Sch1) = size_Sch Sch1).
Proof.
apply_mutual_ind Sch_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Sch_open_Sch_wrt_Ty_rec_var :
forall Sch1 skA1 n1,
  size_Sch (open_Sch_wrt_Ty_rec n1 (T_SkVar_f skA1) Sch1) = size_Sch Sch1.
Proof.
pose proof size_Sch_open_Sch_wrt_Ty_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Sch_open_Sch_wrt_Ty_rec_var : lngen.
#[export] Hint Rewrite size_Sch_open_Sch_wrt_Ty_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_e_open_e_wrt_e_rec_var_mutual :
(forall e1 x1 n1,
  size_e (open_e_wrt_e_rec n1 (e_Var_f x1) e1) = size_e e1).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_e_open_e_wrt_e_rec_var :
forall e1 x1 n1,
  size_e (open_e_wrt_e_rec n1 (e_Var_f x1) e1) = size_e e1.
Proof.
pose proof size_e_open_e_wrt_e_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_e_open_e_wrt_e_rec_var : lngen.
#[export] Hint Rewrite size_e_open_e_wrt_e_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_DTy_open_DTy_wrt_DTy_var :
forall DTy1 dskA1,
  size_DTy (open_DTy_wrt_DTy DTy1 (DT_SkVar_f dskA1)) = size_DTy DTy1.
Proof.
unfold open_DTy_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve size_DTy_open_DTy_wrt_DTy_var : lngen.
#[export] Hint Rewrite size_DTy_open_DTy_wrt_DTy_var using solve [auto] : lngen.

Lemma size_DSch_open_DSch_wrt_DTy_var :
forall DSch1 dskA1,
  size_DSch (open_DSch_wrt_DTy DSch1 (DT_SkVar_f dskA1)) = size_DSch DSch1.
Proof.
unfold open_DSch_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve size_DSch_open_DSch_wrt_DTy_var : lngen.
#[export] Hint Rewrite size_DSch_open_DSch_wrt_DTy_var using solve [auto] : lngen.

Lemma size_Ty_open_Ty_wrt_Ty_var :
forall Ty1 skA1,
  size_Ty (open_Ty_wrt_Ty Ty1 (T_SkVar_f skA1)) = size_Ty Ty1.
Proof.
unfold open_Ty_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve size_Ty_open_Ty_wrt_Ty_var : lngen.
#[export] Hint Rewrite size_Ty_open_Ty_wrt_Ty_var using solve [auto] : lngen.

Lemma size_Sch_open_Sch_wrt_Ty_var :
forall Sch1 skA1,
  size_Sch (open_Sch_wrt_Ty Sch1 (T_SkVar_f skA1)) = size_Sch Sch1.
Proof.
unfold open_Sch_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve size_Sch_open_Sch_wrt_Ty_var : lngen.
#[export] Hint Rewrite size_Sch_open_Sch_wrt_Ty_var using solve [auto] : lngen.

Lemma size_e_open_e_wrt_e_var :
forall e1 x1,
  size_e (open_e_wrt_e e1 (e_Var_f x1)) = size_e e1.
Proof.
unfold open_e_wrt_e; default_simp.
Qed.

#[export] Hint Resolve size_e_open_e_wrt_e_var : lngen.
#[export] Hint Rewrite size_e_open_e_wrt_e_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_DTy_wrt_DTy_S_mutual :
(forall n1 DTy1,
  degree_DTy_wrt_DTy n1 DTy1 ->
  degree_DTy_wrt_DTy (S n1) DTy1).
Proof.
apply_mutual_ind degree_DTy_wrt_DTy_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_DTy_wrt_DTy_S :
forall n1 DTy1,
  degree_DTy_wrt_DTy n1 DTy1 ->
  degree_DTy_wrt_DTy (S n1) DTy1.
Proof.
pose proof degree_DTy_wrt_DTy_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_DTy_wrt_DTy_S : lngen.

(* begin hide *)

Lemma degree_DSch_wrt_DTy_S_mutual :
(forall n1 DSch1,
  degree_DSch_wrt_DTy n1 DSch1 ->
  degree_DSch_wrt_DTy (S n1) DSch1).
Proof.
apply_mutual_ind degree_DSch_wrt_DTy_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_DSch_wrt_DTy_S :
forall n1 DSch1,
  degree_DSch_wrt_DTy n1 DSch1 ->
  degree_DSch_wrt_DTy (S n1) DSch1.
Proof.
pose proof degree_DSch_wrt_DTy_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_DSch_wrt_DTy_S : lngen.

(* begin hide *)

Lemma degree_Ty_wrt_Ty_S_mutual :
(forall n1 Ty1,
  degree_Ty_wrt_Ty n1 Ty1 ->
  degree_Ty_wrt_Ty (S n1) Ty1).
Proof.
apply_mutual_ind degree_Ty_wrt_Ty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_Ty_wrt_Ty_S :
forall n1 Ty1,
  degree_Ty_wrt_Ty n1 Ty1 ->
  degree_Ty_wrt_Ty (S n1) Ty1.
Proof.
pose proof degree_Ty_wrt_Ty_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Ty_wrt_Ty_S : lngen.

(* begin hide *)

Lemma degree_Sch_wrt_Ty_S_mutual :
(forall n1 Sch1,
  degree_Sch_wrt_Ty n1 Sch1 ->
  degree_Sch_wrt_Ty (S n1) Sch1).
Proof.
apply_mutual_ind degree_Sch_wrt_Ty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_Sch_wrt_Ty_S :
forall n1 Sch1,
  degree_Sch_wrt_Ty n1 Sch1 ->
  degree_Sch_wrt_Ty (S n1) Sch1.
Proof.
pose proof degree_Sch_wrt_Ty_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Sch_wrt_Ty_S : lngen.

(* begin hide *)

Lemma degree_e_wrt_e_S_mutual :
(forall n1 e1,
  degree_e_wrt_e n1 e1 ->
  degree_e_wrt_e (S n1) e1).
Proof.
apply_mutual_ind degree_e_wrt_e_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_e_wrt_e_S :
forall n1 e1,
  degree_e_wrt_e n1 e1 ->
  degree_e_wrt_e (S n1) e1.
Proof.
pose proof degree_e_wrt_e_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_e_wrt_e_S : lngen.

Lemma degree_DTy_wrt_DTy_O :
forall n1 DTy1,
  degree_DTy_wrt_DTy O DTy1 ->
  degree_DTy_wrt_DTy n1 DTy1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_DTy_wrt_DTy_O : lngen.

Lemma degree_DSch_wrt_DTy_O :
forall n1 DSch1,
  degree_DSch_wrt_DTy O DSch1 ->
  degree_DSch_wrt_DTy n1 DSch1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_DSch_wrt_DTy_O : lngen.

Lemma degree_Ty_wrt_Ty_O :
forall n1 Ty1,
  degree_Ty_wrt_Ty O Ty1 ->
  degree_Ty_wrt_Ty n1 Ty1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_Ty_wrt_Ty_O : lngen.

Lemma degree_Sch_wrt_Ty_O :
forall n1 Sch1,
  degree_Sch_wrt_Ty O Sch1 ->
  degree_Sch_wrt_Ty n1 Sch1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_Sch_wrt_Ty_O : lngen.

Lemma degree_e_wrt_e_O :
forall n1 e1,
  degree_e_wrt_e O e1 ->
  degree_e_wrt_e n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_e_wrt_e_O : lngen.

(* begin hide *)

Lemma degree_DTy_wrt_DTy_close_DTy_wrt_DTy_rec_mutual :
(forall DTy1 dskA1 n1,
  degree_DTy_wrt_DTy n1 DTy1 ->
  degree_DTy_wrt_DTy (S n1) (close_DTy_wrt_DTy_rec n1 dskA1 DTy1)).
Proof.
apply_mutual_ind DTy_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_DTy_wrt_DTy_close_DTy_wrt_DTy_rec :
forall DTy1 dskA1 n1,
  degree_DTy_wrt_DTy n1 DTy1 ->
  degree_DTy_wrt_DTy (S n1) (close_DTy_wrt_DTy_rec n1 dskA1 DTy1).
Proof.
pose proof degree_DTy_wrt_DTy_close_DTy_wrt_DTy_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_DTy_wrt_DTy_close_DTy_wrt_DTy_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_DSch_wrt_DTy_close_DSch_wrt_DTy_rec_mutual :
(forall DSch1 dskA1 n1,
  degree_DSch_wrt_DTy n1 DSch1 ->
  degree_DSch_wrt_DTy (S n1) (close_DSch_wrt_DTy_rec n1 dskA1 DSch1)).
Proof.
apply_mutual_ind DSch_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_DSch_wrt_DTy_close_DSch_wrt_DTy_rec :
forall DSch1 dskA1 n1,
  degree_DSch_wrt_DTy n1 DSch1 ->
  degree_DSch_wrt_DTy (S n1) (close_DSch_wrt_DTy_rec n1 dskA1 DSch1).
Proof.
pose proof degree_DSch_wrt_DTy_close_DSch_wrt_DTy_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_DSch_wrt_DTy_close_DSch_wrt_DTy_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Ty_wrt_Ty_close_Ty_wrt_Ty_rec_mutual :
(forall Ty1 skA1 n1,
  degree_Ty_wrt_Ty n1 Ty1 ->
  degree_Ty_wrt_Ty (S n1) (close_Ty_wrt_Ty_rec n1 skA1 Ty1)).
Proof.
apply_mutual_ind Ty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Ty_wrt_Ty_close_Ty_wrt_Ty_rec :
forall Ty1 skA1 n1,
  degree_Ty_wrt_Ty n1 Ty1 ->
  degree_Ty_wrt_Ty (S n1) (close_Ty_wrt_Ty_rec n1 skA1 Ty1).
Proof.
pose proof degree_Ty_wrt_Ty_close_Ty_wrt_Ty_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Ty_wrt_Ty_close_Ty_wrt_Ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Sch_wrt_Ty_close_Sch_wrt_Ty_rec_mutual :
(forall Sch1 skA1 n1,
  degree_Sch_wrt_Ty n1 Sch1 ->
  degree_Sch_wrt_Ty (S n1) (close_Sch_wrt_Ty_rec n1 skA1 Sch1)).
Proof.
apply_mutual_ind Sch_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Sch_wrt_Ty_close_Sch_wrt_Ty_rec :
forall Sch1 skA1 n1,
  degree_Sch_wrt_Ty n1 Sch1 ->
  degree_Sch_wrt_Ty (S n1) (close_Sch_wrt_Ty_rec n1 skA1 Sch1).
Proof.
pose proof degree_Sch_wrt_Ty_close_Sch_wrt_Ty_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Sch_wrt_Ty_close_Sch_wrt_Ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_e_close_e_wrt_e_rec_mutual :
(forall e1 x1 n1,
  degree_e_wrt_e n1 e1 ->
  degree_e_wrt_e (S n1) (close_e_wrt_e_rec n1 x1 e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_e_close_e_wrt_e_rec :
forall e1 x1 n1,
  degree_e_wrt_e n1 e1 ->
  degree_e_wrt_e (S n1) (close_e_wrt_e_rec n1 x1 e1).
Proof.
pose proof degree_e_wrt_e_close_e_wrt_e_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_e_wrt_e_close_e_wrt_e_rec : lngen.

(* end hide *)

Lemma degree_DTy_wrt_DTy_close_DTy_wrt_DTy :
forall DTy1 dskA1,
  degree_DTy_wrt_DTy 0 DTy1 ->
  degree_DTy_wrt_DTy 1 (close_DTy_wrt_DTy dskA1 DTy1).
Proof.
unfold close_DTy_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve degree_DTy_wrt_DTy_close_DTy_wrt_DTy : lngen.

Lemma degree_DSch_wrt_DTy_close_DSch_wrt_DTy :
forall DSch1 dskA1,
  degree_DSch_wrt_DTy 0 DSch1 ->
  degree_DSch_wrt_DTy 1 (close_DSch_wrt_DTy dskA1 DSch1).
Proof.
unfold close_DSch_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve degree_DSch_wrt_DTy_close_DSch_wrt_DTy : lngen.

Lemma degree_Ty_wrt_Ty_close_Ty_wrt_Ty :
forall Ty1 skA1,
  degree_Ty_wrt_Ty 0 Ty1 ->
  degree_Ty_wrt_Ty 1 (close_Ty_wrt_Ty skA1 Ty1).
Proof.
unfold close_Ty_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve degree_Ty_wrt_Ty_close_Ty_wrt_Ty : lngen.

Lemma degree_Sch_wrt_Ty_close_Sch_wrt_Ty :
forall Sch1 skA1,
  degree_Sch_wrt_Ty 0 Sch1 ->
  degree_Sch_wrt_Ty 1 (close_Sch_wrt_Ty skA1 Sch1).
Proof.
unfold close_Sch_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve degree_Sch_wrt_Ty_close_Sch_wrt_Ty : lngen.

Lemma degree_e_wrt_e_close_e_wrt_e :
forall e1 x1,
  degree_e_wrt_e 0 e1 ->
  degree_e_wrt_e 1 (close_e_wrt_e x1 e1).
Proof.
unfold close_e_wrt_e; default_simp.
Qed.

#[export] Hint Resolve degree_e_wrt_e_close_e_wrt_e : lngen.

(* begin hide *)

Lemma degree_DTy_wrt_DTy_close_DTy_wrt_DTy_rec_inv_mutual :
(forall DTy1 dskA1 n1,
  degree_DTy_wrt_DTy (S n1) (close_DTy_wrt_DTy_rec n1 dskA1 DTy1) ->
  degree_DTy_wrt_DTy n1 DTy1).
Proof.
apply_mutual_ind DTy_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_DTy_wrt_DTy_close_DTy_wrt_DTy_rec_inv :
forall DTy1 dskA1 n1,
  degree_DTy_wrt_DTy (S n1) (close_DTy_wrt_DTy_rec n1 dskA1 DTy1) ->
  degree_DTy_wrt_DTy n1 DTy1.
Proof.
pose proof degree_DTy_wrt_DTy_close_DTy_wrt_DTy_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_DTy_wrt_DTy_close_DTy_wrt_DTy_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_DSch_wrt_DTy_close_DSch_wrt_DTy_rec_inv_mutual :
(forall DSch1 dskA1 n1,
  degree_DSch_wrt_DTy (S n1) (close_DSch_wrt_DTy_rec n1 dskA1 DSch1) ->
  degree_DSch_wrt_DTy n1 DSch1).
Proof.
apply_mutual_ind DSch_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_DSch_wrt_DTy_close_DSch_wrt_DTy_rec_inv :
forall DSch1 dskA1 n1,
  degree_DSch_wrt_DTy (S n1) (close_DSch_wrt_DTy_rec n1 dskA1 DSch1) ->
  degree_DSch_wrt_DTy n1 DSch1.
Proof.
pose proof degree_DSch_wrt_DTy_close_DSch_wrt_DTy_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_DSch_wrt_DTy_close_DSch_wrt_DTy_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Ty_wrt_Ty_close_Ty_wrt_Ty_rec_inv_mutual :
(forall Ty1 skA1 n1,
  degree_Ty_wrt_Ty (S n1) (close_Ty_wrt_Ty_rec n1 skA1 Ty1) ->
  degree_Ty_wrt_Ty n1 Ty1).
Proof.
apply_mutual_ind Ty_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Ty_wrt_Ty_close_Ty_wrt_Ty_rec_inv :
forall Ty1 skA1 n1,
  degree_Ty_wrt_Ty (S n1) (close_Ty_wrt_Ty_rec n1 skA1 Ty1) ->
  degree_Ty_wrt_Ty n1 Ty1.
Proof.
pose proof degree_Ty_wrt_Ty_close_Ty_wrt_Ty_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_Ty_wrt_Ty_close_Ty_wrt_Ty_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Sch_wrt_Ty_close_Sch_wrt_Ty_rec_inv_mutual :
(forall Sch1 skA1 n1,
  degree_Sch_wrt_Ty (S n1) (close_Sch_wrt_Ty_rec n1 skA1 Sch1) ->
  degree_Sch_wrt_Ty n1 Sch1).
Proof.
apply_mutual_ind Sch_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Sch_wrt_Ty_close_Sch_wrt_Ty_rec_inv :
forall Sch1 skA1 n1,
  degree_Sch_wrt_Ty (S n1) (close_Sch_wrt_Ty_rec n1 skA1 Sch1) ->
  degree_Sch_wrt_Ty n1 Sch1.
Proof.
pose proof degree_Sch_wrt_Ty_close_Sch_wrt_Ty_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_Sch_wrt_Ty_close_Sch_wrt_Ty_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_e_close_e_wrt_e_rec_inv_mutual :
(forall e1 x1 n1,
  degree_e_wrt_e (S n1) (close_e_wrt_e_rec n1 x1 e1) ->
  degree_e_wrt_e n1 e1).
Proof.
apply_mutual_ind e_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_e_close_e_wrt_e_rec_inv :
forall e1 x1 n1,
  degree_e_wrt_e (S n1) (close_e_wrt_e_rec n1 x1 e1) ->
  degree_e_wrt_e n1 e1.
Proof.
pose proof degree_e_wrt_e_close_e_wrt_e_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_e_wrt_e_close_e_wrt_e_rec_inv : lngen.

(* end hide *)

Lemma degree_DTy_wrt_DTy_close_DTy_wrt_DTy_inv :
forall DTy1 dskA1,
  degree_DTy_wrt_DTy 1 (close_DTy_wrt_DTy dskA1 DTy1) ->
  degree_DTy_wrt_DTy 0 DTy1.
Proof.
unfold close_DTy_wrt_DTy; eauto with lngen.
Qed.

#[export] Hint Immediate degree_DTy_wrt_DTy_close_DTy_wrt_DTy_inv : lngen.

Lemma degree_DSch_wrt_DTy_close_DSch_wrt_DTy_inv :
forall DSch1 dskA1,
  degree_DSch_wrt_DTy 1 (close_DSch_wrt_DTy dskA1 DSch1) ->
  degree_DSch_wrt_DTy 0 DSch1.
Proof.
unfold close_DSch_wrt_DTy; eauto with lngen.
Qed.

#[export] Hint Immediate degree_DSch_wrt_DTy_close_DSch_wrt_DTy_inv : lngen.

Lemma degree_Ty_wrt_Ty_close_Ty_wrt_Ty_inv :
forall Ty1 skA1,
  degree_Ty_wrt_Ty 1 (close_Ty_wrt_Ty skA1 Ty1) ->
  degree_Ty_wrt_Ty 0 Ty1.
Proof.
unfold close_Ty_wrt_Ty; eauto with lngen.
Qed.

#[export] Hint Immediate degree_Ty_wrt_Ty_close_Ty_wrt_Ty_inv : lngen.

Lemma degree_Sch_wrt_Ty_close_Sch_wrt_Ty_inv :
forall Sch1 skA1,
  degree_Sch_wrt_Ty 1 (close_Sch_wrt_Ty skA1 Sch1) ->
  degree_Sch_wrt_Ty 0 Sch1.
Proof.
unfold close_Sch_wrt_Ty; eauto with lngen.
Qed.

#[export] Hint Immediate degree_Sch_wrt_Ty_close_Sch_wrt_Ty_inv : lngen.

Lemma degree_e_wrt_e_close_e_wrt_e_inv :
forall e1 x1,
  degree_e_wrt_e 1 (close_e_wrt_e x1 e1) ->
  degree_e_wrt_e 0 e1.
Proof.
unfold close_e_wrt_e; eauto with lngen.
Qed.

#[export] Hint Immediate degree_e_wrt_e_close_e_wrt_e_inv : lngen.

(* begin hide *)

Lemma degree_DTy_wrt_DTy_open_DTy_wrt_DTy_rec_mutual :
(forall DTy1 DTy2 n1,
  degree_DTy_wrt_DTy (S n1) DTy1 ->
  degree_DTy_wrt_DTy n1 DTy2 ->
  degree_DTy_wrt_DTy n1 (open_DTy_wrt_DTy_rec n1 DTy2 DTy1)).
Proof.
apply_mutual_ind DTy_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_DTy_wrt_DTy_open_DTy_wrt_DTy_rec :
forall DTy1 DTy2 n1,
  degree_DTy_wrt_DTy (S n1) DTy1 ->
  degree_DTy_wrt_DTy n1 DTy2 ->
  degree_DTy_wrt_DTy n1 (open_DTy_wrt_DTy_rec n1 DTy2 DTy1).
Proof.
pose proof degree_DTy_wrt_DTy_open_DTy_wrt_DTy_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_DTy_wrt_DTy_open_DTy_wrt_DTy_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_DSch_wrt_DTy_open_DSch_wrt_DTy_rec_mutual :
(forall DSch1 DTy1 n1,
  degree_DSch_wrt_DTy (S n1) DSch1 ->
  degree_DTy_wrt_DTy n1 DTy1 ->
  degree_DSch_wrt_DTy n1 (open_DSch_wrt_DTy_rec n1 DTy1 DSch1)).
Proof.
apply_mutual_ind DSch_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_DSch_wrt_DTy_open_DSch_wrt_DTy_rec :
forall DSch1 DTy1 n1,
  degree_DSch_wrt_DTy (S n1) DSch1 ->
  degree_DTy_wrt_DTy n1 DTy1 ->
  degree_DSch_wrt_DTy n1 (open_DSch_wrt_DTy_rec n1 DTy1 DSch1).
Proof.
pose proof degree_DSch_wrt_DTy_open_DSch_wrt_DTy_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_DSch_wrt_DTy_open_DSch_wrt_DTy_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Ty_wrt_Ty_open_Ty_wrt_Ty_rec_mutual :
(forall Ty1 Ty2 n1,
  degree_Ty_wrt_Ty (S n1) Ty1 ->
  degree_Ty_wrt_Ty n1 Ty2 ->
  degree_Ty_wrt_Ty n1 (open_Ty_wrt_Ty_rec n1 Ty2 Ty1)).
Proof.
apply_mutual_ind Ty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Ty_wrt_Ty_open_Ty_wrt_Ty_rec :
forall Ty1 Ty2 n1,
  degree_Ty_wrt_Ty (S n1) Ty1 ->
  degree_Ty_wrt_Ty n1 Ty2 ->
  degree_Ty_wrt_Ty n1 (open_Ty_wrt_Ty_rec n1 Ty2 Ty1).
Proof.
pose proof degree_Ty_wrt_Ty_open_Ty_wrt_Ty_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Ty_wrt_Ty_open_Ty_wrt_Ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Sch_wrt_Ty_open_Sch_wrt_Ty_rec_mutual :
(forall Sch1 Ty1 n1,
  degree_Sch_wrt_Ty (S n1) Sch1 ->
  degree_Ty_wrt_Ty n1 Ty1 ->
  degree_Sch_wrt_Ty n1 (open_Sch_wrt_Ty_rec n1 Ty1 Sch1)).
Proof.
apply_mutual_ind Sch_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Sch_wrt_Ty_open_Sch_wrt_Ty_rec :
forall Sch1 Ty1 n1,
  degree_Sch_wrt_Ty (S n1) Sch1 ->
  degree_Ty_wrt_Ty n1 Ty1 ->
  degree_Sch_wrt_Ty n1 (open_Sch_wrt_Ty_rec n1 Ty1 Sch1).
Proof.
pose proof degree_Sch_wrt_Ty_open_Sch_wrt_Ty_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Sch_wrt_Ty_open_Sch_wrt_Ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_e_open_e_wrt_e_rec_mutual :
(forall e1 e2 n1,
  degree_e_wrt_e (S n1) e1 ->
  degree_e_wrt_e n1 e2 ->
  degree_e_wrt_e n1 (open_e_wrt_e_rec n1 e2 e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_e_open_e_wrt_e_rec :
forall e1 e2 n1,
  degree_e_wrt_e (S n1) e1 ->
  degree_e_wrt_e n1 e2 ->
  degree_e_wrt_e n1 (open_e_wrt_e_rec n1 e2 e1).
Proof.
pose proof degree_e_wrt_e_open_e_wrt_e_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_e_wrt_e_open_e_wrt_e_rec : lngen.

(* end hide *)

Lemma degree_DTy_wrt_DTy_open_DTy_wrt_DTy :
forall DTy1 DTy2,
  degree_DTy_wrt_DTy 1 DTy1 ->
  degree_DTy_wrt_DTy 0 DTy2 ->
  degree_DTy_wrt_DTy 0 (open_DTy_wrt_DTy DTy1 DTy2).
Proof.
unfold open_DTy_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve degree_DTy_wrt_DTy_open_DTy_wrt_DTy : lngen.

Lemma degree_DSch_wrt_DTy_open_DSch_wrt_DTy :
forall DSch1 DTy1,
  degree_DSch_wrt_DTy 1 DSch1 ->
  degree_DTy_wrt_DTy 0 DTy1 ->
  degree_DSch_wrt_DTy 0 (open_DSch_wrt_DTy DSch1 DTy1).
Proof.
unfold open_DSch_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve degree_DSch_wrt_DTy_open_DSch_wrt_DTy : lngen.

Lemma degree_Ty_wrt_Ty_open_Ty_wrt_Ty :
forall Ty1 Ty2,
  degree_Ty_wrt_Ty 1 Ty1 ->
  degree_Ty_wrt_Ty 0 Ty2 ->
  degree_Ty_wrt_Ty 0 (open_Ty_wrt_Ty Ty1 Ty2).
Proof.
unfold open_Ty_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve degree_Ty_wrt_Ty_open_Ty_wrt_Ty : lngen.

Lemma degree_Sch_wrt_Ty_open_Sch_wrt_Ty :
forall Sch1 Ty1,
  degree_Sch_wrt_Ty 1 Sch1 ->
  degree_Ty_wrt_Ty 0 Ty1 ->
  degree_Sch_wrt_Ty 0 (open_Sch_wrt_Ty Sch1 Ty1).
Proof.
unfold open_Sch_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve degree_Sch_wrt_Ty_open_Sch_wrt_Ty : lngen.

Lemma degree_e_wrt_e_open_e_wrt_e :
forall e1 e2,
  degree_e_wrt_e 1 e1 ->
  degree_e_wrt_e 0 e2 ->
  degree_e_wrt_e 0 (open_e_wrt_e e1 e2).
Proof.
unfold open_e_wrt_e; default_simp.
Qed.

#[export] Hint Resolve degree_e_wrt_e_open_e_wrt_e : lngen.

(* begin hide *)

Lemma degree_DTy_wrt_DTy_open_DTy_wrt_DTy_rec_inv_mutual :
(forall DTy1 DTy2 n1,
  degree_DTy_wrt_DTy n1 (open_DTy_wrt_DTy_rec n1 DTy2 DTy1) ->
  degree_DTy_wrt_DTy (S n1) DTy1).
Proof.
apply_mutual_ind DTy_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_DTy_wrt_DTy_open_DTy_wrt_DTy_rec_inv :
forall DTy1 DTy2 n1,
  degree_DTy_wrt_DTy n1 (open_DTy_wrt_DTy_rec n1 DTy2 DTy1) ->
  degree_DTy_wrt_DTy (S n1) DTy1.
Proof.
pose proof degree_DTy_wrt_DTy_open_DTy_wrt_DTy_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_DTy_wrt_DTy_open_DTy_wrt_DTy_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_DSch_wrt_DTy_open_DSch_wrt_DTy_rec_inv_mutual :
(forall DSch1 DTy1 n1,
  degree_DSch_wrt_DTy n1 (open_DSch_wrt_DTy_rec n1 DTy1 DSch1) ->
  degree_DSch_wrt_DTy (S n1) DSch1).
Proof.
apply_mutual_ind DSch_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_DSch_wrt_DTy_open_DSch_wrt_DTy_rec_inv :
forall DSch1 DTy1 n1,
  degree_DSch_wrt_DTy n1 (open_DSch_wrt_DTy_rec n1 DTy1 DSch1) ->
  degree_DSch_wrt_DTy (S n1) DSch1.
Proof.
pose proof degree_DSch_wrt_DTy_open_DSch_wrt_DTy_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_DSch_wrt_DTy_open_DSch_wrt_DTy_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Ty_wrt_Ty_open_Ty_wrt_Ty_rec_inv_mutual :
(forall Ty1 Ty2 n1,
  degree_Ty_wrt_Ty n1 (open_Ty_wrt_Ty_rec n1 Ty2 Ty1) ->
  degree_Ty_wrt_Ty (S n1) Ty1).
Proof.
apply_mutual_ind Ty_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Ty_wrt_Ty_open_Ty_wrt_Ty_rec_inv :
forall Ty1 Ty2 n1,
  degree_Ty_wrt_Ty n1 (open_Ty_wrt_Ty_rec n1 Ty2 Ty1) ->
  degree_Ty_wrt_Ty (S n1) Ty1.
Proof.
pose proof degree_Ty_wrt_Ty_open_Ty_wrt_Ty_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_Ty_wrt_Ty_open_Ty_wrt_Ty_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Sch_wrt_Ty_open_Sch_wrt_Ty_rec_inv_mutual :
(forall Sch1 Ty1 n1,
  degree_Sch_wrt_Ty n1 (open_Sch_wrt_Ty_rec n1 Ty1 Sch1) ->
  degree_Sch_wrt_Ty (S n1) Sch1).
Proof.
apply_mutual_ind Sch_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Sch_wrt_Ty_open_Sch_wrt_Ty_rec_inv :
forall Sch1 Ty1 n1,
  degree_Sch_wrt_Ty n1 (open_Sch_wrt_Ty_rec n1 Ty1 Sch1) ->
  degree_Sch_wrt_Ty (S n1) Sch1.
Proof.
pose proof degree_Sch_wrt_Ty_open_Sch_wrt_Ty_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_Sch_wrt_Ty_open_Sch_wrt_Ty_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_e_open_e_wrt_e_rec_inv_mutual :
(forall e1 e2 n1,
  degree_e_wrt_e n1 (open_e_wrt_e_rec n1 e2 e1) ->
  degree_e_wrt_e (S n1) e1).
Proof.
apply_mutual_ind e_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_e_open_e_wrt_e_rec_inv :
forall e1 e2 n1,
  degree_e_wrt_e n1 (open_e_wrt_e_rec n1 e2 e1) ->
  degree_e_wrt_e (S n1) e1.
Proof.
pose proof degree_e_wrt_e_open_e_wrt_e_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_e_wrt_e_open_e_wrt_e_rec_inv : lngen.

(* end hide *)

Lemma degree_DTy_wrt_DTy_open_DTy_wrt_DTy_inv :
forall DTy1 DTy2,
  degree_DTy_wrt_DTy 0 (open_DTy_wrt_DTy DTy1 DTy2) ->
  degree_DTy_wrt_DTy 1 DTy1.
Proof.
unfold open_DTy_wrt_DTy; eauto with lngen.
Qed.

#[export] Hint Immediate degree_DTy_wrt_DTy_open_DTy_wrt_DTy_inv : lngen.

Lemma degree_DSch_wrt_DTy_open_DSch_wrt_DTy_inv :
forall DSch1 DTy1,
  degree_DSch_wrt_DTy 0 (open_DSch_wrt_DTy DSch1 DTy1) ->
  degree_DSch_wrt_DTy 1 DSch1.
Proof.
unfold open_DSch_wrt_DTy; eauto with lngen.
Qed.

#[export] Hint Immediate degree_DSch_wrt_DTy_open_DSch_wrt_DTy_inv : lngen.

Lemma degree_Ty_wrt_Ty_open_Ty_wrt_Ty_inv :
forall Ty1 Ty2,
  degree_Ty_wrt_Ty 0 (open_Ty_wrt_Ty Ty1 Ty2) ->
  degree_Ty_wrt_Ty 1 Ty1.
Proof.
unfold open_Ty_wrt_Ty; eauto with lngen.
Qed.

#[export] Hint Immediate degree_Ty_wrt_Ty_open_Ty_wrt_Ty_inv : lngen.

Lemma degree_Sch_wrt_Ty_open_Sch_wrt_Ty_inv :
forall Sch1 Ty1,
  degree_Sch_wrt_Ty 0 (open_Sch_wrt_Ty Sch1 Ty1) ->
  degree_Sch_wrt_Ty 1 Sch1.
Proof.
unfold open_Sch_wrt_Ty; eauto with lngen.
Qed.

#[export] Hint Immediate degree_Sch_wrt_Ty_open_Sch_wrt_Ty_inv : lngen.

Lemma degree_e_wrt_e_open_e_wrt_e_inv :
forall e1 e2,
  degree_e_wrt_e 0 (open_e_wrt_e e1 e2) ->
  degree_e_wrt_e 1 e1.
Proof.
unfold open_e_wrt_e; eauto with lngen.
Qed.

#[export] Hint Immediate degree_e_wrt_e_open_e_wrt_e_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_DTy_wrt_DTy_rec_inj_mutual :
(forall DTy1 DTy2 dskA1 n1,
  close_DTy_wrt_DTy_rec n1 dskA1 DTy1 = close_DTy_wrt_DTy_rec n1 dskA1 DTy2 ->
  DTy1 = DTy2).
Proof.
apply_mutual_ind DTy_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_DTy_wrt_DTy_rec_inj :
forall DTy1 DTy2 dskA1 n1,
  close_DTy_wrt_DTy_rec n1 dskA1 DTy1 = close_DTy_wrt_DTy_rec n1 dskA1 DTy2 ->
  DTy1 = DTy2.
Proof.
pose proof close_DTy_wrt_DTy_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_DTy_wrt_DTy_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_DSch_wrt_DTy_rec_inj_mutual :
(forall DSch1 DSch2 dskA1 n1,
  close_DSch_wrt_DTy_rec n1 dskA1 DSch1 = close_DSch_wrt_DTy_rec n1 dskA1 DSch2 ->
  DSch1 = DSch2).
Proof.
apply_mutual_ind DSch_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_DSch_wrt_DTy_rec_inj :
forall DSch1 DSch2 dskA1 n1,
  close_DSch_wrt_DTy_rec n1 dskA1 DSch1 = close_DSch_wrt_DTy_rec n1 dskA1 DSch2 ->
  DSch1 = DSch2.
Proof.
pose proof close_DSch_wrt_DTy_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_DSch_wrt_DTy_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Ty_wrt_Ty_rec_inj_mutual :
(forall Ty1 Ty2 skA1 n1,
  close_Ty_wrt_Ty_rec n1 skA1 Ty1 = close_Ty_wrt_Ty_rec n1 skA1 Ty2 ->
  Ty1 = Ty2).
Proof.
apply_mutual_ind Ty_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Ty_wrt_Ty_rec_inj :
forall Ty1 Ty2 skA1 n1,
  close_Ty_wrt_Ty_rec n1 skA1 Ty1 = close_Ty_wrt_Ty_rec n1 skA1 Ty2 ->
  Ty1 = Ty2.
Proof.
pose proof close_Ty_wrt_Ty_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_Ty_wrt_Ty_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Sch_wrt_Ty_rec_inj_mutual :
(forall Sch1 Sch2 skA1 n1,
  close_Sch_wrt_Ty_rec n1 skA1 Sch1 = close_Sch_wrt_Ty_rec n1 skA1 Sch2 ->
  Sch1 = Sch2).
Proof.
apply_mutual_ind Sch_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Sch_wrt_Ty_rec_inj :
forall Sch1 Sch2 skA1 n1,
  close_Sch_wrt_Ty_rec n1 skA1 Sch1 = close_Sch_wrt_Ty_rec n1 skA1 Sch2 ->
  Sch1 = Sch2.
Proof.
pose proof close_Sch_wrt_Ty_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_Sch_wrt_Ty_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_e_wrt_e_rec_inj_mutual :
(forall e1 e2 x1 n1,
  close_e_wrt_e_rec n1 x1 e1 = close_e_wrt_e_rec n1 x1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind e_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_e_wrt_e_rec_inj :
forall e1 e2 x1 n1,
  close_e_wrt_e_rec n1 x1 e1 = close_e_wrt_e_rec n1 x1 e2 ->
  e1 = e2.
Proof.
pose proof close_e_wrt_e_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_e_wrt_e_rec_inj : lngen.

(* end hide *)

Lemma close_DTy_wrt_DTy_inj :
forall DTy1 DTy2 dskA1,
  close_DTy_wrt_DTy dskA1 DTy1 = close_DTy_wrt_DTy dskA1 DTy2 ->
  DTy1 = DTy2.
Proof.
unfold close_DTy_wrt_DTy; eauto with lngen.
Qed.

#[export] Hint Immediate close_DTy_wrt_DTy_inj : lngen.

Lemma close_DSch_wrt_DTy_inj :
forall DSch1 DSch2 dskA1,
  close_DSch_wrt_DTy dskA1 DSch1 = close_DSch_wrt_DTy dskA1 DSch2 ->
  DSch1 = DSch2.
Proof.
unfold close_DSch_wrt_DTy; eauto with lngen.
Qed.

#[export] Hint Immediate close_DSch_wrt_DTy_inj : lngen.

Lemma close_Ty_wrt_Ty_inj :
forall Ty1 Ty2 skA1,
  close_Ty_wrt_Ty skA1 Ty1 = close_Ty_wrt_Ty skA1 Ty2 ->
  Ty1 = Ty2.
Proof.
unfold close_Ty_wrt_Ty; eauto with lngen.
Qed.

#[export] Hint Immediate close_Ty_wrt_Ty_inj : lngen.

Lemma close_Sch_wrt_Ty_inj :
forall Sch1 Sch2 skA1,
  close_Sch_wrt_Ty skA1 Sch1 = close_Sch_wrt_Ty skA1 Sch2 ->
  Sch1 = Sch2.
Proof.
unfold close_Sch_wrt_Ty; eauto with lngen.
Qed.

#[export] Hint Immediate close_Sch_wrt_Ty_inj : lngen.

Lemma close_e_wrt_e_inj :
forall e1 e2 x1,
  close_e_wrt_e x1 e1 = close_e_wrt_e x1 e2 ->
  e1 = e2.
Proof.
unfold close_e_wrt_e; eauto with lngen.
Qed.

#[export] Hint Immediate close_e_wrt_e_inj : lngen.

(* begin hide *)

Lemma close_DTy_wrt_DTy_rec_open_DTy_wrt_DTy_rec_mutual :
(forall DTy1 dskA1 n1,
  dskA1 `notin` free_dskvars_DTy DTy1 ->
  close_DTy_wrt_DTy_rec n1 dskA1 (open_DTy_wrt_DTy_rec n1 (DT_SkVar_f dskA1) DTy1) = DTy1).
Proof.
apply_mutual_ind DTy_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_DTy_wrt_DTy_rec_open_DTy_wrt_DTy_rec :
forall DTy1 dskA1 n1,
  dskA1 `notin` free_dskvars_DTy DTy1 ->
  close_DTy_wrt_DTy_rec n1 dskA1 (open_DTy_wrt_DTy_rec n1 (DT_SkVar_f dskA1) DTy1) = DTy1.
Proof.
pose proof close_DTy_wrt_DTy_rec_open_DTy_wrt_DTy_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_DTy_wrt_DTy_rec_open_DTy_wrt_DTy_rec : lngen.
#[export] Hint Rewrite close_DTy_wrt_DTy_rec_open_DTy_wrt_DTy_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_DSch_wrt_DTy_rec_open_DSch_wrt_DTy_rec_mutual :
(forall DSch1 dskA1 n1,
  dskA1 `notin` free_dskvars_DSch DSch1 ->
  close_DSch_wrt_DTy_rec n1 dskA1 (open_DSch_wrt_DTy_rec n1 (DT_SkVar_f dskA1) DSch1) = DSch1).
Proof.
apply_mutual_ind DSch_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_DSch_wrt_DTy_rec_open_DSch_wrt_DTy_rec :
forall DSch1 dskA1 n1,
  dskA1 `notin` free_dskvars_DSch DSch1 ->
  close_DSch_wrt_DTy_rec n1 dskA1 (open_DSch_wrt_DTy_rec n1 (DT_SkVar_f dskA1) DSch1) = DSch1.
Proof.
pose proof close_DSch_wrt_DTy_rec_open_DSch_wrt_DTy_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_DSch_wrt_DTy_rec_open_DSch_wrt_DTy_rec : lngen.
#[export] Hint Rewrite close_DSch_wrt_DTy_rec_open_DSch_wrt_DTy_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Ty_wrt_Ty_rec_open_Ty_wrt_Ty_rec_mutual :
(forall Ty1 skA1 n1,
  skA1 `notin` free_skvars_Ty Ty1 ->
  close_Ty_wrt_Ty_rec n1 skA1 (open_Ty_wrt_Ty_rec n1 (T_SkVar_f skA1) Ty1) = Ty1).
Proof.
apply_mutual_ind Ty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Ty_wrt_Ty_rec_open_Ty_wrt_Ty_rec :
forall Ty1 skA1 n1,
  skA1 `notin` free_skvars_Ty Ty1 ->
  close_Ty_wrt_Ty_rec n1 skA1 (open_Ty_wrt_Ty_rec n1 (T_SkVar_f skA1) Ty1) = Ty1.
Proof.
pose proof close_Ty_wrt_Ty_rec_open_Ty_wrt_Ty_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_Ty_wrt_Ty_rec_open_Ty_wrt_Ty_rec : lngen.
#[export] Hint Rewrite close_Ty_wrt_Ty_rec_open_Ty_wrt_Ty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Sch_wrt_Ty_rec_open_Sch_wrt_Ty_rec_mutual :
(forall Sch1 skA1 n1,
  skA1 `notin` free_skvars_Sch Sch1 ->
  close_Sch_wrt_Ty_rec n1 skA1 (open_Sch_wrt_Ty_rec n1 (T_SkVar_f skA1) Sch1) = Sch1).
Proof.
apply_mutual_ind Sch_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Sch_wrt_Ty_rec_open_Sch_wrt_Ty_rec :
forall Sch1 skA1 n1,
  skA1 `notin` free_skvars_Sch Sch1 ->
  close_Sch_wrt_Ty_rec n1 skA1 (open_Sch_wrt_Ty_rec n1 (T_SkVar_f skA1) Sch1) = Sch1.
Proof.
pose proof close_Sch_wrt_Ty_rec_open_Sch_wrt_Ty_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_Sch_wrt_Ty_rec_open_Sch_wrt_Ty_rec : lngen.
#[export] Hint Rewrite close_Sch_wrt_Ty_rec_open_Sch_wrt_Ty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_e_wrt_e_rec_open_e_wrt_e_rec_mutual :
(forall e1 x1 n1,
  x1 `notin` free_xs_e e1 ->
  close_e_wrt_e_rec n1 x1 (open_e_wrt_e_rec n1 (e_Var_f x1) e1) = e1).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_e_wrt_e_rec_open_e_wrt_e_rec :
forall e1 x1 n1,
  x1 `notin` free_xs_e e1 ->
  close_e_wrt_e_rec n1 x1 (open_e_wrt_e_rec n1 (e_Var_f x1) e1) = e1.
Proof.
pose proof close_e_wrt_e_rec_open_e_wrt_e_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_e_wrt_e_rec_open_e_wrt_e_rec : lngen.
#[export] Hint Rewrite close_e_wrt_e_rec_open_e_wrt_e_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_DTy_wrt_DTy_open_DTy_wrt_DTy :
forall DTy1 dskA1,
  dskA1 `notin` free_dskvars_DTy DTy1 ->
  close_DTy_wrt_DTy dskA1 (open_DTy_wrt_DTy DTy1 (DT_SkVar_f dskA1)) = DTy1.
Proof.
unfold close_DTy_wrt_DTy; unfold open_DTy_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve close_DTy_wrt_DTy_open_DTy_wrt_DTy : lngen.
#[export] Hint Rewrite close_DTy_wrt_DTy_open_DTy_wrt_DTy using solve [auto] : lngen.

Lemma close_DSch_wrt_DTy_open_DSch_wrt_DTy :
forall DSch1 dskA1,
  dskA1 `notin` free_dskvars_DSch DSch1 ->
  close_DSch_wrt_DTy dskA1 (open_DSch_wrt_DTy DSch1 (DT_SkVar_f dskA1)) = DSch1.
Proof.
unfold close_DSch_wrt_DTy; unfold open_DSch_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve close_DSch_wrt_DTy_open_DSch_wrt_DTy : lngen.
#[export] Hint Rewrite close_DSch_wrt_DTy_open_DSch_wrt_DTy using solve [auto] : lngen.

Lemma close_Ty_wrt_Ty_open_Ty_wrt_Ty :
forall Ty1 skA1,
  skA1 `notin` free_skvars_Ty Ty1 ->
  close_Ty_wrt_Ty skA1 (open_Ty_wrt_Ty Ty1 (T_SkVar_f skA1)) = Ty1.
Proof.
unfold close_Ty_wrt_Ty; unfold open_Ty_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve close_Ty_wrt_Ty_open_Ty_wrt_Ty : lngen.
#[export] Hint Rewrite close_Ty_wrt_Ty_open_Ty_wrt_Ty using solve [auto] : lngen.

Lemma close_Sch_wrt_Ty_open_Sch_wrt_Ty :
forall Sch1 skA1,
  skA1 `notin` free_skvars_Sch Sch1 ->
  close_Sch_wrt_Ty skA1 (open_Sch_wrt_Ty Sch1 (T_SkVar_f skA1)) = Sch1.
Proof.
unfold close_Sch_wrt_Ty; unfold open_Sch_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve close_Sch_wrt_Ty_open_Sch_wrt_Ty : lngen.
#[export] Hint Rewrite close_Sch_wrt_Ty_open_Sch_wrt_Ty using solve [auto] : lngen.

Lemma close_e_wrt_e_open_e_wrt_e :
forall e1 x1,
  x1 `notin` free_xs_e e1 ->
  close_e_wrt_e x1 (open_e_wrt_e e1 (e_Var_f x1)) = e1.
Proof.
unfold close_e_wrt_e; unfold open_e_wrt_e; default_simp.
Qed.

#[export] Hint Resolve close_e_wrt_e_open_e_wrt_e : lngen.
#[export] Hint Rewrite close_e_wrt_e_open_e_wrt_e using solve [auto] : lngen.

(* begin hide *)

Lemma open_DTy_wrt_DTy_rec_close_DTy_wrt_DTy_rec_mutual :
(forall DTy1 dskA1 n1,
  open_DTy_wrt_DTy_rec n1 (DT_SkVar_f dskA1) (close_DTy_wrt_DTy_rec n1 dskA1 DTy1) = DTy1).
Proof.
apply_mutual_ind DTy_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_DTy_wrt_DTy_rec_close_DTy_wrt_DTy_rec :
forall DTy1 dskA1 n1,
  open_DTy_wrt_DTy_rec n1 (DT_SkVar_f dskA1) (close_DTy_wrt_DTy_rec n1 dskA1 DTy1) = DTy1.
Proof.
pose proof open_DTy_wrt_DTy_rec_close_DTy_wrt_DTy_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_DTy_wrt_DTy_rec_close_DTy_wrt_DTy_rec : lngen.
#[export] Hint Rewrite open_DTy_wrt_DTy_rec_close_DTy_wrt_DTy_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_DSch_wrt_DTy_rec_close_DSch_wrt_DTy_rec_mutual :
(forall DSch1 dskA1 n1,
  open_DSch_wrt_DTy_rec n1 (DT_SkVar_f dskA1) (close_DSch_wrt_DTy_rec n1 dskA1 DSch1) = DSch1).
Proof.
apply_mutual_ind DSch_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_DSch_wrt_DTy_rec_close_DSch_wrt_DTy_rec :
forall DSch1 dskA1 n1,
  open_DSch_wrt_DTy_rec n1 (DT_SkVar_f dskA1) (close_DSch_wrt_DTy_rec n1 dskA1 DSch1) = DSch1.
Proof.
pose proof open_DSch_wrt_DTy_rec_close_DSch_wrt_DTy_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_DSch_wrt_DTy_rec_close_DSch_wrt_DTy_rec : lngen.
#[export] Hint Rewrite open_DSch_wrt_DTy_rec_close_DSch_wrt_DTy_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Ty_wrt_Ty_rec_close_Ty_wrt_Ty_rec_mutual :
(forall Ty1 skA1 n1,
  open_Ty_wrt_Ty_rec n1 (T_SkVar_f skA1) (close_Ty_wrt_Ty_rec n1 skA1 Ty1) = Ty1).
Proof.
apply_mutual_ind Ty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Ty_wrt_Ty_rec_close_Ty_wrt_Ty_rec :
forall Ty1 skA1 n1,
  open_Ty_wrt_Ty_rec n1 (T_SkVar_f skA1) (close_Ty_wrt_Ty_rec n1 skA1 Ty1) = Ty1.
Proof.
pose proof open_Ty_wrt_Ty_rec_close_Ty_wrt_Ty_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_Ty_wrt_Ty_rec_close_Ty_wrt_Ty_rec : lngen.
#[export] Hint Rewrite open_Ty_wrt_Ty_rec_close_Ty_wrt_Ty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Sch_wrt_Ty_rec_close_Sch_wrt_Ty_rec_mutual :
(forall Sch1 skA1 n1,
  open_Sch_wrt_Ty_rec n1 (T_SkVar_f skA1) (close_Sch_wrt_Ty_rec n1 skA1 Sch1) = Sch1).
Proof.
apply_mutual_ind Sch_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Sch_wrt_Ty_rec_close_Sch_wrt_Ty_rec :
forall Sch1 skA1 n1,
  open_Sch_wrt_Ty_rec n1 (T_SkVar_f skA1) (close_Sch_wrt_Ty_rec n1 skA1 Sch1) = Sch1.
Proof.
pose proof open_Sch_wrt_Ty_rec_close_Sch_wrt_Ty_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_Sch_wrt_Ty_rec_close_Sch_wrt_Ty_rec : lngen.
#[export] Hint Rewrite open_Sch_wrt_Ty_rec_close_Sch_wrt_Ty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_e_wrt_e_rec_close_e_wrt_e_rec_mutual :
(forall e1 x1 n1,
  open_e_wrt_e_rec n1 (e_Var_f x1) (close_e_wrt_e_rec n1 x1 e1) = e1).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_e_wrt_e_rec_close_e_wrt_e_rec :
forall e1 x1 n1,
  open_e_wrt_e_rec n1 (e_Var_f x1) (close_e_wrt_e_rec n1 x1 e1) = e1.
Proof.
pose proof open_e_wrt_e_rec_close_e_wrt_e_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_e_wrt_e_rec_close_e_wrt_e_rec : lngen.
#[export] Hint Rewrite open_e_wrt_e_rec_close_e_wrt_e_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_DTy_wrt_DTy_close_DTy_wrt_DTy :
forall DTy1 dskA1,
  open_DTy_wrt_DTy (close_DTy_wrt_DTy dskA1 DTy1) (DT_SkVar_f dskA1) = DTy1.
Proof.
unfold close_DTy_wrt_DTy; unfold open_DTy_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve open_DTy_wrt_DTy_close_DTy_wrt_DTy : lngen.
#[export] Hint Rewrite open_DTy_wrt_DTy_close_DTy_wrt_DTy using solve [auto] : lngen.

Lemma open_DSch_wrt_DTy_close_DSch_wrt_DTy :
forall DSch1 dskA1,
  open_DSch_wrt_DTy (close_DSch_wrt_DTy dskA1 DSch1) (DT_SkVar_f dskA1) = DSch1.
Proof.
unfold close_DSch_wrt_DTy; unfold open_DSch_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve open_DSch_wrt_DTy_close_DSch_wrt_DTy : lngen.
#[export] Hint Rewrite open_DSch_wrt_DTy_close_DSch_wrt_DTy using solve [auto] : lngen.

Lemma open_Ty_wrt_Ty_close_Ty_wrt_Ty :
forall Ty1 skA1,
  open_Ty_wrt_Ty (close_Ty_wrt_Ty skA1 Ty1) (T_SkVar_f skA1) = Ty1.
Proof.
unfold close_Ty_wrt_Ty; unfold open_Ty_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve open_Ty_wrt_Ty_close_Ty_wrt_Ty : lngen.
#[export] Hint Rewrite open_Ty_wrt_Ty_close_Ty_wrt_Ty using solve [auto] : lngen.

Lemma open_Sch_wrt_Ty_close_Sch_wrt_Ty :
forall Sch1 skA1,
  open_Sch_wrt_Ty (close_Sch_wrt_Ty skA1 Sch1) (T_SkVar_f skA1) = Sch1.
Proof.
unfold close_Sch_wrt_Ty; unfold open_Sch_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve open_Sch_wrt_Ty_close_Sch_wrt_Ty : lngen.
#[export] Hint Rewrite open_Sch_wrt_Ty_close_Sch_wrt_Ty using solve [auto] : lngen.

Lemma open_e_wrt_e_close_e_wrt_e :
forall e1 x1,
  open_e_wrt_e (close_e_wrt_e x1 e1) (e_Var_f x1) = e1.
Proof.
unfold close_e_wrt_e; unfold open_e_wrt_e; default_simp.
Qed.

#[export] Hint Resolve open_e_wrt_e_close_e_wrt_e : lngen.
#[export] Hint Rewrite open_e_wrt_e_close_e_wrt_e using solve [auto] : lngen.

(* begin hide *)

Lemma open_DTy_wrt_DTy_rec_inj_mutual :
(forall DTy2 DTy1 dskA1 n1,
  dskA1 `notin` free_dskvars_DTy DTy2 ->
  dskA1 `notin` free_dskvars_DTy DTy1 ->
  open_DTy_wrt_DTy_rec n1 (DT_SkVar_f dskA1) DTy2 = open_DTy_wrt_DTy_rec n1 (DT_SkVar_f dskA1) DTy1 ->
  DTy2 = DTy1).
Proof.
apply_mutual_ind DTy_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_DTy_wrt_DTy_rec_inj :
forall DTy2 DTy1 dskA1 n1,
  dskA1 `notin` free_dskvars_DTy DTy2 ->
  dskA1 `notin` free_dskvars_DTy DTy1 ->
  open_DTy_wrt_DTy_rec n1 (DT_SkVar_f dskA1) DTy2 = open_DTy_wrt_DTy_rec n1 (DT_SkVar_f dskA1) DTy1 ->
  DTy2 = DTy1.
Proof.
pose proof open_DTy_wrt_DTy_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_DTy_wrt_DTy_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_DSch_wrt_DTy_rec_inj_mutual :
(forall DSch2 DSch1 dskA1 n1,
  dskA1 `notin` free_dskvars_DSch DSch2 ->
  dskA1 `notin` free_dskvars_DSch DSch1 ->
  open_DSch_wrt_DTy_rec n1 (DT_SkVar_f dskA1) DSch2 = open_DSch_wrt_DTy_rec n1 (DT_SkVar_f dskA1) DSch1 ->
  DSch2 = DSch1).
Proof.
apply_mutual_ind DSch_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_DSch_wrt_DTy_rec_inj :
forall DSch2 DSch1 dskA1 n1,
  dskA1 `notin` free_dskvars_DSch DSch2 ->
  dskA1 `notin` free_dskvars_DSch DSch1 ->
  open_DSch_wrt_DTy_rec n1 (DT_SkVar_f dskA1) DSch2 = open_DSch_wrt_DTy_rec n1 (DT_SkVar_f dskA1) DSch1 ->
  DSch2 = DSch1.
Proof.
pose proof open_DSch_wrt_DTy_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_DSch_wrt_DTy_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Ty_wrt_Ty_rec_inj_mutual :
(forall Ty2 Ty1 skA1 n1,
  skA1 `notin` free_skvars_Ty Ty2 ->
  skA1 `notin` free_skvars_Ty Ty1 ->
  open_Ty_wrt_Ty_rec n1 (T_SkVar_f skA1) Ty2 = open_Ty_wrt_Ty_rec n1 (T_SkVar_f skA1) Ty1 ->
  Ty2 = Ty1).
Proof.
apply_mutual_ind Ty_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Ty_wrt_Ty_rec_inj :
forall Ty2 Ty1 skA1 n1,
  skA1 `notin` free_skvars_Ty Ty2 ->
  skA1 `notin` free_skvars_Ty Ty1 ->
  open_Ty_wrt_Ty_rec n1 (T_SkVar_f skA1) Ty2 = open_Ty_wrt_Ty_rec n1 (T_SkVar_f skA1) Ty1 ->
  Ty2 = Ty1.
Proof.
pose proof open_Ty_wrt_Ty_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_Ty_wrt_Ty_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Sch_wrt_Ty_rec_inj_mutual :
(forall Sch2 Sch1 skA1 n1,
  skA1 `notin` free_skvars_Sch Sch2 ->
  skA1 `notin` free_skvars_Sch Sch1 ->
  open_Sch_wrt_Ty_rec n1 (T_SkVar_f skA1) Sch2 = open_Sch_wrt_Ty_rec n1 (T_SkVar_f skA1) Sch1 ->
  Sch2 = Sch1).
Proof.
apply_mutual_ind Sch_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Sch_wrt_Ty_rec_inj :
forall Sch2 Sch1 skA1 n1,
  skA1 `notin` free_skvars_Sch Sch2 ->
  skA1 `notin` free_skvars_Sch Sch1 ->
  open_Sch_wrt_Ty_rec n1 (T_SkVar_f skA1) Sch2 = open_Sch_wrt_Ty_rec n1 (T_SkVar_f skA1) Sch1 ->
  Sch2 = Sch1.
Proof.
pose proof open_Sch_wrt_Ty_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_Sch_wrt_Ty_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_e_wrt_e_rec_inj_mutual :
(forall e2 e1 x1 n1,
  x1 `notin` free_xs_e e2 ->
  x1 `notin` free_xs_e e1 ->
  open_e_wrt_e_rec n1 (e_Var_f x1) e2 = open_e_wrt_e_rec n1 (e_Var_f x1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind e_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_e_wrt_e_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` free_xs_e e2 ->
  x1 `notin` free_xs_e e1 ->
  open_e_wrt_e_rec n1 (e_Var_f x1) e2 = open_e_wrt_e_rec n1 (e_Var_f x1) e1 ->
  e2 = e1.
Proof.
pose proof open_e_wrt_e_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_e_wrt_e_rec_inj : lngen.

(* end hide *)

Lemma open_DTy_wrt_DTy_inj :
forall DTy2 DTy1 dskA1,
  dskA1 `notin` free_dskvars_DTy DTy2 ->
  dskA1 `notin` free_dskvars_DTy DTy1 ->
  open_DTy_wrt_DTy DTy2 (DT_SkVar_f dskA1) = open_DTy_wrt_DTy DTy1 (DT_SkVar_f dskA1) ->
  DTy2 = DTy1.
Proof.
unfold open_DTy_wrt_DTy; eauto with lngen.
Qed.

#[export] Hint Immediate open_DTy_wrt_DTy_inj : lngen.

Lemma open_DSch_wrt_DTy_inj :
forall DSch2 DSch1 dskA1,
  dskA1 `notin` free_dskvars_DSch DSch2 ->
  dskA1 `notin` free_dskvars_DSch DSch1 ->
  open_DSch_wrt_DTy DSch2 (DT_SkVar_f dskA1) = open_DSch_wrt_DTy DSch1 (DT_SkVar_f dskA1) ->
  DSch2 = DSch1.
Proof.
unfold open_DSch_wrt_DTy; eauto with lngen.
Qed.

#[export] Hint Immediate open_DSch_wrt_DTy_inj : lngen.

Lemma open_Ty_wrt_Ty_inj :
forall Ty2 Ty1 skA1,
  skA1 `notin` free_skvars_Ty Ty2 ->
  skA1 `notin` free_skvars_Ty Ty1 ->
  open_Ty_wrt_Ty Ty2 (T_SkVar_f skA1) = open_Ty_wrt_Ty Ty1 (T_SkVar_f skA1) ->
  Ty2 = Ty1.
Proof.
unfold open_Ty_wrt_Ty; eauto with lngen.
Qed.

#[export] Hint Immediate open_Ty_wrt_Ty_inj : lngen.

Lemma open_Sch_wrt_Ty_inj :
forall Sch2 Sch1 skA1,
  skA1 `notin` free_skvars_Sch Sch2 ->
  skA1 `notin` free_skvars_Sch Sch1 ->
  open_Sch_wrt_Ty Sch2 (T_SkVar_f skA1) = open_Sch_wrt_Ty Sch1 (T_SkVar_f skA1) ->
  Sch2 = Sch1.
Proof.
unfold open_Sch_wrt_Ty; eauto with lngen.
Qed.

#[export] Hint Immediate open_Sch_wrt_Ty_inj : lngen.

Lemma open_e_wrt_e_inj :
forall e2 e1 x1,
  x1 `notin` free_xs_e e2 ->
  x1 `notin` free_xs_e e1 ->
  open_e_wrt_e e2 (e_Var_f x1) = open_e_wrt_e e1 (e_Var_f x1) ->
  e2 = e1.
Proof.
unfold open_e_wrt_e; eauto with lngen.
Qed.

#[export] Hint Immediate open_e_wrt_e_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_DTy_wrt_DTy_of_lc_DTy_mutual :
(forall DTy1,
  lc_DTy DTy1 ->
  degree_DTy_wrt_DTy 0 DTy1).
Proof.
apply_mutual_ind lc_DTy_mutind;
intros;
let dskA1 := fresh "dskA1" in pick_fresh dskA1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_DTy_wrt_DTy_of_lc_DTy :
forall DTy1,
  lc_DTy DTy1 ->
  degree_DTy_wrt_DTy 0 DTy1.
Proof.
pose proof degree_DTy_wrt_DTy_of_lc_DTy_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_DTy_wrt_DTy_of_lc_DTy : lngen.

(* begin hide *)

Lemma degree_DSch_wrt_DTy_of_lc_DSch_mutual :
(forall DSch1,
  lc_DSch DSch1 ->
  degree_DSch_wrt_DTy 0 DSch1).
Proof.
apply_mutual_ind lc_DSch_mutind;
intros;
let dskA1 := fresh "dskA1" in pick_fresh dskA1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_DSch_wrt_DTy_of_lc_DSch :
forall DSch1,
  lc_DSch DSch1 ->
  degree_DSch_wrt_DTy 0 DSch1.
Proof.
pose proof degree_DSch_wrt_DTy_of_lc_DSch_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_DSch_wrt_DTy_of_lc_DSch : lngen.

(* begin hide *)

Lemma degree_Ty_wrt_Ty_of_lc_Ty_mutual :
(forall Ty1,
  lc_Ty Ty1 ->
  degree_Ty_wrt_Ty 0 Ty1).
Proof.
apply_mutual_ind lc_Ty_mutind;
intros;
let skA1 := fresh "skA1" in pick_fresh skA1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_Ty_wrt_Ty_of_lc_Ty :
forall Ty1,
  lc_Ty Ty1 ->
  degree_Ty_wrt_Ty 0 Ty1.
Proof.
pose proof degree_Ty_wrt_Ty_of_lc_Ty_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Ty_wrt_Ty_of_lc_Ty : lngen.

(* begin hide *)

Lemma degree_Sch_wrt_Ty_of_lc_Sch_mutual :
(forall Sch1,
  lc_Sch Sch1 ->
  degree_Sch_wrt_Ty 0 Sch1).
Proof.
apply_mutual_ind lc_Sch_mutind;
intros;
let skA1 := fresh "skA1" in pick_fresh skA1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_Sch_wrt_Ty_of_lc_Sch :
forall Sch1,
  lc_Sch Sch1 ->
  degree_Sch_wrt_Ty 0 Sch1.
Proof.
pose proof degree_Sch_wrt_Ty_of_lc_Sch_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Sch_wrt_Ty_of_lc_Sch : lngen.

(* begin hide *)

Lemma degree_e_wrt_e_of_lc_e_mutual :
(forall e1,
  lc_e e1 ->
  degree_e_wrt_e 0 e1).
Proof.
apply_mutual_ind lc_e_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_e_wrt_e_of_lc_e :
forall e1,
  lc_e e1 ->
  degree_e_wrt_e 0 e1.
Proof.
pose proof degree_e_wrt_e_of_lc_e_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_e_wrt_e_of_lc_e : lngen.

(* begin hide *)

Lemma lc_DTy_of_degree_size_mutual :
forall i1,
(forall DTy1,
  size_DTy DTy1 = i1 ->
  degree_DTy_wrt_DTy 0 DTy1 ->
  lc_DTy DTy1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind DTy_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_DTy_of_degree :
forall DTy1,
  degree_DTy_wrt_DTy 0 DTy1 ->
  lc_DTy DTy1.
Proof.
intros DTy1; intros;
pose proof (lc_DTy_of_degree_size_mutual (size_DTy DTy1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_DTy_of_degree : lngen.

(* begin hide *)

Lemma lc_DSch_of_degree_size_mutual :
forall i1,
(forall DSch1,
  size_DSch DSch1 = i1 ->
  degree_DSch_wrt_DTy 0 DSch1 ->
  lc_DSch DSch1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind DSch_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_DSch_of_degree :
forall DSch1,
  degree_DSch_wrt_DTy 0 DSch1 ->
  lc_DSch DSch1.
Proof.
intros DSch1; intros;
pose proof (lc_DSch_of_degree_size_mutual (size_DSch DSch1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_DSch_of_degree : lngen.

(* begin hide *)

Lemma lc_Ty_of_degree_size_mutual :
forall i1,
(forall Ty1,
  size_Ty Ty1 = i1 ->
  degree_Ty_wrt_Ty 0 Ty1 ->
  lc_Ty Ty1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind Ty_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_Ty_of_degree :
forall Ty1,
  degree_Ty_wrt_Ty 0 Ty1 ->
  lc_Ty Ty1.
Proof.
intros Ty1; intros;
pose proof (lc_Ty_of_degree_size_mutual (size_Ty Ty1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_Ty_of_degree : lngen.

(* begin hide *)

Lemma lc_Sch_of_degree_size_mutual :
forall i1,
(forall Sch1,
  size_Sch Sch1 = i1 ->
  degree_Sch_wrt_Ty 0 Sch1 ->
  lc_Sch Sch1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind Sch_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_Sch_of_degree :
forall Sch1,
  degree_Sch_wrt_Ty 0 Sch1 ->
  lc_Sch Sch1.
Proof.
intros Sch1; intros;
pose proof (lc_Sch_of_degree_size_mutual (size_Sch Sch1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_Sch_of_degree : lngen.

(* begin hide *)

Lemma lc_e_of_degree_size_mutual :
forall i1,
(forall e1,
  size_e e1 = i1 ->
  degree_e_wrt_e 0 e1 ->
  lc_e e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind e_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_e_of_degree :
forall e1,
  degree_e_wrt_e 0 e1 ->
  lc_e e1.
Proof.
intros e1; intros;
pose proof (lc_e_of_degree_size_mutual (size_e e1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_e_of_degree : lngen.

Ltac DTy_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_DTy_wrt_DTy_of_lc_DTy in J1; clear H
          end).

Ltac DSch_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_DSch_wrt_DTy_of_lc_DSch in J1; clear H
          end).

Ltac Ty_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_Ty_wrt_Ty_of_lc_Ty in J1; clear H
          end).

Ltac Sch_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_Sch_wrt_Ty_of_lc_Sch in J1; clear H
          end).

Ltac e_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_e_wrt_e_of_lc_e in J1; clear H
          end).

Lemma lc_DS_Forall_exists :
forall dskA1 DSch1,
  lc_DSch (open_DSch_wrt_DTy DSch1 (DT_SkVar_f dskA1)) ->
  lc_DSch (DS_Forall DSch1).
Proof.
intros; DSch_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_S_Forall_exists :
forall skA1 Sch1,
  lc_Sch (open_Sch_wrt_Ty Sch1 (T_SkVar_f skA1)) ->
  lc_Sch (S_Forall Sch1).
Proof.
intros; Sch_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_e_Lam_exists :
forall x1 e1,
  lc_e (open_e_wrt_e e1 (e_Var_f x1)) ->
  lc_e (e_Lam e1).
Proof.
intros; e_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_e_Let_exists :
forall x1 e1 e2,
  lc_e e1 ->
  lc_e (open_e_wrt_e e2 (e_Var_f x1)) ->
  lc_e (e_Let e1 e2).
Proof.
intros; e_lc_exists_tac; eauto 6 with lngen.
Qed.

#[export] Hint Extern 1 (lc_DSch (DS_Forall _)) =>
  let dskA1 := fresh in
  pick_fresh dskA1;
  apply (lc_DS_Forall_exists dskA1) : core.

#[export] Hint Extern 1 (lc_Sch (S_Forall _)) =>
  let skA1 := fresh in
  pick_fresh skA1;
  apply (lc_S_Forall_exists skA1) : core.

#[export] Hint Extern 1 (lc_e (e_Lam _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_e_Lam_exists x1) : core.

#[export] Hint Extern 1 (lc_e (e_Let _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_e_Let_exists x1) : core.

Lemma lc_body_DTy_wrt_DTy :
forall DTy1 DTy2,
  body_DTy_wrt_DTy DTy1 ->
  lc_DTy DTy2 ->
  lc_DTy (open_DTy_wrt_DTy DTy1 DTy2).
Proof.
unfold body_DTy_wrt_DTy;
default_simp;
let dskA1 := fresh "x" in
pick_fresh dskA1;
specialize_all dskA1;
DTy_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_DTy_wrt_DTy : lngen.

Lemma lc_body_DSch_wrt_DTy :
forall DSch1 DTy1,
  body_DSch_wrt_DTy DSch1 ->
  lc_DTy DTy1 ->
  lc_DSch (open_DSch_wrt_DTy DSch1 DTy1).
Proof.
unfold body_DSch_wrt_DTy;
default_simp;
let dskA1 := fresh "x" in
pick_fresh dskA1;
specialize_all dskA1;
DSch_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_DSch_wrt_DTy : lngen.

Lemma lc_body_Ty_wrt_Ty :
forall Ty1 Ty2,
  body_Ty_wrt_Ty Ty1 ->
  lc_Ty Ty2 ->
  lc_Ty (open_Ty_wrt_Ty Ty1 Ty2).
Proof.
unfold body_Ty_wrt_Ty;
default_simp;
let skA1 := fresh "x" in
pick_fresh skA1;
specialize_all skA1;
Ty_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_Ty_wrt_Ty : lngen.

Lemma lc_body_Sch_wrt_Ty :
forall Sch1 Ty1,
  body_Sch_wrt_Ty Sch1 ->
  lc_Ty Ty1 ->
  lc_Sch (open_Sch_wrt_Ty Sch1 Ty1).
Proof.
unfold body_Sch_wrt_Ty;
default_simp;
let skA1 := fresh "x" in
pick_fresh skA1;
specialize_all skA1;
Sch_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_Sch_wrt_Ty : lngen.

Lemma lc_body_e_wrt_e :
forall e1 e2,
  body_e_wrt_e e1 ->
  lc_e e2 ->
  lc_e (open_e_wrt_e e1 e2).
Proof.
unfold body_e_wrt_e;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
e_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_e_wrt_e : lngen.

Lemma lc_body_DS_Forall_1 :
forall DSch1,
  lc_DSch (DS_Forall DSch1) ->
  body_DSch_wrt_DTy DSch1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_DS_Forall_1 : lngen.

Lemma lc_body_S_Forall_1 :
forall Sch1,
  lc_Sch (S_Forall Sch1) ->
  body_Sch_wrt_Ty Sch1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_S_Forall_1 : lngen.

Lemma lc_body_e_Lam_1 :
forall e1,
  lc_e (e_Lam e1) ->
  body_e_wrt_e e1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_e_Lam_1 : lngen.

Lemma lc_body_e_Let_2 :
forall e1 e2,
  lc_e (e_Let e1 e2) ->
  body_e_wrt_e e2.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_e_Let_2 : lngen.

(* begin hide *)

Lemma lc_DTy_unique_mutual :
(forall DTy1 (proof2 proof3 : lc_DTy DTy1), proof2 = proof3).
Proof.
apply_mutual_ind lc_DTy_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_DTy_unique :
forall DTy1 (proof2 proof3 : lc_DTy DTy1), proof2 = proof3.
Proof.
pose proof lc_DTy_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_DTy_unique : lngen.

(* begin hide *)

Lemma lc_DSch_unique_mutual :
(forall DSch1 (proof2 proof3 : lc_DSch DSch1), proof2 = proof3).
Proof.
apply_mutual_ind lc_DSch_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_DSch_unique :
forall DSch1 (proof2 proof3 : lc_DSch DSch1), proof2 = proof3.
Proof.
pose proof lc_DSch_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_DSch_unique : lngen.

(* begin hide *)

Lemma lc_Ty_unique_mutual :
(forall Ty1 (proof2 proof3 : lc_Ty Ty1), proof2 = proof3).
Proof.
apply_mutual_ind lc_Ty_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_Ty_unique :
forall Ty1 (proof2 proof3 : lc_Ty Ty1), proof2 = proof3.
Proof.
pose proof lc_Ty_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_Ty_unique : lngen.

(* begin hide *)

Lemma lc_Sch_unique_mutual :
(forall Sch1 (proof2 proof3 : lc_Sch Sch1), proof2 = proof3).
Proof.
apply_mutual_ind lc_Sch_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_Sch_unique :
forall Sch1 (proof2 proof3 : lc_Sch Sch1), proof2 = proof3.
Proof.
pose proof lc_Sch_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_Sch_unique : lngen.

(* begin hide *)

Lemma lc_e_unique_mutual :
(forall e1 (proof2 proof3 : lc_e e1), proof2 = proof3).
Proof.
apply_mutual_ind lc_e_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_e_unique :
forall e1 (proof2 proof3 : lc_e e1), proof2 = proof3.
Proof.
pose proof lc_e_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_e_unique : lngen.

(* begin hide *)

Lemma lc_DTy_of_lc_set_DTy_mutual :
(forall DTy1, lc_set_DTy DTy1 -> lc_DTy DTy1).
Proof.
apply_mutual_ind lc_set_DTy_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_DTy_of_lc_set_DTy :
forall DTy1, lc_set_DTy DTy1 -> lc_DTy DTy1.
Proof.
pose proof lc_DTy_of_lc_set_DTy_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_DTy_of_lc_set_DTy : lngen.

(* begin hide *)

Lemma lc_DSch_of_lc_set_DSch_mutual :
(forall DSch1, lc_set_DSch DSch1 -> lc_DSch DSch1).
Proof.
apply_mutual_ind lc_set_DSch_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_DSch_of_lc_set_DSch :
forall DSch1, lc_set_DSch DSch1 -> lc_DSch DSch1.
Proof.
pose proof lc_DSch_of_lc_set_DSch_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_DSch_of_lc_set_DSch : lngen.

(* begin hide *)

Lemma lc_Ty_of_lc_set_Ty_mutual :
(forall Ty1, lc_set_Ty Ty1 -> lc_Ty Ty1).
Proof.
apply_mutual_ind lc_set_Ty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_Ty_of_lc_set_Ty :
forall Ty1, lc_set_Ty Ty1 -> lc_Ty Ty1.
Proof.
pose proof lc_Ty_of_lc_set_Ty_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_Ty_of_lc_set_Ty : lngen.

(* begin hide *)

Lemma lc_Sch_of_lc_set_Sch_mutual :
(forall Sch1, lc_set_Sch Sch1 -> lc_Sch Sch1).
Proof.
apply_mutual_ind lc_set_Sch_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_Sch_of_lc_set_Sch :
forall Sch1, lc_set_Sch Sch1 -> lc_Sch Sch1.
Proof.
pose proof lc_Sch_of_lc_set_Sch_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_Sch_of_lc_set_Sch : lngen.

(* begin hide *)

Lemma lc_e_of_lc_set_e_mutual :
(forall e1, lc_set_e e1 -> lc_e e1).
Proof.
apply_mutual_ind lc_set_e_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_e_of_lc_set_e :
forall e1, lc_set_e e1 -> lc_e e1.
Proof.
pose proof lc_e_of_lc_set_e_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_e_of_lc_set_e : lngen.

(* begin hide *)

Lemma lc_set_DTy_of_lc_DTy_size_mutual :
forall i1,
(forall DTy1,
  size_DTy DTy1 = i1 ->
  lc_DTy DTy1 ->
  lc_set_DTy DTy1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind DTy_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_DTy_of_lc_DTy];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_DTy_of_lc_DTy :
forall DTy1,
  lc_DTy DTy1 ->
  lc_set_DTy DTy1.
Proof.
intros DTy1; intros;
pose proof (lc_set_DTy_of_lc_DTy_size_mutual (size_DTy DTy1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_DTy_of_lc_DTy : lngen.

(* begin hide *)

Lemma lc_set_DSch_of_lc_DSch_size_mutual :
forall i1,
(forall DSch1,
  size_DSch DSch1 = i1 ->
  lc_DSch DSch1 ->
  lc_set_DSch DSch1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind DSch_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_DSch_of_lc_DSch
 | apply lc_set_DTy_of_lc_DTy];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_DSch_of_lc_DSch :
forall DSch1,
  lc_DSch DSch1 ->
  lc_set_DSch DSch1.
Proof.
intros DSch1; intros;
pose proof (lc_set_DSch_of_lc_DSch_size_mutual (size_DSch DSch1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_DSch_of_lc_DSch : lngen.

(* begin hide *)

Lemma lc_set_Ty_of_lc_Ty_size_mutual :
forall i1,
(forall Ty1,
  size_Ty Ty1 = i1 ->
  lc_Ty Ty1 ->
  lc_set_Ty Ty1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind Ty_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_Ty_of_lc_Ty];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_Ty_of_lc_Ty :
forall Ty1,
  lc_Ty Ty1 ->
  lc_set_Ty Ty1.
Proof.
intros Ty1; intros;
pose proof (lc_set_Ty_of_lc_Ty_size_mutual (size_Ty Ty1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_Ty_of_lc_Ty : lngen.

(* begin hide *)

Lemma lc_set_Sch_of_lc_Sch_size_mutual :
forall i1,
(forall Sch1,
  size_Sch Sch1 = i1 ->
  lc_Sch Sch1 ->
  lc_set_Sch Sch1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind Sch_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_Sch_of_lc_Sch
 | apply lc_set_Ty_of_lc_Ty];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_Sch_of_lc_Sch :
forall Sch1,
  lc_Sch Sch1 ->
  lc_set_Sch Sch1.
Proof.
intros Sch1; intros;
pose proof (lc_set_Sch_of_lc_Sch_size_mutual (size_Sch Sch1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_Sch_of_lc_Sch : lngen.

(* begin hide *)

Lemma lc_set_e_of_lc_e_size_mutual :
forall i1,
(forall e1,
  size_e e1 = i1 ->
  lc_e e1 ->
  lc_set_e e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind e_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_e_of_lc_e];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_e_of_lc_e :
forall e1,
  lc_e e1 ->
  lc_set_e e1.
Proof.
intros e1; intros;
pose proof (lc_set_e_of_lc_e_size_mutual (size_e e1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_e_of_lc_e : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_DTy_wrt_DTy_rec_degree_DTy_wrt_DTy_mutual :
(forall DTy1 dskA1 n1,
  degree_DTy_wrt_DTy n1 DTy1 ->
  dskA1 `notin` free_dskvars_DTy DTy1 ->
  close_DTy_wrt_DTy_rec n1 dskA1 DTy1 = DTy1).
Proof.
apply_mutual_ind DTy_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_DTy_wrt_DTy_rec_degree_DTy_wrt_DTy :
forall DTy1 dskA1 n1,
  degree_DTy_wrt_DTy n1 DTy1 ->
  dskA1 `notin` free_dskvars_DTy DTy1 ->
  close_DTy_wrt_DTy_rec n1 dskA1 DTy1 = DTy1.
Proof.
pose proof close_DTy_wrt_DTy_rec_degree_DTy_wrt_DTy_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_DTy_wrt_DTy_rec_degree_DTy_wrt_DTy : lngen.
#[export] Hint Rewrite close_DTy_wrt_DTy_rec_degree_DTy_wrt_DTy using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_DSch_wrt_DTy_rec_degree_DSch_wrt_DTy_mutual :
(forall DSch1 dskA1 n1,
  degree_DSch_wrt_DTy n1 DSch1 ->
  dskA1 `notin` free_dskvars_DSch DSch1 ->
  close_DSch_wrt_DTy_rec n1 dskA1 DSch1 = DSch1).
Proof.
apply_mutual_ind DSch_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_DSch_wrt_DTy_rec_degree_DSch_wrt_DTy :
forall DSch1 dskA1 n1,
  degree_DSch_wrt_DTy n1 DSch1 ->
  dskA1 `notin` free_dskvars_DSch DSch1 ->
  close_DSch_wrt_DTy_rec n1 dskA1 DSch1 = DSch1.
Proof.
pose proof close_DSch_wrt_DTy_rec_degree_DSch_wrt_DTy_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_DSch_wrt_DTy_rec_degree_DSch_wrt_DTy : lngen.
#[export] Hint Rewrite close_DSch_wrt_DTy_rec_degree_DSch_wrt_DTy using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Ty_wrt_Ty_rec_degree_Ty_wrt_Ty_mutual :
(forall Ty1 skA1 n1,
  degree_Ty_wrt_Ty n1 Ty1 ->
  skA1 `notin` free_skvars_Ty Ty1 ->
  close_Ty_wrt_Ty_rec n1 skA1 Ty1 = Ty1).
Proof.
apply_mutual_ind Ty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Ty_wrt_Ty_rec_degree_Ty_wrt_Ty :
forall Ty1 skA1 n1,
  degree_Ty_wrt_Ty n1 Ty1 ->
  skA1 `notin` free_skvars_Ty Ty1 ->
  close_Ty_wrt_Ty_rec n1 skA1 Ty1 = Ty1.
Proof.
pose proof close_Ty_wrt_Ty_rec_degree_Ty_wrt_Ty_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_Ty_wrt_Ty_rec_degree_Ty_wrt_Ty : lngen.
#[export] Hint Rewrite close_Ty_wrt_Ty_rec_degree_Ty_wrt_Ty using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Sch_wrt_Ty_rec_degree_Sch_wrt_Ty_mutual :
(forall Sch1 skA1 n1,
  degree_Sch_wrt_Ty n1 Sch1 ->
  skA1 `notin` free_skvars_Sch Sch1 ->
  close_Sch_wrt_Ty_rec n1 skA1 Sch1 = Sch1).
Proof.
apply_mutual_ind Sch_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Sch_wrt_Ty_rec_degree_Sch_wrt_Ty :
forall Sch1 skA1 n1,
  degree_Sch_wrt_Ty n1 Sch1 ->
  skA1 `notin` free_skvars_Sch Sch1 ->
  close_Sch_wrt_Ty_rec n1 skA1 Sch1 = Sch1.
Proof.
pose proof close_Sch_wrt_Ty_rec_degree_Sch_wrt_Ty_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_Sch_wrt_Ty_rec_degree_Sch_wrt_Ty : lngen.
#[export] Hint Rewrite close_Sch_wrt_Ty_rec_degree_Sch_wrt_Ty using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_e_wrt_e_rec_degree_e_wrt_e_mutual :
(forall e1 x1 n1,
  degree_e_wrt_e n1 e1 ->
  x1 `notin` free_xs_e e1 ->
  close_e_wrt_e_rec n1 x1 e1 = e1).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_e_wrt_e_rec_degree_e_wrt_e :
forall e1 x1 n1,
  degree_e_wrt_e n1 e1 ->
  x1 `notin` free_xs_e e1 ->
  close_e_wrt_e_rec n1 x1 e1 = e1.
Proof.
pose proof close_e_wrt_e_rec_degree_e_wrt_e_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_e_wrt_e_rec_degree_e_wrt_e : lngen.
#[export] Hint Rewrite close_e_wrt_e_rec_degree_e_wrt_e using solve [auto] : lngen.

(* end hide *)

Lemma close_DTy_wrt_DTy_lc_DTy :
forall DTy1 dskA1,
  lc_DTy DTy1 ->
  dskA1 `notin` free_dskvars_DTy DTy1 ->
  close_DTy_wrt_DTy dskA1 DTy1 = DTy1.
Proof.
unfold close_DTy_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve close_DTy_wrt_DTy_lc_DTy : lngen.
#[export] Hint Rewrite close_DTy_wrt_DTy_lc_DTy using solve [auto] : lngen.

Lemma close_DSch_wrt_DTy_lc_DSch :
forall DSch1 dskA1,
  lc_DSch DSch1 ->
  dskA1 `notin` free_dskvars_DSch DSch1 ->
  close_DSch_wrt_DTy dskA1 DSch1 = DSch1.
Proof.
unfold close_DSch_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve close_DSch_wrt_DTy_lc_DSch : lngen.
#[export] Hint Rewrite close_DSch_wrt_DTy_lc_DSch using solve [auto] : lngen.

Lemma close_Ty_wrt_Ty_lc_Ty :
forall Ty1 skA1,
  lc_Ty Ty1 ->
  skA1 `notin` free_skvars_Ty Ty1 ->
  close_Ty_wrt_Ty skA1 Ty1 = Ty1.
Proof.
unfold close_Ty_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve close_Ty_wrt_Ty_lc_Ty : lngen.
#[export] Hint Rewrite close_Ty_wrt_Ty_lc_Ty using solve [auto] : lngen.

Lemma close_Sch_wrt_Ty_lc_Sch :
forall Sch1 skA1,
  lc_Sch Sch1 ->
  skA1 `notin` free_skvars_Sch Sch1 ->
  close_Sch_wrt_Ty skA1 Sch1 = Sch1.
Proof.
unfold close_Sch_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve close_Sch_wrt_Ty_lc_Sch : lngen.
#[export] Hint Rewrite close_Sch_wrt_Ty_lc_Sch using solve [auto] : lngen.

Lemma close_e_wrt_e_lc_e :
forall e1 x1,
  lc_e e1 ->
  x1 `notin` free_xs_e e1 ->
  close_e_wrt_e x1 e1 = e1.
Proof.
unfold close_e_wrt_e; default_simp.
Qed.

#[export] Hint Resolve close_e_wrt_e_lc_e : lngen.
#[export] Hint Rewrite close_e_wrt_e_lc_e using solve [auto] : lngen.

(* begin hide *)

Lemma open_DTy_wrt_DTy_rec_degree_DTy_wrt_DTy_mutual :
(forall DTy2 DTy1 n1,
  degree_DTy_wrt_DTy n1 DTy2 ->
  open_DTy_wrt_DTy_rec n1 DTy1 DTy2 = DTy2).
Proof.
apply_mutual_ind DTy_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_DTy_wrt_DTy_rec_degree_DTy_wrt_DTy :
forall DTy2 DTy1 n1,
  degree_DTy_wrt_DTy n1 DTy2 ->
  open_DTy_wrt_DTy_rec n1 DTy1 DTy2 = DTy2.
Proof.
pose proof open_DTy_wrt_DTy_rec_degree_DTy_wrt_DTy_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_DTy_wrt_DTy_rec_degree_DTy_wrt_DTy : lngen.
#[export] Hint Rewrite open_DTy_wrt_DTy_rec_degree_DTy_wrt_DTy using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_DSch_wrt_DTy_rec_degree_DSch_wrt_DTy_mutual :
(forall DSch1 DTy1 n1,
  degree_DSch_wrt_DTy n1 DSch1 ->
  open_DSch_wrt_DTy_rec n1 DTy1 DSch1 = DSch1).
Proof.
apply_mutual_ind DSch_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_DSch_wrt_DTy_rec_degree_DSch_wrt_DTy :
forall DSch1 DTy1 n1,
  degree_DSch_wrt_DTy n1 DSch1 ->
  open_DSch_wrt_DTy_rec n1 DTy1 DSch1 = DSch1.
Proof.
pose proof open_DSch_wrt_DTy_rec_degree_DSch_wrt_DTy_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_DSch_wrt_DTy_rec_degree_DSch_wrt_DTy : lngen.
#[export] Hint Rewrite open_DSch_wrt_DTy_rec_degree_DSch_wrt_DTy using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Ty_wrt_Ty_rec_degree_Ty_wrt_Ty_mutual :
(forall Ty2 Ty1 n1,
  degree_Ty_wrt_Ty n1 Ty2 ->
  open_Ty_wrt_Ty_rec n1 Ty1 Ty2 = Ty2).
Proof.
apply_mutual_ind Ty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Ty_wrt_Ty_rec_degree_Ty_wrt_Ty :
forall Ty2 Ty1 n1,
  degree_Ty_wrt_Ty n1 Ty2 ->
  open_Ty_wrt_Ty_rec n1 Ty1 Ty2 = Ty2.
Proof.
pose proof open_Ty_wrt_Ty_rec_degree_Ty_wrt_Ty_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_Ty_wrt_Ty_rec_degree_Ty_wrt_Ty : lngen.
#[export] Hint Rewrite open_Ty_wrt_Ty_rec_degree_Ty_wrt_Ty using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Sch_wrt_Ty_rec_degree_Sch_wrt_Ty_mutual :
(forall Sch1 Ty1 n1,
  degree_Sch_wrt_Ty n1 Sch1 ->
  open_Sch_wrt_Ty_rec n1 Ty1 Sch1 = Sch1).
Proof.
apply_mutual_ind Sch_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Sch_wrt_Ty_rec_degree_Sch_wrt_Ty :
forall Sch1 Ty1 n1,
  degree_Sch_wrt_Ty n1 Sch1 ->
  open_Sch_wrt_Ty_rec n1 Ty1 Sch1 = Sch1.
Proof.
pose proof open_Sch_wrt_Ty_rec_degree_Sch_wrt_Ty_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_Sch_wrt_Ty_rec_degree_Sch_wrt_Ty : lngen.
#[export] Hint Rewrite open_Sch_wrt_Ty_rec_degree_Sch_wrt_Ty using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_e_wrt_e_rec_degree_e_wrt_e_mutual :
(forall e2 e1 n1,
  degree_e_wrt_e n1 e2 ->
  open_e_wrt_e_rec n1 e1 e2 = e2).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_e_wrt_e_rec_degree_e_wrt_e :
forall e2 e1 n1,
  degree_e_wrt_e n1 e2 ->
  open_e_wrt_e_rec n1 e1 e2 = e2.
Proof.
pose proof open_e_wrt_e_rec_degree_e_wrt_e_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_e_wrt_e_rec_degree_e_wrt_e : lngen.
#[export] Hint Rewrite open_e_wrt_e_rec_degree_e_wrt_e using solve [auto] : lngen.

(* end hide *)

Lemma open_DTy_wrt_DTy_lc_DTy :
forall DTy2 DTy1,
  lc_DTy DTy2 ->
  open_DTy_wrt_DTy DTy2 DTy1 = DTy2.
Proof.
unfold open_DTy_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve open_DTy_wrt_DTy_lc_DTy : lngen.
#[export] Hint Rewrite open_DTy_wrt_DTy_lc_DTy using solve [auto] : lngen.

Lemma open_DSch_wrt_DTy_lc_DSch :
forall DSch1 DTy1,
  lc_DSch DSch1 ->
  open_DSch_wrt_DTy DSch1 DTy1 = DSch1.
Proof.
unfold open_DSch_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve open_DSch_wrt_DTy_lc_DSch : lngen.
#[export] Hint Rewrite open_DSch_wrt_DTy_lc_DSch using solve [auto] : lngen.

Lemma open_Ty_wrt_Ty_lc_Ty :
forall Ty2 Ty1,
  lc_Ty Ty2 ->
  open_Ty_wrt_Ty Ty2 Ty1 = Ty2.
Proof.
unfold open_Ty_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve open_Ty_wrt_Ty_lc_Ty : lngen.
#[export] Hint Rewrite open_Ty_wrt_Ty_lc_Ty using solve [auto] : lngen.

Lemma open_Sch_wrt_Ty_lc_Sch :
forall Sch1 Ty1,
  lc_Sch Sch1 ->
  open_Sch_wrt_Ty Sch1 Ty1 = Sch1.
Proof.
unfold open_Sch_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve open_Sch_wrt_Ty_lc_Sch : lngen.
#[export] Hint Rewrite open_Sch_wrt_Ty_lc_Sch using solve [auto] : lngen.

Lemma open_e_wrt_e_lc_e :
forall e2 e1,
  lc_e e2 ->
  open_e_wrt_e e2 e1 = e2.
Proof.
unfold open_e_wrt_e; default_simp.
Qed.

#[export] Hint Resolve open_e_wrt_e_lc_e : lngen.
#[export] Hint Rewrite open_e_wrt_e_lc_e using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma free_dskvars_DTy_close_DTy_wrt_DTy_rec_mutual :
(forall DTy1 dskA1 n1,
  free_dskvars_DTy (close_DTy_wrt_DTy_rec n1 dskA1 DTy1) [=] remove dskA1 (free_dskvars_DTy DTy1)).
Proof.
apply_mutual_ind DTy_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma free_dskvars_DTy_close_DTy_wrt_DTy_rec :
forall DTy1 dskA1 n1,
  free_dskvars_DTy (close_DTy_wrt_DTy_rec n1 dskA1 DTy1) [=] remove dskA1 (free_dskvars_DTy DTy1).
Proof.
pose proof free_dskvars_DTy_close_DTy_wrt_DTy_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_dskvars_DTy_close_DTy_wrt_DTy_rec : lngen.
#[export] Hint Rewrite free_dskvars_DTy_close_DTy_wrt_DTy_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma free_dskvars_DSch_close_DSch_wrt_DTy_rec_mutual :
(forall DSch1 dskA1 n1,
  free_dskvars_DSch (close_DSch_wrt_DTy_rec n1 dskA1 DSch1) [=] remove dskA1 (free_dskvars_DSch DSch1)).
Proof.
apply_mutual_ind DSch_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma free_dskvars_DSch_close_DSch_wrt_DTy_rec :
forall DSch1 dskA1 n1,
  free_dskvars_DSch (close_DSch_wrt_DTy_rec n1 dskA1 DSch1) [=] remove dskA1 (free_dskvars_DSch DSch1).
Proof.
pose proof free_dskvars_DSch_close_DSch_wrt_DTy_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_dskvars_DSch_close_DSch_wrt_DTy_rec : lngen.
#[export] Hint Rewrite free_dskvars_DSch_close_DSch_wrt_DTy_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma free_skvars_Ty_close_Ty_wrt_Ty_rec_mutual :
(forall Ty1 skA1 n1,
  free_skvars_Ty (close_Ty_wrt_Ty_rec n1 skA1 Ty1) [=] remove skA1 (free_skvars_Ty Ty1)).
Proof.
apply_mutual_ind Ty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma free_skvars_Ty_close_Ty_wrt_Ty_rec :
forall Ty1 skA1 n1,
  free_skvars_Ty (close_Ty_wrt_Ty_rec n1 skA1 Ty1) [=] remove skA1 (free_skvars_Ty Ty1).
Proof.
pose proof free_skvars_Ty_close_Ty_wrt_Ty_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_skvars_Ty_close_Ty_wrt_Ty_rec : lngen.
#[export] Hint Rewrite free_skvars_Ty_close_Ty_wrt_Ty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma free_skvars_Sch_close_Sch_wrt_Ty_rec_mutual :
(forall Sch1 skA1 n1,
  free_skvars_Sch (close_Sch_wrt_Ty_rec n1 skA1 Sch1) [=] remove skA1 (free_skvars_Sch Sch1)).
Proof.
apply_mutual_ind Sch_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma free_skvars_Sch_close_Sch_wrt_Ty_rec :
forall Sch1 skA1 n1,
  free_skvars_Sch (close_Sch_wrt_Ty_rec n1 skA1 Sch1) [=] remove skA1 (free_skvars_Sch Sch1).
Proof.
pose proof free_skvars_Sch_close_Sch_wrt_Ty_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_skvars_Sch_close_Sch_wrt_Ty_rec : lngen.
#[export] Hint Rewrite free_skvars_Sch_close_Sch_wrt_Ty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma free_xs_e_close_e_wrt_e_rec_mutual :
(forall e1 x1 n1,
  free_xs_e (close_e_wrt_e_rec n1 x1 e1) [=] remove x1 (free_xs_e e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma free_xs_e_close_e_wrt_e_rec :
forall e1 x1 n1,
  free_xs_e (close_e_wrt_e_rec n1 x1 e1) [=] remove x1 (free_xs_e e1).
Proof.
pose proof free_xs_e_close_e_wrt_e_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_xs_e_close_e_wrt_e_rec : lngen.
#[export] Hint Rewrite free_xs_e_close_e_wrt_e_rec using solve [auto] : lngen.

(* end hide *)

Lemma free_dskvars_DTy_close_DTy_wrt_DTy :
forall DTy1 dskA1,
  free_dskvars_DTy (close_DTy_wrt_DTy dskA1 DTy1) [=] remove dskA1 (free_dskvars_DTy DTy1).
Proof.
unfold close_DTy_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve free_dskvars_DTy_close_DTy_wrt_DTy : lngen.
#[export] Hint Rewrite free_dskvars_DTy_close_DTy_wrt_DTy using solve [auto] : lngen.

Lemma free_dskvars_DSch_close_DSch_wrt_DTy :
forall DSch1 dskA1,
  free_dskvars_DSch (close_DSch_wrt_DTy dskA1 DSch1) [=] remove dskA1 (free_dskvars_DSch DSch1).
Proof.
unfold close_DSch_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve free_dskvars_DSch_close_DSch_wrt_DTy : lngen.
#[export] Hint Rewrite free_dskvars_DSch_close_DSch_wrt_DTy using solve [auto] : lngen.

Lemma free_skvars_Ty_close_Ty_wrt_Ty :
forall Ty1 skA1,
  free_skvars_Ty (close_Ty_wrt_Ty skA1 Ty1) [=] remove skA1 (free_skvars_Ty Ty1).
Proof.
unfold close_Ty_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve free_skvars_Ty_close_Ty_wrt_Ty : lngen.
#[export] Hint Rewrite free_skvars_Ty_close_Ty_wrt_Ty using solve [auto] : lngen.

Lemma free_skvars_Sch_close_Sch_wrt_Ty :
forall Sch1 skA1,
  free_skvars_Sch (close_Sch_wrt_Ty skA1 Sch1) [=] remove skA1 (free_skvars_Sch Sch1).
Proof.
unfold close_Sch_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve free_skvars_Sch_close_Sch_wrt_Ty : lngen.
#[export] Hint Rewrite free_skvars_Sch_close_Sch_wrt_Ty using solve [auto] : lngen.

Lemma free_xs_e_close_e_wrt_e :
forall e1 x1,
  free_xs_e (close_e_wrt_e x1 e1) [=] remove x1 (free_xs_e e1).
Proof.
unfold close_e_wrt_e; default_simp.
Qed.

#[export] Hint Resolve free_xs_e_close_e_wrt_e : lngen.
#[export] Hint Rewrite free_xs_e_close_e_wrt_e using solve [auto] : lngen.

(* begin hide *)

Lemma free_dskvars_DTy_open_DTy_wrt_DTy_rec_lower_mutual :
(forall DTy1 DTy2 n1,
  free_dskvars_DTy DTy1 [<=] free_dskvars_DTy (open_DTy_wrt_DTy_rec n1 DTy2 DTy1)).
Proof.
apply_mutual_ind DTy_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma free_dskvars_DTy_open_DTy_wrt_DTy_rec_lower :
forall DTy1 DTy2 n1,
  free_dskvars_DTy DTy1 [<=] free_dskvars_DTy (open_DTy_wrt_DTy_rec n1 DTy2 DTy1).
Proof.
pose proof free_dskvars_DTy_open_DTy_wrt_DTy_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_dskvars_DTy_open_DTy_wrt_DTy_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma free_dskvars_DSch_open_DSch_wrt_DTy_rec_lower_mutual :
(forall DSch1 DTy1 n1,
  free_dskvars_DSch DSch1 [<=] free_dskvars_DSch (open_DSch_wrt_DTy_rec n1 DTy1 DSch1)).
Proof.
apply_mutual_ind DSch_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma free_dskvars_DSch_open_DSch_wrt_DTy_rec_lower :
forall DSch1 DTy1 n1,
  free_dskvars_DSch DSch1 [<=] free_dskvars_DSch (open_DSch_wrt_DTy_rec n1 DTy1 DSch1).
Proof.
pose proof free_dskvars_DSch_open_DSch_wrt_DTy_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_dskvars_DSch_open_DSch_wrt_DTy_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma free_skvars_Ty_open_Ty_wrt_Ty_rec_lower_mutual :
(forall Ty1 Ty2 n1,
  free_skvars_Ty Ty1 [<=] free_skvars_Ty (open_Ty_wrt_Ty_rec n1 Ty2 Ty1)).
Proof.
apply_mutual_ind Ty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma free_skvars_Ty_open_Ty_wrt_Ty_rec_lower :
forall Ty1 Ty2 n1,
  free_skvars_Ty Ty1 [<=] free_skvars_Ty (open_Ty_wrt_Ty_rec n1 Ty2 Ty1).
Proof.
pose proof free_skvars_Ty_open_Ty_wrt_Ty_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_skvars_Ty_open_Ty_wrt_Ty_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma free_skvars_Sch_open_Sch_wrt_Ty_rec_lower_mutual :
(forall Sch1 Ty1 n1,
  free_skvars_Sch Sch1 [<=] free_skvars_Sch (open_Sch_wrt_Ty_rec n1 Ty1 Sch1)).
Proof.
apply_mutual_ind Sch_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma free_skvars_Sch_open_Sch_wrt_Ty_rec_lower :
forall Sch1 Ty1 n1,
  free_skvars_Sch Sch1 [<=] free_skvars_Sch (open_Sch_wrt_Ty_rec n1 Ty1 Sch1).
Proof.
pose proof free_skvars_Sch_open_Sch_wrt_Ty_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_skvars_Sch_open_Sch_wrt_Ty_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma free_xs_e_open_e_wrt_e_rec_lower_mutual :
(forall e1 e2 n1,
  free_xs_e e1 [<=] free_xs_e (open_e_wrt_e_rec n1 e2 e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma free_xs_e_open_e_wrt_e_rec_lower :
forall e1 e2 n1,
  free_xs_e e1 [<=] free_xs_e (open_e_wrt_e_rec n1 e2 e1).
Proof.
pose proof free_xs_e_open_e_wrt_e_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_xs_e_open_e_wrt_e_rec_lower : lngen.

(* end hide *)

Lemma free_dskvars_DTy_open_DTy_wrt_DTy_lower :
forall DTy1 DTy2,
  free_dskvars_DTy DTy1 [<=] free_dskvars_DTy (open_DTy_wrt_DTy DTy1 DTy2).
Proof.
unfold open_DTy_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve free_dskvars_DTy_open_DTy_wrt_DTy_lower : lngen.

Lemma free_dskvars_DSch_open_DSch_wrt_DTy_lower :
forall DSch1 DTy1,
  free_dskvars_DSch DSch1 [<=] free_dskvars_DSch (open_DSch_wrt_DTy DSch1 DTy1).
Proof.
unfold open_DSch_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve free_dskvars_DSch_open_DSch_wrt_DTy_lower : lngen.

Lemma free_skvars_Ty_open_Ty_wrt_Ty_lower :
forall Ty1 Ty2,
  free_skvars_Ty Ty1 [<=] free_skvars_Ty (open_Ty_wrt_Ty Ty1 Ty2).
Proof.
unfold open_Ty_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve free_skvars_Ty_open_Ty_wrt_Ty_lower : lngen.

Lemma free_skvars_Sch_open_Sch_wrt_Ty_lower :
forall Sch1 Ty1,
  free_skvars_Sch Sch1 [<=] free_skvars_Sch (open_Sch_wrt_Ty Sch1 Ty1).
Proof.
unfold open_Sch_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve free_skvars_Sch_open_Sch_wrt_Ty_lower : lngen.

Lemma free_xs_e_open_e_wrt_e_lower :
forall e1 e2,
  free_xs_e e1 [<=] free_xs_e (open_e_wrt_e e1 e2).
Proof.
unfold open_e_wrt_e; default_simp.
Qed.

#[export] Hint Resolve free_xs_e_open_e_wrt_e_lower : lngen.

(* begin hide *)

Lemma free_dskvars_DTy_open_DTy_wrt_DTy_rec_upper_mutual :
(forall DTy1 DTy2 n1,
  free_dskvars_DTy (open_DTy_wrt_DTy_rec n1 DTy2 DTy1) [<=] free_dskvars_DTy DTy2 `union` free_dskvars_DTy DTy1).
Proof.
apply_mutual_ind DTy_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma free_dskvars_DTy_open_DTy_wrt_DTy_rec_upper :
forall DTy1 DTy2 n1,
  free_dskvars_DTy (open_DTy_wrt_DTy_rec n1 DTy2 DTy1) [<=] free_dskvars_DTy DTy2 `union` free_dskvars_DTy DTy1.
Proof.
pose proof free_dskvars_DTy_open_DTy_wrt_DTy_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_dskvars_DTy_open_DTy_wrt_DTy_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma free_dskvars_DSch_open_DSch_wrt_DTy_rec_upper_mutual :
(forall DSch1 DTy1 n1,
  free_dskvars_DSch (open_DSch_wrt_DTy_rec n1 DTy1 DSch1) [<=] free_dskvars_DTy DTy1 `union` free_dskvars_DSch DSch1).
Proof.
apply_mutual_ind DSch_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma free_dskvars_DSch_open_DSch_wrt_DTy_rec_upper :
forall DSch1 DTy1 n1,
  free_dskvars_DSch (open_DSch_wrt_DTy_rec n1 DTy1 DSch1) [<=] free_dskvars_DTy DTy1 `union` free_dskvars_DSch DSch1.
Proof.
pose proof free_dskvars_DSch_open_DSch_wrt_DTy_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_dskvars_DSch_open_DSch_wrt_DTy_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma free_skvars_Ty_open_Ty_wrt_Ty_rec_upper_mutual :
(forall Ty1 Ty2 n1,
  free_skvars_Ty (open_Ty_wrt_Ty_rec n1 Ty2 Ty1) [<=] free_skvars_Ty Ty2 `union` free_skvars_Ty Ty1).
Proof.
apply_mutual_ind Ty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma free_skvars_Ty_open_Ty_wrt_Ty_rec_upper :
forall Ty1 Ty2 n1,
  free_skvars_Ty (open_Ty_wrt_Ty_rec n1 Ty2 Ty1) [<=] free_skvars_Ty Ty2 `union` free_skvars_Ty Ty1.
Proof.
pose proof free_skvars_Ty_open_Ty_wrt_Ty_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_skvars_Ty_open_Ty_wrt_Ty_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma free_skvars_Sch_open_Sch_wrt_Ty_rec_upper_mutual :
(forall Sch1 Ty1 n1,
  free_skvars_Sch (open_Sch_wrt_Ty_rec n1 Ty1 Sch1) [<=] free_skvars_Ty Ty1 `union` free_skvars_Sch Sch1).
Proof.
apply_mutual_ind Sch_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma free_skvars_Sch_open_Sch_wrt_Ty_rec_upper :
forall Sch1 Ty1 n1,
  free_skvars_Sch (open_Sch_wrt_Ty_rec n1 Ty1 Sch1) [<=] free_skvars_Ty Ty1 `union` free_skvars_Sch Sch1.
Proof.
pose proof free_skvars_Sch_open_Sch_wrt_Ty_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_skvars_Sch_open_Sch_wrt_Ty_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma free_xs_e_open_e_wrt_e_rec_upper_mutual :
(forall e1 e2 n1,
  free_xs_e (open_e_wrt_e_rec n1 e2 e1) [<=] free_xs_e e2 `union` free_xs_e e1).
Proof.
apply_mutual_ind e_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma free_xs_e_open_e_wrt_e_rec_upper :
forall e1 e2 n1,
  free_xs_e (open_e_wrt_e_rec n1 e2 e1) [<=] free_xs_e e2 `union` free_xs_e e1.
Proof.
pose proof free_xs_e_open_e_wrt_e_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_xs_e_open_e_wrt_e_rec_upper : lngen.

(* end hide *)

Lemma free_dskvars_DTy_open_DTy_wrt_DTy_upper :
forall DTy1 DTy2,
  free_dskvars_DTy (open_DTy_wrt_DTy DTy1 DTy2) [<=] free_dskvars_DTy DTy2 `union` free_dskvars_DTy DTy1.
Proof.
unfold open_DTy_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve free_dskvars_DTy_open_DTy_wrt_DTy_upper : lngen.

Lemma free_dskvars_DSch_open_DSch_wrt_DTy_upper :
forall DSch1 DTy1,
  free_dskvars_DSch (open_DSch_wrt_DTy DSch1 DTy1) [<=] free_dskvars_DTy DTy1 `union` free_dskvars_DSch DSch1.
Proof.
unfold open_DSch_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve free_dskvars_DSch_open_DSch_wrt_DTy_upper : lngen.

Lemma free_skvars_Ty_open_Ty_wrt_Ty_upper :
forall Ty1 Ty2,
  free_skvars_Ty (open_Ty_wrt_Ty Ty1 Ty2) [<=] free_skvars_Ty Ty2 `union` free_skvars_Ty Ty1.
Proof.
unfold open_Ty_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve free_skvars_Ty_open_Ty_wrt_Ty_upper : lngen.

Lemma free_skvars_Sch_open_Sch_wrt_Ty_upper :
forall Sch1 Ty1,
  free_skvars_Sch (open_Sch_wrt_Ty Sch1 Ty1) [<=] free_skvars_Ty Ty1 `union` free_skvars_Sch Sch1.
Proof.
unfold open_Sch_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve free_skvars_Sch_open_Sch_wrt_Ty_upper : lngen.

Lemma free_xs_e_open_e_wrt_e_upper :
forall e1 e2,
  free_xs_e (open_e_wrt_e e1 e2) [<=] free_xs_e e2 `union` free_xs_e e1.
Proof.
unfold open_e_wrt_e; default_simp.
Qed.

#[export] Hint Resolve free_xs_e_open_e_wrt_e_upper : lngen.

(* begin hide *)

Lemma free_dskvars_DTy_subst_dskvar_DTy_fresh_mutual :
(forall DTy1 DTy2 dskA1,
  dskA1 `notin` free_dskvars_DTy DTy1 ->
  free_dskvars_DTy (subst_dskvar_DTy DTy2 dskA1 DTy1) [=] free_dskvars_DTy DTy1).
Proof.
apply_mutual_ind DTy_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma free_dskvars_DTy_subst_dskvar_DTy_fresh :
forall DTy1 DTy2 dskA1,
  dskA1 `notin` free_dskvars_DTy DTy1 ->
  free_dskvars_DTy (subst_dskvar_DTy DTy2 dskA1 DTy1) [=] free_dskvars_DTy DTy1.
Proof.
pose proof free_dskvars_DTy_subst_dskvar_DTy_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_dskvars_DTy_subst_dskvar_DTy_fresh : lngen.
#[export] Hint Rewrite free_dskvars_DTy_subst_dskvar_DTy_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma free_dskvars_DSch_subst_dskvar_DSch_fresh_mutual :
(forall DSch1 DTy1 dskA1,
  dskA1 `notin` free_dskvars_DSch DSch1 ->
  free_dskvars_DSch (subst_dskvar_DSch DTy1 dskA1 DSch1) [=] free_dskvars_DSch DSch1).
Proof.
apply_mutual_ind DSch_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma free_dskvars_DSch_subst_dskvar_DSch_fresh :
forall DSch1 DTy1 dskA1,
  dskA1 `notin` free_dskvars_DSch DSch1 ->
  free_dskvars_DSch (subst_dskvar_DSch DTy1 dskA1 DSch1) [=] free_dskvars_DSch DSch1.
Proof.
pose proof free_dskvars_DSch_subst_dskvar_DSch_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_dskvars_DSch_subst_dskvar_DSch_fresh : lngen.
#[export] Hint Rewrite free_dskvars_DSch_subst_dskvar_DSch_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma free_skvars_Ty_subst_skvar_Ty_fresh_mutual :
(forall Ty1 Ty2 skA1,
  skA1 `notin` free_skvars_Ty Ty1 ->
  free_skvars_Ty (subst_skvar_Ty Ty2 skA1 Ty1) [=] free_skvars_Ty Ty1).
Proof.
apply_mutual_ind Ty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma free_skvars_Ty_subst_skvar_Ty_fresh :
forall Ty1 Ty2 skA1,
  skA1 `notin` free_skvars_Ty Ty1 ->
  free_skvars_Ty (subst_skvar_Ty Ty2 skA1 Ty1) [=] free_skvars_Ty Ty1.
Proof.
pose proof free_skvars_Ty_subst_skvar_Ty_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_skvars_Ty_subst_skvar_Ty_fresh : lngen.
#[export] Hint Rewrite free_skvars_Ty_subst_skvar_Ty_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma free_skvars_Sch_subst_skvar_Sch_fresh_mutual :
(forall Sch1 Ty1 skA1,
  skA1 `notin` free_skvars_Sch Sch1 ->
  free_skvars_Sch (subst_skvar_Sch Ty1 skA1 Sch1) [=] free_skvars_Sch Sch1).
Proof.
apply_mutual_ind Sch_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma free_skvars_Sch_subst_skvar_Sch_fresh :
forall Sch1 Ty1 skA1,
  skA1 `notin` free_skvars_Sch Sch1 ->
  free_skvars_Sch (subst_skvar_Sch Ty1 skA1 Sch1) [=] free_skvars_Sch Sch1.
Proof.
pose proof free_skvars_Sch_subst_skvar_Sch_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_skvars_Sch_subst_skvar_Sch_fresh : lngen.
#[export] Hint Rewrite free_skvars_Sch_subst_skvar_Sch_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma free_xs_e_subst_tm_e_fresh_mutual :
(forall e1 e2 x1,
  x1 `notin` free_xs_e e1 ->
  free_xs_e (subst_tm_e e2 x1 e1) [=] free_xs_e e1).
Proof.
apply_mutual_ind e_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma free_xs_e_subst_tm_e_fresh :
forall e1 e2 x1,
  x1 `notin` free_xs_e e1 ->
  free_xs_e (subst_tm_e e2 x1 e1) [=] free_xs_e e1.
Proof.
pose proof free_xs_e_subst_tm_e_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_xs_e_subst_tm_e_fresh : lngen.
#[export] Hint Rewrite free_xs_e_subst_tm_e_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma free_dskvars_DTy_subst_dskvar_DTy_lower_mutual :
(forall DTy1 DTy2 dskA1,
  remove dskA1 (free_dskvars_DTy DTy1) [<=] free_dskvars_DTy (subst_dskvar_DTy DTy2 dskA1 DTy1)).
Proof.
apply_mutual_ind DTy_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma free_dskvars_DTy_subst_dskvar_DTy_lower :
forall DTy1 DTy2 dskA1,
  remove dskA1 (free_dskvars_DTy DTy1) [<=] free_dskvars_DTy (subst_dskvar_DTy DTy2 dskA1 DTy1).
Proof.
pose proof free_dskvars_DTy_subst_dskvar_DTy_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_dskvars_DTy_subst_dskvar_DTy_lower : lngen.

(* begin hide *)

Lemma free_dskvars_DSch_subst_dskvar_DSch_lower_mutual :
(forall DSch1 DTy1 dskA1,
  remove dskA1 (free_dskvars_DSch DSch1) [<=] free_dskvars_DSch (subst_dskvar_DSch DTy1 dskA1 DSch1)).
Proof.
apply_mutual_ind DSch_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma free_dskvars_DSch_subst_dskvar_DSch_lower :
forall DSch1 DTy1 dskA1,
  remove dskA1 (free_dskvars_DSch DSch1) [<=] free_dskvars_DSch (subst_dskvar_DSch DTy1 dskA1 DSch1).
Proof.
pose proof free_dskvars_DSch_subst_dskvar_DSch_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_dskvars_DSch_subst_dskvar_DSch_lower : lngen.

(* begin hide *)

Lemma free_skvars_Ty_subst_skvar_Ty_lower_mutual :
(forall Ty1 Ty2 skA1,
  remove skA1 (free_skvars_Ty Ty1) [<=] free_skvars_Ty (subst_skvar_Ty Ty2 skA1 Ty1)).
Proof.
apply_mutual_ind Ty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma free_skvars_Ty_subst_skvar_Ty_lower :
forall Ty1 Ty2 skA1,
  remove skA1 (free_skvars_Ty Ty1) [<=] free_skvars_Ty (subst_skvar_Ty Ty2 skA1 Ty1).
Proof.
pose proof free_skvars_Ty_subst_skvar_Ty_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_skvars_Ty_subst_skvar_Ty_lower : lngen.

(* begin hide *)

Lemma free_skvars_Sch_subst_skvar_Sch_lower_mutual :
(forall Sch1 Ty1 skA1,
  remove skA1 (free_skvars_Sch Sch1) [<=] free_skvars_Sch (subst_skvar_Sch Ty1 skA1 Sch1)).
Proof.
apply_mutual_ind Sch_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma free_skvars_Sch_subst_skvar_Sch_lower :
forall Sch1 Ty1 skA1,
  remove skA1 (free_skvars_Sch Sch1) [<=] free_skvars_Sch (subst_skvar_Sch Ty1 skA1 Sch1).
Proof.
pose proof free_skvars_Sch_subst_skvar_Sch_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_skvars_Sch_subst_skvar_Sch_lower : lngen.

(* begin hide *)

Lemma free_xs_e_subst_tm_e_lower_mutual :
(forall e1 e2 x1,
  remove x1 (free_xs_e e1) [<=] free_xs_e (subst_tm_e e2 x1 e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma free_xs_e_subst_tm_e_lower :
forall e1 e2 x1,
  remove x1 (free_xs_e e1) [<=] free_xs_e (subst_tm_e e2 x1 e1).
Proof.
pose proof free_xs_e_subst_tm_e_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_xs_e_subst_tm_e_lower : lngen.

(* begin hide *)

Lemma free_dskvars_DTy_subst_dskvar_DTy_notin_mutual :
(forall DTy1 DTy2 dskA1 dskA2,
  dskA2 `notin` free_dskvars_DTy DTy1 ->
  dskA2 `notin` free_dskvars_DTy DTy2 ->
  dskA2 `notin` free_dskvars_DTy (subst_dskvar_DTy DTy2 dskA1 DTy1)).
Proof.
apply_mutual_ind DTy_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma free_dskvars_DTy_subst_dskvar_DTy_notin :
forall DTy1 DTy2 dskA1 dskA2,
  dskA2 `notin` free_dskvars_DTy DTy1 ->
  dskA2 `notin` free_dskvars_DTy DTy2 ->
  dskA2 `notin` free_dskvars_DTy (subst_dskvar_DTy DTy2 dskA1 DTy1).
Proof.
pose proof free_dskvars_DTy_subst_dskvar_DTy_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_dskvars_DTy_subst_dskvar_DTy_notin : lngen.

(* begin hide *)

Lemma free_dskvars_DSch_subst_dskvar_DSch_notin_mutual :
(forall DSch1 DTy1 dskA1 dskA2,
  dskA2 `notin` free_dskvars_DSch DSch1 ->
  dskA2 `notin` free_dskvars_DTy DTy1 ->
  dskA2 `notin` free_dskvars_DSch (subst_dskvar_DSch DTy1 dskA1 DSch1)).
Proof.
apply_mutual_ind DSch_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma free_dskvars_DSch_subst_dskvar_DSch_notin :
forall DSch1 DTy1 dskA1 dskA2,
  dskA2 `notin` free_dskvars_DSch DSch1 ->
  dskA2 `notin` free_dskvars_DTy DTy1 ->
  dskA2 `notin` free_dskvars_DSch (subst_dskvar_DSch DTy1 dskA1 DSch1).
Proof.
pose proof free_dskvars_DSch_subst_dskvar_DSch_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_dskvars_DSch_subst_dskvar_DSch_notin : lngen.

(* begin hide *)

Lemma free_skvars_Ty_subst_skvar_Ty_notin_mutual :
(forall Ty1 Ty2 skA1 skA2,
  skA2 `notin` free_skvars_Ty Ty1 ->
  skA2 `notin` free_skvars_Ty Ty2 ->
  skA2 `notin` free_skvars_Ty (subst_skvar_Ty Ty2 skA1 Ty1)).
Proof.
apply_mutual_ind Ty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma free_skvars_Ty_subst_skvar_Ty_notin :
forall Ty1 Ty2 skA1 skA2,
  skA2 `notin` free_skvars_Ty Ty1 ->
  skA2 `notin` free_skvars_Ty Ty2 ->
  skA2 `notin` free_skvars_Ty (subst_skvar_Ty Ty2 skA1 Ty1).
Proof.
pose proof free_skvars_Ty_subst_skvar_Ty_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_skvars_Ty_subst_skvar_Ty_notin : lngen.

(* begin hide *)

Lemma free_skvars_Sch_subst_skvar_Sch_notin_mutual :
(forall Sch1 Ty1 skA1 skA2,
  skA2 `notin` free_skvars_Sch Sch1 ->
  skA2 `notin` free_skvars_Ty Ty1 ->
  skA2 `notin` free_skvars_Sch (subst_skvar_Sch Ty1 skA1 Sch1)).
Proof.
apply_mutual_ind Sch_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma free_skvars_Sch_subst_skvar_Sch_notin :
forall Sch1 Ty1 skA1 skA2,
  skA2 `notin` free_skvars_Sch Sch1 ->
  skA2 `notin` free_skvars_Ty Ty1 ->
  skA2 `notin` free_skvars_Sch (subst_skvar_Sch Ty1 skA1 Sch1).
Proof.
pose proof free_skvars_Sch_subst_skvar_Sch_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_skvars_Sch_subst_skvar_Sch_notin : lngen.

(* begin hide *)

Lemma free_xs_e_subst_tm_e_notin_mutual :
(forall e1 e2 x1 x2,
  x2 `notin` free_xs_e e1 ->
  x2 `notin` free_xs_e e2 ->
  x2 `notin` free_xs_e (subst_tm_e e2 x1 e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma free_xs_e_subst_tm_e_notin :
forall e1 e2 x1 x2,
  x2 `notin` free_xs_e e1 ->
  x2 `notin` free_xs_e e2 ->
  x2 `notin` free_xs_e (subst_tm_e e2 x1 e1).
Proof.
pose proof free_xs_e_subst_tm_e_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_xs_e_subst_tm_e_notin : lngen.

(* begin hide *)

Lemma free_dskvars_DTy_subst_dskvar_DTy_upper_mutual :
(forall DTy1 DTy2 dskA1,
  free_dskvars_DTy (subst_dskvar_DTy DTy2 dskA1 DTy1) [<=] free_dskvars_DTy DTy2 `union` remove dskA1 (free_dskvars_DTy DTy1)).
Proof.
apply_mutual_ind DTy_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma free_dskvars_DTy_subst_dskvar_DTy_upper :
forall DTy1 DTy2 dskA1,
  free_dskvars_DTy (subst_dskvar_DTy DTy2 dskA1 DTy1) [<=] free_dskvars_DTy DTy2 `union` remove dskA1 (free_dskvars_DTy DTy1).
Proof.
pose proof free_dskvars_DTy_subst_dskvar_DTy_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_dskvars_DTy_subst_dskvar_DTy_upper : lngen.

(* begin hide *)

Lemma free_dskvars_DSch_subst_dskvar_DSch_upper_mutual :
(forall DSch1 DTy1 dskA1,
  free_dskvars_DSch (subst_dskvar_DSch DTy1 dskA1 DSch1) [<=] free_dskvars_DTy DTy1 `union` remove dskA1 (free_dskvars_DSch DSch1)).
Proof.
apply_mutual_ind DSch_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma free_dskvars_DSch_subst_dskvar_DSch_upper :
forall DSch1 DTy1 dskA1,
  free_dskvars_DSch (subst_dskvar_DSch DTy1 dskA1 DSch1) [<=] free_dskvars_DTy DTy1 `union` remove dskA1 (free_dskvars_DSch DSch1).
Proof.
pose proof free_dskvars_DSch_subst_dskvar_DSch_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_dskvars_DSch_subst_dskvar_DSch_upper : lngen.

(* begin hide *)

Lemma free_skvars_Ty_subst_skvar_Ty_upper_mutual :
(forall Ty1 Ty2 skA1,
  free_skvars_Ty (subst_skvar_Ty Ty2 skA1 Ty1) [<=] free_skvars_Ty Ty2 `union` remove skA1 (free_skvars_Ty Ty1)).
Proof.
apply_mutual_ind Ty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma free_skvars_Ty_subst_skvar_Ty_upper :
forall Ty1 Ty2 skA1,
  free_skvars_Ty (subst_skvar_Ty Ty2 skA1 Ty1) [<=] free_skvars_Ty Ty2 `union` remove skA1 (free_skvars_Ty Ty1).
Proof.
pose proof free_skvars_Ty_subst_skvar_Ty_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_skvars_Ty_subst_skvar_Ty_upper : lngen.

(* begin hide *)

Lemma free_skvars_Sch_subst_skvar_Sch_upper_mutual :
(forall Sch1 Ty1 skA1,
  free_skvars_Sch (subst_skvar_Sch Ty1 skA1 Sch1) [<=] free_skvars_Ty Ty1 `union` remove skA1 (free_skvars_Sch Sch1)).
Proof.
apply_mutual_ind Sch_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma free_skvars_Sch_subst_skvar_Sch_upper :
forall Sch1 Ty1 skA1,
  free_skvars_Sch (subst_skvar_Sch Ty1 skA1 Sch1) [<=] free_skvars_Ty Ty1 `union` remove skA1 (free_skvars_Sch Sch1).
Proof.
pose proof free_skvars_Sch_subst_skvar_Sch_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_skvars_Sch_subst_skvar_Sch_upper : lngen.

(* begin hide *)

Lemma free_xs_e_subst_tm_e_upper_mutual :
(forall e1 e2 x1,
  free_xs_e (subst_tm_e e2 x1 e1) [<=] free_xs_e e2 `union` remove x1 (free_xs_e e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma free_xs_e_subst_tm_e_upper :
forall e1 e2 x1,
  free_xs_e (subst_tm_e e2 x1 e1) [<=] free_xs_e e2 `union` remove x1 (free_xs_e e1).
Proof.
pose proof free_xs_e_subst_tm_e_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve free_xs_e_subst_tm_e_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_dskvar_DTy_close_DTy_wrt_DTy_rec_mutual :
(forall DTy2 DTy1 dskA1 dskA2 n1,
  degree_DTy_wrt_DTy n1 DTy1 ->
  dskA1 <> dskA2 ->
  dskA2 `notin` free_dskvars_DTy DTy1 ->
  subst_dskvar_DTy DTy1 dskA1 (close_DTy_wrt_DTy_rec n1 dskA2 DTy2) = close_DTy_wrt_DTy_rec n1 dskA2 (subst_dskvar_DTy DTy1 dskA1 DTy2)).
Proof.
apply_mutual_ind DTy_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dskvar_DTy_close_DTy_wrt_DTy_rec :
forall DTy2 DTy1 dskA1 dskA2 n1,
  degree_DTy_wrt_DTy n1 DTy1 ->
  dskA1 <> dskA2 ->
  dskA2 `notin` free_dskvars_DTy DTy1 ->
  subst_dskvar_DTy DTy1 dskA1 (close_DTy_wrt_DTy_rec n1 dskA2 DTy2) = close_DTy_wrt_DTy_rec n1 dskA2 (subst_dskvar_DTy DTy1 dskA1 DTy2).
Proof.
pose proof subst_dskvar_DTy_close_DTy_wrt_DTy_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_dskvar_DTy_close_DTy_wrt_DTy_rec : lngen.

(* begin hide *)

Lemma subst_dskvar_DSch_close_DSch_wrt_DTy_rec_mutual :
(forall DSch1 DTy1 dskA1 dskA2 n1,
  degree_DTy_wrt_DTy n1 DTy1 ->
  dskA1 <> dskA2 ->
  dskA2 `notin` free_dskvars_DTy DTy1 ->
  subst_dskvar_DSch DTy1 dskA1 (close_DSch_wrt_DTy_rec n1 dskA2 DSch1) = close_DSch_wrt_DTy_rec n1 dskA2 (subst_dskvar_DSch DTy1 dskA1 DSch1)).
Proof.
apply_mutual_ind DSch_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dskvar_DSch_close_DSch_wrt_DTy_rec :
forall DSch1 DTy1 dskA1 dskA2 n1,
  degree_DTy_wrt_DTy n1 DTy1 ->
  dskA1 <> dskA2 ->
  dskA2 `notin` free_dskvars_DTy DTy1 ->
  subst_dskvar_DSch DTy1 dskA1 (close_DSch_wrt_DTy_rec n1 dskA2 DSch1) = close_DSch_wrt_DTy_rec n1 dskA2 (subst_dskvar_DSch DTy1 dskA1 DSch1).
Proof.
pose proof subst_dskvar_DSch_close_DSch_wrt_DTy_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_dskvar_DSch_close_DSch_wrt_DTy_rec : lngen.

(* begin hide *)

Lemma subst_skvar_Ty_close_Ty_wrt_Ty_rec_mutual :
(forall Ty2 Ty1 skA1 skA2 n1,
  degree_Ty_wrt_Ty n1 Ty1 ->
  skA1 <> skA2 ->
  skA2 `notin` free_skvars_Ty Ty1 ->
  subst_skvar_Ty Ty1 skA1 (close_Ty_wrt_Ty_rec n1 skA2 Ty2) = close_Ty_wrt_Ty_rec n1 skA2 (subst_skvar_Ty Ty1 skA1 Ty2)).
Proof.
apply_mutual_ind Ty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Ty_close_Ty_wrt_Ty_rec :
forall Ty2 Ty1 skA1 skA2 n1,
  degree_Ty_wrt_Ty n1 Ty1 ->
  skA1 <> skA2 ->
  skA2 `notin` free_skvars_Ty Ty1 ->
  subst_skvar_Ty Ty1 skA1 (close_Ty_wrt_Ty_rec n1 skA2 Ty2) = close_Ty_wrt_Ty_rec n1 skA2 (subst_skvar_Ty Ty1 skA1 Ty2).
Proof.
pose proof subst_skvar_Ty_close_Ty_wrt_Ty_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Ty_close_Ty_wrt_Ty_rec : lngen.

(* begin hide *)

Lemma subst_skvar_Sch_close_Sch_wrt_Ty_rec_mutual :
(forall Sch1 Ty1 skA1 skA2 n1,
  degree_Ty_wrt_Ty n1 Ty1 ->
  skA1 <> skA2 ->
  skA2 `notin` free_skvars_Ty Ty1 ->
  subst_skvar_Sch Ty1 skA1 (close_Sch_wrt_Ty_rec n1 skA2 Sch1) = close_Sch_wrt_Ty_rec n1 skA2 (subst_skvar_Sch Ty1 skA1 Sch1)).
Proof.
apply_mutual_ind Sch_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Sch_close_Sch_wrt_Ty_rec :
forall Sch1 Ty1 skA1 skA2 n1,
  degree_Ty_wrt_Ty n1 Ty1 ->
  skA1 <> skA2 ->
  skA2 `notin` free_skvars_Ty Ty1 ->
  subst_skvar_Sch Ty1 skA1 (close_Sch_wrt_Ty_rec n1 skA2 Sch1) = close_Sch_wrt_Ty_rec n1 skA2 (subst_skvar_Sch Ty1 skA1 Sch1).
Proof.
pose proof subst_skvar_Sch_close_Sch_wrt_Ty_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Sch_close_Sch_wrt_Ty_rec : lngen.

(* begin hide *)

Lemma subst_tm_e_close_e_wrt_e_rec_mutual :
(forall e2 e1 x1 x2 n1,
  degree_e_wrt_e n1 e1 ->
  x1 <> x2 ->
  x2 `notin` free_xs_e e1 ->
  subst_tm_e e1 x1 (close_e_wrt_e_rec n1 x2 e2) = close_e_wrt_e_rec n1 x2 (subst_tm_e e1 x1 e2)).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_e_close_e_wrt_e_rec :
forall e2 e1 x1 x2 n1,
  degree_e_wrt_e n1 e1 ->
  x1 <> x2 ->
  x2 `notin` free_xs_e e1 ->
  subst_tm_e e1 x1 (close_e_wrt_e_rec n1 x2 e2) = close_e_wrt_e_rec n1 x2 (subst_tm_e e1 x1 e2).
Proof.
pose proof subst_tm_e_close_e_wrt_e_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_e_close_e_wrt_e_rec : lngen.

Lemma subst_dskvar_DTy_close_DTy_wrt_DTy :
forall DTy2 DTy1 dskA1 dskA2,
  lc_DTy DTy1 ->  dskA1 <> dskA2 ->
  dskA2 `notin` free_dskvars_DTy DTy1 ->
  subst_dskvar_DTy DTy1 dskA1 (close_DTy_wrt_DTy dskA2 DTy2) = close_DTy_wrt_DTy dskA2 (subst_dskvar_DTy DTy1 dskA1 DTy2).
Proof.
unfold close_DTy_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve subst_dskvar_DTy_close_DTy_wrt_DTy : lngen.

Lemma subst_dskvar_DSch_close_DSch_wrt_DTy :
forall DSch1 DTy1 dskA1 dskA2,
  lc_DTy DTy1 ->  dskA1 <> dskA2 ->
  dskA2 `notin` free_dskvars_DTy DTy1 ->
  subst_dskvar_DSch DTy1 dskA1 (close_DSch_wrt_DTy dskA2 DSch1) = close_DSch_wrt_DTy dskA2 (subst_dskvar_DSch DTy1 dskA1 DSch1).
Proof.
unfold close_DSch_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve subst_dskvar_DSch_close_DSch_wrt_DTy : lngen.

Lemma subst_skvar_Ty_close_Ty_wrt_Ty :
forall Ty2 Ty1 skA1 skA2,
  lc_Ty Ty1 ->  skA1 <> skA2 ->
  skA2 `notin` free_skvars_Ty Ty1 ->
  subst_skvar_Ty Ty1 skA1 (close_Ty_wrt_Ty skA2 Ty2) = close_Ty_wrt_Ty skA2 (subst_skvar_Ty Ty1 skA1 Ty2).
Proof.
unfold close_Ty_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Ty_close_Ty_wrt_Ty : lngen.

Lemma subst_skvar_Sch_close_Sch_wrt_Ty :
forall Sch1 Ty1 skA1 skA2,
  lc_Ty Ty1 ->  skA1 <> skA2 ->
  skA2 `notin` free_skvars_Ty Ty1 ->
  subst_skvar_Sch Ty1 skA1 (close_Sch_wrt_Ty skA2 Sch1) = close_Sch_wrt_Ty skA2 (subst_skvar_Sch Ty1 skA1 Sch1).
Proof.
unfold close_Sch_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Sch_close_Sch_wrt_Ty : lngen.

Lemma subst_tm_e_close_e_wrt_e :
forall e2 e1 x1 x2,
  lc_e e1 ->  x1 <> x2 ->
  x2 `notin` free_xs_e e1 ->
  subst_tm_e e1 x1 (close_e_wrt_e x2 e2) = close_e_wrt_e x2 (subst_tm_e e1 x1 e2).
Proof.
unfold close_e_wrt_e; default_simp.
Qed.

#[export] Hint Resolve subst_tm_e_close_e_wrt_e : lngen.

(* begin hide *)

Lemma subst_dskvar_DTy_degree_DTy_wrt_DTy_mutual :
(forall DTy1 DTy2 dskA1 n1,
  degree_DTy_wrt_DTy n1 DTy1 ->
  degree_DTy_wrt_DTy n1 DTy2 ->
  degree_DTy_wrt_DTy n1 (subst_dskvar_DTy DTy2 dskA1 DTy1)).
Proof.
apply_mutual_ind DTy_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dskvar_DTy_degree_DTy_wrt_DTy :
forall DTy1 DTy2 dskA1 n1,
  degree_DTy_wrt_DTy n1 DTy1 ->
  degree_DTy_wrt_DTy n1 DTy2 ->
  degree_DTy_wrt_DTy n1 (subst_dskvar_DTy DTy2 dskA1 DTy1).
Proof.
pose proof subst_dskvar_DTy_degree_DTy_wrt_DTy_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_dskvar_DTy_degree_DTy_wrt_DTy : lngen.

(* begin hide *)

Lemma subst_dskvar_DSch_degree_DSch_wrt_DTy_mutual :
(forall DSch1 DTy1 dskA1 n1,
  degree_DSch_wrt_DTy n1 DSch1 ->
  degree_DTy_wrt_DTy n1 DTy1 ->
  degree_DSch_wrt_DTy n1 (subst_dskvar_DSch DTy1 dskA1 DSch1)).
Proof.
apply_mutual_ind DSch_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dskvar_DSch_degree_DSch_wrt_DTy :
forall DSch1 DTy1 dskA1 n1,
  degree_DSch_wrt_DTy n1 DSch1 ->
  degree_DTy_wrt_DTy n1 DTy1 ->
  degree_DSch_wrt_DTy n1 (subst_dskvar_DSch DTy1 dskA1 DSch1).
Proof.
pose proof subst_dskvar_DSch_degree_DSch_wrt_DTy_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_dskvar_DSch_degree_DSch_wrt_DTy : lngen.

(* begin hide *)

Lemma subst_skvar_Ty_degree_Ty_wrt_Ty_mutual :
(forall Ty1 Ty2 skA1 n1,
  degree_Ty_wrt_Ty n1 Ty1 ->
  degree_Ty_wrt_Ty n1 Ty2 ->
  degree_Ty_wrt_Ty n1 (subst_skvar_Ty Ty2 skA1 Ty1)).
Proof.
apply_mutual_ind Ty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Ty_degree_Ty_wrt_Ty :
forall Ty1 Ty2 skA1 n1,
  degree_Ty_wrt_Ty n1 Ty1 ->
  degree_Ty_wrt_Ty n1 Ty2 ->
  degree_Ty_wrt_Ty n1 (subst_skvar_Ty Ty2 skA1 Ty1).
Proof.
pose proof subst_skvar_Ty_degree_Ty_wrt_Ty_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Ty_degree_Ty_wrt_Ty : lngen.

(* begin hide *)

Lemma subst_skvar_Sch_degree_Sch_wrt_Ty_mutual :
(forall Sch1 Ty1 skA1 n1,
  degree_Sch_wrt_Ty n1 Sch1 ->
  degree_Ty_wrt_Ty n1 Ty1 ->
  degree_Sch_wrt_Ty n1 (subst_skvar_Sch Ty1 skA1 Sch1)).
Proof.
apply_mutual_ind Sch_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Sch_degree_Sch_wrt_Ty :
forall Sch1 Ty1 skA1 n1,
  degree_Sch_wrt_Ty n1 Sch1 ->
  degree_Ty_wrt_Ty n1 Ty1 ->
  degree_Sch_wrt_Ty n1 (subst_skvar_Sch Ty1 skA1 Sch1).
Proof.
pose proof subst_skvar_Sch_degree_Sch_wrt_Ty_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Sch_degree_Sch_wrt_Ty : lngen.

(* begin hide *)

Lemma subst_tm_e_degree_e_wrt_e_mutual :
(forall e1 e2 x1 n1,
  degree_e_wrt_e n1 e1 ->
  degree_e_wrt_e n1 e2 ->
  degree_e_wrt_e n1 (subst_tm_e e2 x1 e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_e_degree_e_wrt_e :
forall e1 e2 x1 n1,
  degree_e_wrt_e n1 e1 ->
  degree_e_wrt_e n1 e2 ->
  degree_e_wrt_e n1 (subst_tm_e e2 x1 e1).
Proof.
pose proof subst_tm_e_degree_e_wrt_e_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_e_degree_e_wrt_e : lngen.

(* begin hide *)

Lemma subst_dskvar_DTy_fresh_eq_mutual :
(forall DTy2 DTy1 dskA1,
  dskA1 `notin` free_dskvars_DTy DTy2 ->
  subst_dskvar_DTy DTy1 dskA1 DTy2 = DTy2).
Proof.
apply_mutual_ind DTy_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dskvar_DTy_fresh_eq :
forall DTy2 DTy1 dskA1,
  dskA1 `notin` free_dskvars_DTy DTy2 ->
  subst_dskvar_DTy DTy1 dskA1 DTy2 = DTy2.
Proof.
pose proof subst_dskvar_DTy_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_dskvar_DTy_fresh_eq : lngen.
#[export] Hint Rewrite subst_dskvar_DTy_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_dskvar_DSch_fresh_eq_mutual :
(forall DSch1 DTy1 dskA1,
  dskA1 `notin` free_dskvars_DSch DSch1 ->
  subst_dskvar_DSch DTy1 dskA1 DSch1 = DSch1).
Proof.
apply_mutual_ind DSch_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dskvar_DSch_fresh_eq :
forall DSch1 DTy1 dskA1,
  dskA1 `notin` free_dskvars_DSch DSch1 ->
  subst_dskvar_DSch DTy1 dskA1 DSch1 = DSch1.
Proof.
pose proof subst_dskvar_DSch_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_dskvar_DSch_fresh_eq : lngen.
#[export] Hint Rewrite subst_dskvar_DSch_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_skvar_Ty_fresh_eq_mutual :
(forall Ty2 Ty1 skA1,
  skA1 `notin` free_skvars_Ty Ty2 ->
  subst_skvar_Ty Ty1 skA1 Ty2 = Ty2).
Proof.
apply_mutual_ind Ty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Ty_fresh_eq :
forall Ty2 Ty1 skA1,
  skA1 `notin` free_skvars_Ty Ty2 ->
  subst_skvar_Ty Ty1 skA1 Ty2 = Ty2.
Proof.
pose proof subst_skvar_Ty_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Ty_fresh_eq : lngen.
#[export] Hint Rewrite subst_skvar_Ty_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_skvar_Sch_fresh_eq_mutual :
(forall Sch1 Ty1 skA1,
  skA1 `notin` free_skvars_Sch Sch1 ->
  subst_skvar_Sch Ty1 skA1 Sch1 = Sch1).
Proof.
apply_mutual_ind Sch_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Sch_fresh_eq :
forall Sch1 Ty1 skA1,
  skA1 `notin` free_skvars_Sch Sch1 ->
  subst_skvar_Sch Ty1 skA1 Sch1 = Sch1.
Proof.
pose proof subst_skvar_Sch_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Sch_fresh_eq : lngen.
#[export] Hint Rewrite subst_skvar_Sch_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tm_e_fresh_eq_mutual :
(forall e2 e1 x1,
  x1 `notin` free_xs_e e2 ->
  subst_tm_e e1 x1 e2 = e2).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_e_fresh_eq :
forall e2 e1 x1,
  x1 `notin` free_xs_e e2 ->
  subst_tm_e e1 x1 e2 = e2.
Proof.
pose proof subst_tm_e_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_e_fresh_eq : lngen.
#[export] Hint Rewrite subst_tm_e_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_dskvar_DTy_fresh_same_mutual :
(forall DTy2 DTy1 dskA1,
  dskA1 `notin` free_dskvars_DTy DTy1 ->
  dskA1 `notin` free_dskvars_DTy (subst_dskvar_DTy DTy1 dskA1 DTy2)).
Proof.
apply_mutual_ind DTy_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dskvar_DTy_fresh_same :
forall DTy2 DTy1 dskA1,
  dskA1 `notin` free_dskvars_DTy DTy1 ->
  dskA1 `notin` free_dskvars_DTy (subst_dskvar_DTy DTy1 dskA1 DTy2).
Proof.
pose proof subst_dskvar_DTy_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_dskvar_DTy_fresh_same : lngen.

(* begin hide *)

Lemma subst_dskvar_DSch_fresh_same_mutual :
(forall DSch1 DTy1 dskA1,
  dskA1 `notin` free_dskvars_DTy DTy1 ->
  dskA1 `notin` free_dskvars_DSch (subst_dskvar_DSch DTy1 dskA1 DSch1)).
Proof.
apply_mutual_ind DSch_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dskvar_DSch_fresh_same :
forall DSch1 DTy1 dskA1,
  dskA1 `notin` free_dskvars_DTy DTy1 ->
  dskA1 `notin` free_dskvars_DSch (subst_dskvar_DSch DTy1 dskA1 DSch1).
Proof.
pose proof subst_dskvar_DSch_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_dskvar_DSch_fresh_same : lngen.

(* begin hide *)

Lemma subst_skvar_Ty_fresh_same_mutual :
(forall Ty2 Ty1 skA1,
  skA1 `notin` free_skvars_Ty Ty1 ->
  skA1 `notin` free_skvars_Ty (subst_skvar_Ty Ty1 skA1 Ty2)).
Proof.
apply_mutual_ind Ty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Ty_fresh_same :
forall Ty2 Ty1 skA1,
  skA1 `notin` free_skvars_Ty Ty1 ->
  skA1 `notin` free_skvars_Ty (subst_skvar_Ty Ty1 skA1 Ty2).
Proof.
pose proof subst_skvar_Ty_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Ty_fresh_same : lngen.

(* begin hide *)

Lemma subst_skvar_Sch_fresh_same_mutual :
(forall Sch1 Ty1 skA1,
  skA1 `notin` free_skvars_Ty Ty1 ->
  skA1 `notin` free_skvars_Sch (subst_skvar_Sch Ty1 skA1 Sch1)).
Proof.
apply_mutual_ind Sch_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Sch_fresh_same :
forall Sch1 Ty1 skA1,
  skA1 `notin` free_skvars_Ty Ty1 ->
  skA1 `notin` free_skvars_Sch (subst_skvar_Sch Ty1 skA1 Sch1).
Proof.
pose proof subst_skvar_Sch_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Sch_fresh_same : lngen.

(* begin hide *)

Lemma subst_tm_e_fresh_same_mutual :
(forall e2 e1 x1,
  x1 `notin` free_xs_e e1 ->
  x1 `notin` free_xs_e (subst_tm_e e1 x1 e2)).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_e_fresh_same :
forall e2 e1 x1,
  x1 `notin` free_xs_e e1 ->
  x1 `notin` free_xs_e (subst_tm_e e1 x1 e2).
Proof.
pose proof subst_tm_e_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_e_fresh_same : lngen.

(* begin hide *)

Lemma subst_dskvar_DTy_fresh_mutual :
(forall DTy2 DTy1 dskA1 dskA2,
  dskA1 `notin` free_dskvars_DTy DTy2 ->
  dskA1 `notin` free_dskvars_DTy DTy1 ->
  dskA1 `notin` free_dskvars_DTy (subst_dskvar_DTy DTy1 dskA2 DTy2)).
Proof.
apply_mutual_ind DTy_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dskvar_DTy_fresh :
forall DTy2 DTy1 dskA1 dskA2,
  dskA1 `notin` free_dskvars_DTy DTy2 ->
  dskA1 `notin` free_dskvars_DTy DTy1 ->
  dskA1 `notin` free_dskvars_DTy (subst_dskvar_DTy DTy1 dskA2 DTy2).
Proof.
pose proof subst_dskvar_DTy_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_dskvar_DTy_fresh : lngen.

(* begin hide *)

Lemma subst_dskvar_DSch_fresh_mutual :
(forall DSch1 DTy1 dskA1 dskA2,
  dskA1 `notin` free_dskvars_DSch DSch1 ->
  dskA1 `notin` free_dskvars_DTy DTy1 ->
  dskA1 `notin` free_dskvars_DSch (subst_dskvar_DSch DTy1 dskA2 DSch1)).
Proof.
apply_mutual_ind DSch_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dskvar_DSch_fresh :
forall DSch1 DTy1 dskA1 dskA2,
  dskA1 `notin` free_dskvars_DSch DSch1 ->
  dskA1 `notin` free_dskvars_DTy DTy1 ->
  dskA1 `notin` free_dskvars_DSch (subst_dskvar_DSch DTy1 dskA2 DSch1).
Proof.
pose proof subst_dskvar_DSch_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_dskvar_DSch_fresh : lngen.

(* begin hide *)

Lemma subst_skvar_Ty_fresh_mutual :
(forall Ty2 Ty1 skA1 skA2,
  skA1 `notin` free_skvars_Ty Ty2 ->
  skA1 `notin` free_skvars_Ty Ty1 ->
  skA1 `notin` free_skvars_Ty (subst_skvar_Ty Ty1 skA2 Ty2)).
Proof.
apply_mutual_ind Ty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Ty_fresh :
forall Ty2 Ty1 skA1 skA2,
  skA1 `notin` free_skvars_Ty Ty2 ->
  skA1 `notin` free_skvars_Ty Ty1 ->
  skA1 `notin` free_skvars_Ty (subst_skvar_Ty Ty1 skA2 Ty2).
Proof.
pose proof subst_skvar_Ty_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Ty_fresh : lngen.

(* begin hide *)

Lemma subst_skvar_Sch_fresh_mutual :
(forall Sch1 Ty1 skA1 skA2,
  skA1 `notin` free_skvars_Sch Sch1 ->
  skA1 `notin` free_skvars_Ty Ty1 ->
  skA1 `notin` free_skvars_Sch (subst_skvar_Sch Ty1 skA2 Sch1)).
Proof.
apply_mutual_ind Sch_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Sch_fresh :
forall Sch1 Ty1 skA1 skA2,
  skA1 `notin` free_skvars_Sch Sch1 ->
  skA1 `notin` free_skvars_Ty Ty1 ->
  skA1 `notin` free_skvars_Sch (subst_skvar_Sch Ty1 skA2 Sch1).
Proof.
pose proof subst_skvar_Sch_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Sch_fresh : lngen.

(* begin hide *)

Lemma subst_tm_e_fresh_mutual :
(forall e2 e1 x1 x2,
  x1 `notin` free_xs_e e2 ->
  x1 `notin` free_xs_e e1 ->
  x1 `notin` free_xs_e (subst_tm_e e1 x2 e2)).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_e_fresh :
forall e2 e1 x1 x2,
  x1 `notin` free_xs_e e2 ->
  x1 `notin` free_xs_e e1 ->
  x1 `notin` free_xs_e (subst_tm_e e1 x2 e2).
Proof.
pose proof subst_tm_e_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_e_fresh : lngen.

Lemma subst_dskvar_DTy_lc_DTy :
forall DTy1 DTy2 dskA1,
  lc_DTy DTy1 ->
  lc_DTy DTy2 ->
  lc_DTy (subst_dskvar_DTy DTy2 dskA1 DTy1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_dskvar_DTy_lc_DTy : lngen.

Lemma subst_dskvar_DSch_lc_DSch :
forall DSch1 DTy1 dskA1,
  lc_DSch DSch1 ->
  lc_DTy DTy1 ->
  lc_DSch (subst_dskvar_DSch DTy1 dskA1 DSch1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_dskvar_DSch_lc_DSch : lngen.

Lemma subst_skvar_Ty_lc_Ty :
forall Ty1 Ty2 skA1,
  lc_Ty Ty1 ->
  lc_Ty Ty2 ->
  lc_Ty (subst_skvar_Ty Ty2 skA1 Ty1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Ty_lc_Ty : lngen.

Lemma subst_skvar_Sch_lc_Sch :
forall Sch1 Ty1 skA1,
  lc_Sch Sch1 ->
  lc_Ty Ty1 ->
  lc_Sch (subst_skvar_Sch Ty1 skA1 Sch1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Sch_lc_Sch : lngen.

Lemma subst_tm_e_lc_e :
forall e1 e2 x1,
  lc_e e1 ->
  lc_e e2 ->
  lc_e (subst_tm_e e2 x1 e1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tm_e_lc_e : lngen.

(* begin hide *)

Lemma subst_dskvar_DTy_open_DTy_wrt_DTy_rec_mutual :
(forall DTy3 DTy1 DTy2 dskA1 n1,
  lc_DTy DTy1 ->
  subst_dskvar_DTy DTy1 dskA1 (open_DTy_wrt_DTy_rec n1 DTy2 DTy3) = open_DTy_wrt_DTy_rec n1 (subst_dskvar_DTy DTy1 dskA1 DTy2) (subst_dskvar_DTy DTy1 dskA1 DTy3)).
Proof.
apply_mutual_ind DTy_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_dskvar_DTy_open_DTy_wrt_DTy_rec :
forall DTy3 DTy1 DTy2 dskA1 n1,
  lc_DTy DTy1 ->
  subst_dskvar_DTy DTy1 dskA1 (open_DTy_wrt_DTy_rec n1 DTy2 DTy3) = open_DTy_wrt_DTy_rec n1 (subst_dskvar_DTy DTy1 dskA1 DTy2) (subst_dskvar_DTy DTy1 dskA1 DTy3).
Proof.
pose proof subst_dskvar_DTy_open_DTy_wrt_DTy_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_dskvar_DTy_open_DTy_wrt_DTy_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_dskvar_DSch_open_DSch_wrt_DTy_rec_mutual :
(forall DSch1 DTy1 DTy2 dskA1 n1,
  lc_DTy DTy1 ->
  subst_dskvar_DSch DTy1 dskA1 (open_DSch_wrt_DTy_rec n1 DTy2 DSch1) = open_DSch_wrt_DTy_rec n1 (subst_dskvar_DTy DTy1 dskA1 DTy2) (subst_dskvar_DSch DTy1 dskA1 DSch1)).
Proof.
apply_mutual_ind DSch_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_dskvar_DSch_open_DSch_wrt_DTy_rec :
forall DSch1 DTy1 DTy2 dskA1 n1,
  lc_DTy DTy1 ->
  subst_dskvar_DSch DTy1 dskA1 (open_DSch_wrt_DTy_rec n1 DTy2 DSch1) = open_DSch_wrt_DTy_rec n1 (subst_dskvar_DTy DTy1 dskA1 DTy2) (subst_dskvar_DSch DTy1 dskA1 DSch1).
Proof.
pose proof subst_dskvar_DSch_open_DSch_wrt_DTy_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_dskvar_DSch_open_DSch_wrt_DTy_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Ty_open_Ty_wrt_Ty_rec_mutual :
(forall Ty3 Ty1 Ty2 skA1 n1,
  lc_Ty Ty1 ->
  subst_skvar_Ty Ty1 skA1 (open_Ty_wrt_Ty_rec n1 Ty2 Ty3) = open_Ty_wrt_Ty_rec n1 (subst_skvar_Ty Ty1 skA1 Ty2) (subst_skvar_Ty Ty1 skA1 Ty3)).
Proof.
apply_mutual_ind Ty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Ty_open_Ty_wrt_Ty_rec :
forall Ty3 Ty1 Ty2 skA1 n1,
  lc_Ty Ty1 ->
  subst_skvar_Ty Ty1 skA1 (open_Ty_wrt_Ty_rec n1 Ty2 Ty3) = open_Ty_wrt_Ty_rec n1 (subst_skvar_Ty Ty1 skA1 Ty2) (subst_skvar_Ty Ty1 skA1 Ty3).
Proof.
pose proof subst_skvar_Ty_open_Ty_wrt_Ty_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Ty_open_Ty_wrt_Ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Sch_open_Sch_wrt_Ty_rec_mutual :
(forall Sch1 Ty1 Ty2 skA1 n1,
  lc_Ty Ty1 ->
  subst_skvar_Sch Ty1 skA1 (open_Sch_wrt_Ty_rec n1 Ty2 Sch1) = open_Sch_wrt_Ty_rec n1 (subst_skvar_Ty Ty1 skA1 Ty2) (subst_skvar_Sch Ty1 skA1 Sch1)).
Proof.
apply_mutual_ind Sch_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Sch_open_Sch_wrt_Ty_rec :
forall Sch1 Ty1 Ty2 skA1 n1,
  lc_Ty Ty1 ->
  subst_skvar_Sch Ty1 skA1 (open_Sch_wrt_Ty_rec n1 Ty2 Sch1) = open_Sch_wrt_Ty_rec n1 (subst_skvar_Ty Ty1 skA1 Ty2) (subst_skvar_Sch Ty1 skA1 Sch1).
Proof.
pose proof subst_skvar_Sch_open_Sch_wrt_Ty_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Sch_open_Sch_wrt_Ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tm_e_open_e_wrt_e_rec_mutual :
(forall e3 e1 e2 x1 n1,
  lc_e e1 ->
  subst_tm_e e1 x1 (open_e_wrt_e_rec n1 e2 e3) = open_e_wrt_e_rec n1 (subst_tm_e e1 x1 e2) (subst_tm_e e1 x1 e3)).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tm_e_open_e_wrt_e_rec :
forall e3 e1 e2 x1 n1,
  lc_e e1 ->
  subst_tm_e e1 x1 (open_e_wrt_e_rec n1 e2 e3) = open_e_wrt_e_rec n1 (subst_tm_e e1 x1 e2) (subst_tm_e e1 x1 e3).
Proof.
pose proof subst_tm_e_open_e_wrt_e_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_e_open_e_wrt_e_rec : lngen.

(* end hide *)

Lemma subst_dskvar_DTy_open_DTy_wrt_DTy :
forall DTy3 DTy1 DTy2 dskA1,
  lc_DTy DTy1 ->
  subst_dskvar_DTy DTy1 dskA1 (open_DTy_wrt_DTy DTy3 DTy2) = open_DTy_wrt_DTy (subst_dskvar_DTy DTy1 dskA1 DTy3) (subst_dskvar_DTy DTy1 dskA1 DTy2).
Proof.
unfold open_DTy_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve subst_dskvar_DTy_open_DTy_wrt_DTy : lngen.

Lemma subst_dskvar_DSch_open_DSch_wrt_DTy :
forall DSch1 DTy1 DTy2 dskA1,
  lc_DTy DTy1 ->
  subst_dskvar_DSch DTy1 dskA1 (open_DSch_wrt_DTy DSch1 DTy2) = open_DSch_wrt_DTy (subst_dskvar_DSch DTy1 dskA1 DSch1) (subst_dskvar_DTy DTy1 dskA1 DTy2).
Proof.
unfold open_DSch_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve subst_dskvar_DSch_open_DSch_wrt_DTy : lngen.

Lemma subst_skvar_Ty_open_Ty_wrt_Ty :
forall Ty3 Ty1 Ty2 skA1,
  lc_Ty Ty1 ->
  subst_skvar_Ty Ty1 skA1 (open_Ty_wrt_Ty Ty3 Ty2) = open_Ty_wrt_Ty (subst_skvar_Ty Ty1 skA1 Ty3) (subst_skvar_Ty Ty1 skA1 Ty2).
Proof.
unfold open_Ty_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Ty_open_Ty_wrt_Ty : lngen.

Lemma subst_skvar_Sch_open_Sch_wrt_Ty :
forall Sch1 Ty1 Ty2 skA1,
  lc_Ty Ty1 ->
  subst_skvar_Sch Ty1 skA1 (open_Sch_wrt_Ty Sch1 Ty2) = open_Sch_wrt_Ty (subst_skvar_Sch Ty1 skA1 Sch1) (subst_skvar_Ty Ty1 skA1 Ty2).
Proof.
unfold open_Sch_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Sch_open_Sch_wrt_Ty : lngen.

Lemma subst_tm_e_open_e_wrt_e :
forall e3 e1 e2 x1,
  lc_e e1 ->
  subst_tm_e e1 x1 (open_e_wrt_e e3 e2) = open_e_wrt_e (subst_tm_e e1 x1 e3) (subst_tm_e e1 x1 e2).
Proof.
unfold open_e_wrt_e; default_simp.
Qed.

#[export] Hint Resolve subst_tm_e_open_e_wrt_e : lngen.

Lemma subst_dskvar_DTy_open_DTy_wrt_DTy_var :
forall DTy2 DTy1 dskA1 dskA2,
  dskA1 <> dskA2 ->
  lc_DTy DTy1 ->
  open_DTy_wrt_DTy (subst_dskvar_DTy DTy1 dskA1 DTy2) (DT_SkVar_f dskA2) = subst_dskvar_DTy DTy1 dskA1 (open_DTy_wrt_DTy DTy2 (DT_SkVar_f dskA2)).
Proof.
intros; rewrite subst_dskvar_DTy_open_DTy_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve subst_dskvar_DTy_open_DTy_wrt_DTy_var : lngen.

Lemma subst_dskvar_DSch_open_DSch_wrt_DTy_var :
forall DSch1 DTy1 dskA1 dskA2,
  dskA1 <> dskA2 ->
  lc_DTy DTy1 ->
  open_DSch_wrt_DTy (subst_dskvar_DSch DTy1 dskA1 DSch1) (DT_SkVar_f dskA2) = subst_dskvar_DSch DTy1 dskA1 (open_DSch_wrt_DTy DSch1 (DT_SkVar_f dskA2)).
Proof.
intros; rewrite subst_dskvar_DSch_open_DSch_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve subst_dskvar_DSch_open_DSch_wrt_DTy_var : lngen.

Lemma subst_skvar_Ty_open_Ty_wrt_Ty_var :
forall Ty2 Ty1 skA1 skA2,
  skA1 <> skA2 ->
  lc_Ty Ty1 ->
  open_Ty_wrt_Ty (subst_skvar_Ty Ty1 skA1 Ty2) (T_SkVar_f skA2) = subst_skvar_Ty Ty1 skA1 (open_Ty_wrt_Ty Ty2 (T_SkVar_f skA2)).
Proof.
intros; rewrite subst_skvar_Ty_open_Ty_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Ty_open_Ty_wrt_Ty_var : lngen.

Lemma subst_skvar_Sch_open_Sch_wrt_Ty_var :
forall Sch1 Ty1 skA1 skA2,
  skA1 <> skA2 ->
  lc_Ty Ty1 ->
  open_Sch_wrt_Ty (subst_skvar_Sch Ty1 skA1 Sch1) (T_SkVar_f skA2) = subst_skvar_Sch Ty1 skA1 (open_Sch_wrt_Ty Sch1 (T_SkVar_f skA2)).
Proof.
intros; rewrite subst_skvar_Sch_open_Sch_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Sch_open_Sch_wrt_Ty_var : lngen.

Lemma subst_tm_e_open_e_wrt_e_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_e e1 ->
  open_e_wrt_e (subst_tm_e e1 x1 e2) (e_Var_f x2) = subst_tm_e e1 x1 (open_e_wrt_e e2 (e_Var_f x2)).
Proof.
intros; rewrite subst_tm_e_open_e_wrt_e; default_simp.
Qed.

#[export] Hint Resolve subst_tm_e_open_e_wrt_e_var : lngen.

(* begin hide *)

Lemma subst_dskvar_DTy_spec_rec_mutual :
(forall DTy1 DTy2 dskA1 n1,
  subst_dskvar_DTy DTy2 dskA1 DTy1 = open_DTy_wrt_DTy_rec n1 DTy2 (close_DTy_wrt_DTy_rec n1 dskA1 DTy1)).
Proof.
apply_mutual_ind DTy_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_dskvar_DTy_spec_rec :
forall DTy1 DTy2 dskA1 n1,
  subst_dskvar_DTy DTy2 dskA1 DTy1 = open_DTy_wrt_DTy_rec n1 DTy2 (close_DTy_wrt_DTy_rec n1 dskA1 DTy1).
Proof.
pose proof subst_dskvar_DTy_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_dskvar_DTy_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_dskvar_DSch_spec_rec_mutual :
(forall DSch1 DTy1 dskA1 n1,
  subst_dskvar_DSch DTy1 dskA1 DSch1 = open_DSch_wrt_DTy_rec n1 DTy1 (close_DSch_wrt_DTy_rec n1 dskA1 DSch1)).
Proof.
apply_mutual_ind DSch_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_dskvar_DSch_spec_rec :
forall DSch1 DTy1 dskA1 n1,
  subst_dskvar_DSch DTy1 dskA1 DSch1 = open_DSch_wrt_DTy_rec n1 DTy1 (close_DSch_wrt_DTy_rec n1 dskA1 DSch1).
Proof.
pose proof subst_dskvar_DSch_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_dskvar_DSch_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Ty_spec_rec_mutual :
(forall Ty1 Ty2 skA1 n1,
  subst_skvar_Ty Ty2 skA1 Ty1 = open_Ty_wrt_Ty_rec n1 Ty2 (close_Ty_wrt_Ty_rec n1 skA1 Ty1)).
Proof.
apply_mutual_ind Ty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Ty_spec_rec :
forall Ty1 Ty2 skA1 n1,
  subst_skvar_Ty Ty2 skA1 Ty1 = open_Ty_wrt_Ty_rec n1 Ty2 (close_Ty_wrt_Ty_rec n1 skA1 Ty1).
Proof.
pose proof subst_skvar_Ty_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Ty_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Sch_spec_rec_mutual :
(forall Sch1 Ty1 skA1 n1,
  subst_skvar_Sch Ty1 skA1 Sch1 = open_Sch_wrt_Ty_rec n1 Ty1 (close_Sch_wrt_Ty_rec n1 skA1 Sch1)).
Proof.
apply_mutual_ind Sch_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Sch_spec_rec :
forall Sch1 Ty1 skA1 n1,
  subst_skvar_Sch Ty1 skA1 Sch1 = open_Sch_wrt_Ty_rec n1 Ty1 (close_Sch_wrt_Ty_rec n1 skA1 Sch1).
Proof.
pose proof subst_skvar_Sch_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Sch_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tm_e_spec_rec_mutual :
(forall e1 e2 x1 n1,
  subst_tm_e e2 x1 e1 = open_e_wrt_e_rec n1 e2 (close_e_wrt_e_rec n1 x1 e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tm_e_spec_rec :
forall e1 e2 x1 n1,
  subst_tm_e e2 x1 e1 = open_e_wrt_e_rec n1 e2 (close_e_wrt_e_rec n1 x1 e1).
Proof.
pose proof subst_tm_e_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_e_spec_rec : lngen.

(* end hide *)

Lemma subst_dskvar_DTy_spec :
forall DTy1 DTy2 dskA1,
  subst_dskvar_DTy DTy2 dskA1 DTy1 = open_DTy_wrt_DTy (close_DTy_wrt_DTy dskA1 DTy1) DTy2.
Proof.
unfold close_DTy_wrt_DTy; unfold open_DTy_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve subst_dskvar_DTy_spec : lngen.

Lemma subst_dskvar_DSch_spec :
forall DSch1 DTy1 dskA1,
  subst_dskvar_DSch DTy1 dskA1 DSch1 = open_DSch_wrt_DTy (close_DSch_wrt_DTy dskA1 DSch1) DTy1.
Proof.
unfold close_DSch_wrt_DTy; unfold open_DSch_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve subst_dskvar_DSch_spec : lngen.

Lemma subst_skvar_Ty_spec :
forall Ty1 Ty2 skA1,
  subst_skvar_Ty Ty2 skA1 Ty1 = open_Ty_wrt_Ty (close_Ty_wrt_Ty skA1 Ty1) Ty2.
Proof.
unfold close_Ty_wrt_Ty; unfold open_Ty_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Ty_spec : lngen.

Lemma subst_skvar_Sch_spec :
forall Sch1 Ty1 skA1,
  subst_skvar_Sch Ty1 skA1 Sch1 = open_Sch_wrt_Ty (close_Sch_wrt_Ty skA1 Sch1) Ty1.
Proof.
unfold close_Sch_wrt_Ty; unfold open_Sch_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Sch_spec : lngen.

Lemma subst_tm_e_spec :
forall e1 e2 x1,
  subst_tm_e e2 x1 e1 = open_e_wrt_e (close_e_wrt_e x1 e1) e2.
Proof.
unfold close_e_wrt_e; unfold open_e_wrt_e; default_simp.
Qed.

#[export] Hint Resolve subst_tm_e_spec : lngen.

(* begin hide *)

Lemma subst_dskvar_DTy_subst_dskvar_DTy_mutual :
(forall DTy1 DTy2 DTy3 dskA2 dskA1,
  dskA2 `notin` free_dskvars_DTy DTy2 ->
  dskA2 <> dskA1 ->
  subst_dskvar_DTy DTy2 dskA1 (subst_dskvar_DTy DTy3 dskA2 DTy1) = subst_dskvar_DTy (subst_dskvar_DTy DTy2 dskA1 DTy3) dskA2 (subst_dskvar_DTy DTy2 dskA1 DTy1)).
Proof.
apply_mutual_ind DTy_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dskvar_DTy_subst_dskvar_DTy :
forall DTy1 DTy2 DTy3 dskA2 dskA1,
  dskA2 `notin` free_dskvars_DTy DTy2 ->
  dskA2 <> dskA1 ->
  subst_dskvar_DTy DTy2 dskA1 (subst_dskvar_DTy DTy3 dskA2 DTy1) = subst_dskvar_DTy (subst_dskvar_DTy DTy2 dskA1 DTy3) dskA2 (subst_dskvar_DTy DTy2 dskA1 DTy1).
Proof.
pose proof subst_dskvar_DTy_subst_dskvar_DTy_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_dskvar_DTy_subst_dskvar_DTy : lngen.

(* begin hide *)

Lemma subst_dskvar_DSch_subst_dskvar_DSch_mutual :
(forall DSch1 DTy1 DTy2 dskA2 dskA1,
  dskA2 `notin` free_dskvars_DTy DTy1 ->
  dskA2 <> dskA1 ->
  subst_dskvar_DSch DTy1 dskA1 (subst_dskvar_DSch DTy2 dskA2 DSch1) = subst_dskvar_DSch (subst_dskvar_DTy DTy1 dskA1 DTy2) dskA2 (subst_dskvar_DSch DTy1 dskA1 DSch1)).
Proof.
apply_mutual_ind DSch_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dskvar_DSch_subst_dskvar_DSch :
forall DSch1 DTy1 DTy2 dskA2 dskA1,
  dskA2 `notin` free_dskvars_DTy DTy1 ->
  dskA2 <> dskA1 ->
  subst_dskvar_DSch DTy1 dskA1 (subst_dskvar_DSch DTy2 dskA2 DSch1) = subst_dskvar_DSch (subst_dskvar_DTy DTy1 dskA1 DTy2) dskA2 (subst_dskvar_DSch DTy1 dskA1 DSch1).
Proof.
pose proof subst_dskvar_DSch_subst_dskvar_DSch_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_dskvar_DSch_subst_dskvar_DSch : lngen.

(* begin hide *)

Lemma subst_skvar_Ty_subst_skvar_Ty_mutual :
(forall Ty1 Ty2 Ty3 skA2 skA1,
  skA2 `notin` free_skvars_Ty Ty2 ->
  skA2 <> skA1 ->
  subst_skvar_Ty Ty2 skA1 (subst_skvar_Ty Ty3 skA2 Ty1) = subst_skvar_Ty (subst_skvar_Ty Ty2 skA1 Ty3) skA2 (subst_skvar_Ty Ty2 skA1 Ty1)).
Proof.
apply_mutual_ind Ty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Ty_subst_skvar_Ty :
forall Ty1 Ty2 Ty3 skA2 skA1,
  skA2 `notin` free_skvars_Ty Ty2 ->
  skA2 <> skA1 ->
  subst_skvar_Ty Ty2 skA1 (subst_skvar_Ty Ty3 skA2 Ty1) = subst_skvar_Ty (subst_skvar_Ty Ty2 skA1 Ty3) skA2 (subst_skvar_Ty Ty2 skA1 Ty1).
Proof.
pose proof subst_skvar_Ty_subst_skvar_Ty_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Ty_subst_skvar_Ty : lngen.

(* begin hide *)

Lemma subst_skvar_Sch_subst_skvar_Sch_mutual :
(forall Sch1 Ty1 Ty2 skA2 skA1,
  skA2 `notin` free_skvars_Ty Ty1 ->
  skA2 <> skA1 ->
  subst_skvar_Sch Ty1 skA1 (subst_skvar_Sch Ty2 skA2 Sch1) = subst_skvar_Sch (subst_skvar_Ty Ty1 skA1 Ty2) skA2 (subst_skvar_Sch Ty1 skA1 Sch1)).
Proof.
apply_mutual_ind Sch_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Sch_subst_skvar_Sch :
forall Sch1 Ty1 Ty2 skA2 skA1,
  skA2 `notin` free_skvars_Ty Ty1 ->
  skA2 <> skA1 ->
  subst_skvar_Sch Ty1 skA1 (subst_skvar_Sch Ty2 skA2 Sch1) = subst_skvar_Sch (subst_skvar_Ty Ty1 skA1 Ty2) skA2 (subst_skvar_Sch Ty1 skA1 Sch1).
Proof.
pose proof subst_skvar_Sch_subst_skvar_Sch_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Sch_subst_skvar_Sch : lngen.

(* begin hide *)

Lemma subst_tm_e_subst_tm_e_mutual :
(forall e1 e2 e3 x2 x1,
  x2 `notin` free_xs_e e2 ->
  x2 <> x1 ->
  subst_tm_e e2 x1 (subst_tm_e e3 x2 e1) = subst_tm_e (subst_tm_e e2 x1 e3) x2 (subst_tm_e e2 x1 e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_e_subst_tm_e :
forall e1 e2 e3 x2 x1,
  x2 `notin` free_xs_e e2 ->
  x2 <> x1 ->
  subst_tm_e e2 x1 (subst_tm_e e3 x2 e1) = subst_tm_e (subst_tm_e e2 x1 e3) x2 (subst_tm_e e2 x1 e1).
Proof.
pose proof subst_tm_e_subst_tm_e_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_e_subst_tm_e : lngen.

(* begin hide *)

Lemma subst_dskvar_DTy_close_DTy_wrt_DTy_rec_open_DTy_wrt_DTy_rec_mutual :
(forall DTy2 DTy1 dskA1 dskA2 n1,
  dskA2 `notin` free_dskvars_DTy DTy2 ->
  dskA2 `notin` free_dskvars_DTy DTy1 ->
  dskA2 <> dskA1 ->
  degree_DTy_wrt_DTy n1 DTy1 ->
  subst_dskvar_DTy DTy1 dskA1 DTy2 = close_DTy_wrt_DTy_rec n1 dskA2 (subst_dskvar_DTy DTy1 dskA1 (open_DTy_wrt_DTy_rec n1 (DT_SkVar_f dskA2) DTy2))).
Proof.
apply_mutual_ind DTy_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_dskvar_DTy_close_DTy_wrt_DTy_rec_open_DTy_wrt_DTy_rec :
forall DTy2 DTy1 dskA1 dskA2 n1,
  dskA2 `notin` free_dskvars_DTy DTy2 ->
  dskA2 `notin` free_dskvars_DTy DTy1 ->
  dskA2 <> dskA1 ->
  degree_DTy_wrt_DTy n1 DTy1 ->
  subst_dskvar_DTy DTy1 dskA1 DTy2 = close_DTy_wrt_DTy_rec n1 dskA2 (subst_dskvar_DTy DTy1 dskA1 (open_DTy_wrt_DTy_rec n1 (DT_SkVar_f dskA2) DTy2)).
Proof.
pose proof subst_dskvar_DTy_close_DTy_wrt_DTy_rec_open_DTy_wrt_DTy_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_dskvar_DTy_close_DTy_wrt_DTy_rec_open_DTy_wrt_DTy_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_dskvar_DSch_close_DSch_wrt_DTy_rec_open_DSch_wrt_DTy_rec_mutual :
(forall DSch1 DTy1 dskA1 dskA2 n1,
  dskA2 `notin` free_dskvars_DSch DSch1 ->
  dskA2 `notin` free_dskvars_DTy DTy1 ->
  dskA2 <> dskA1 ->
  degree_DTy_wrt_DTy n1 DTy1 ->
  subst_dskvar_DSch DTy1 dskA1 DSch1 = close_DSch_wrt_DTy_rec n1 dskA2 (subst_dskvar_DSch DTy1 dskA1 (open_DSch_wrt_DTy_rec n1 (DT_SkVar_f dskA2) DSch1))).
Proof.
apply_mutual_ind DSch_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_dskvar_DSch_close_DSch_wrt_DTy_rec_open_DSch_wrt_DTy_rec :
forall DSch1 DTy1 dskA1 dskA2 n1,
  dskA2 `notin` free_dskvars_DSch DSch1 ->
  dskA2 `notin` free_dskvars_DTy DTy1 ->
  dskA2 <> dskA1 ->
  degree_DTy_wrt_DTy n1 DTy1 ->
  subst_dskvar_DSch DTy1 dskA1 DSch1 = close_DSch_wrt_DTy_rec n1 dskA2 (subst_dskvar_DSch DTy1 dskA1 (open_DSch_wrt_DTy_rec n1 (DT_SkVar_f dskA2) DSch1)).
Proof.
pose proof subst_dskvar_DSch_close_DSch_wrt_DTy_rec_open_DSch_wrt_DTy_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_dskvar_DSch_close_DSch_wrt_DTy_rec_open_DSch_wrt_DTy_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Ty_close_Ty_wrt_Ty_rec_open_Ty_wrt_Ty_rec_mutual :
(forall Ty2 Ty1 skA1 skA2 n1,
  skA2 `notin` free_skvars_Ty Ty2 ->
  skA2 `notin` free_skvars_Ty Ty1 ->
  skA2 <> skA1 ->
  degree_Ty_wrt_Ty n1 Ty1 ->
  subst_skvar_Ty Ty1 skA1 Ty2 = close_Ty_wrt_Ty_rec n1 skA2 (subst_skvar_Ty Ty1 skA1 (open_Ty_wrt_Ty_rec n1 (T_SkVar_f skA2) Ty2))).
Proof.
apply_mutual_ind Ty_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Ty_close_Ty_wrt_Ty_rec_open_Ty_wrt_Ty_rec :
forall Ty2 Ty1 skA1 skA2 n1,
  skA2 `notin` free_skvars_Ty Ty2 ->
  skA2 `notin` free_skvars_Ty Ty1 ->
  skA2 <> skA1 ->
  degree_Ty_wrt_Ty n1 Ty1 ->
  subst_skvar_Ty Ty1 skA1 Ty2 = close_Ty_wrt_Ty_rec n1 skA2 (subst_skvar_Ty Ty1 skA1 (open_Ty_wrt_Ty_rec n1 (T_SkVar_f skA2) Ty2)).
Proof.
pose proof subst_skvar_Ty_close_Ty_wrt_Ty_rec_open_Ty_wrt_Ty_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Ty_close_Ty_wrt_Ty_rec_open_Ty_wrt_Ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Sch_close_Sch_wrt_Ty_rec_open_Sch_wrt_Ty_rec_mutual :
(forall Sch1 Ty1 skA1 skA2 n1,
  skA2 `notin` free_skvars_Sch Sch1 ->
  skA2 `notin` free_skvars_Ty Ty1 ->
  skA2 <> skA1 ->
  degree_Ty_wrt_Ty n1 Ty1 ->
  subst_skvar_Sch Ty1 skA1 Sch1 = close_Sch_wrt_Ty_rec n1 skA2 (subst_skvar_Sch Ty1 skA1 (open_Sch_wrt_Ty_rec n1 (T_SkVar_f skA2) Sch1))).
Proof.
apply_mutual_ind Sch_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Sch_close_Sch_wrt_Ty_rec_open_Sch_wrt_Ty_rec :
forall Sch1 Ty1 skA1 skA2 n1,
  skA2 `notin` free_skvars_Sch Sch1 ->
  skA2 `notin` free_skvars_Ty Ty1 ->
  skA2 <> skA1 ->
  degree_Ty_wrt_Ty n1 Ty1 ->
  subst_skvar_Sch Ty1 skA1 Sch1 = close_Sch_wrt_Ty_rec n1 skA2 (subst_skvar_Sch Ty1 skA1 (open_Sch_wrt_Ty_rec n1 (T_SkVar_f skA2) Sch1)).
Proof.
pose proof subst_skvar_Sch_close_Sch_wrt_Ty_rec_open_Sch_wrt_Ty_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Sch_close_Sch_wrt_Ty_rec_open_Sch_wrt_Ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tm_e_close_e_wrt_e_rec_open_e_wrt_e_rec_mutual :
(forall e2 e1 x1 x2 n1,
  x2 `notin` free_xs_e e2 ->
  x2 `notin` free_xs_e e1 ->
  x2 <> x1 ->
  degree_e_wrt_e n1 e1 ->
  subst_tm_e e1 x1 e2 = close_e_wrt_e_rec n1 x2 (subst_tm_e e1 x1 (open_e_wrt_e_rec n1 (e_Var_f x2) e2))).
Proof.
apply_mutual_ind e_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tm_e_close_e_wrt_e_rec_open_e_wrt_e_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` free_xs_e e2 ->
  x2 `notin` free_xs_e e1 ->
  x2 <> x1 ->
  degree_e_wrt_e n1 e1 ->
  subst_tm_e e1 x1 e2 = close_e_wrt_e_rec n1 x2 (subst_tm_e e1 x1 (open_e_wrt_e_rec n1 (e_Var_f x2) e2)).
Proof.
pose proof subst_tm_e_close_e_wrt_e_rec_open_e_wrt_e_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_e_close_e_wrt_e_rec_open_e_wrt_e_rec : lngen.

(* end hide *)

Lemma subst_dskvar_DTy_close_DTy_wrt_DTy_open_DTy_wrt_DTy :
forall DTy2 DTy1 dskA1 dskA2,
  dskA2 `notin` free_dskvars_DTy DTy2 ->
  dskA2 `notin` free_dskvars_DTy DTy1 ->
  dskA2 <> dskA1 ->
  lc_DTy DTy1 ->
  subst_dskvar_DTy DTy1 dskA1 DTy2 = close_DTy_wrt_DTy dskA2 (subst_dskvar_DTy DTy1 dskA1 (open_DTy_wrt_DTy DTy2 (DT_SkVar_f dskA2))).
Proof.
unfold close_DTy_wrt_DTy; unfold open_DTy_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve subst_dskvar_DTy_close_DTy_wrt_DTy_open_DTy_wrt_DTy : lngen.

Lemma subst_dskvar_DSch_close_DSch_wrt_DTy_open_DSch_wrt_DTy :
forall DSch1 DTy1 dskA1 dskA2,
  dskA2 `notin` free_dskvars_DSch DSch1 ->
  dskA2 `notin` free_dskvars_DTy DTy1 ->
  dskA2 <> dskA1 ->
  lc_DTy DTy1 ->
  subst_dskvar_DSch DTy1 dskA1 DSch1 = close_DSch_wrt_DTy dskA2 (subst_dskvar_DSch DTy1 dskA1 (open_DSch_wrt_DTy DSch1 (DT_SkVar_f dskA2))).
Proof.
unfold close_DSch_wrt_DTy; unfold open_DSch_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve subst_dskvar_DSch_close_DSch_wrt_DTy_open_DSch_wrt_DTy : lngen.

Lemma subst_skvar_Ty_close_Ty_wrt_Ty_open_Ty_wrt_Ty :
forall Ty2 Ty1 skA1 skA2,
  skA2 `notin` free_skvars_Ty Ty2 ->
  skA2 `notin` free_skvars_Ty Ty1 ->
  skA2 <> skA1 ->
  lc_Ty Ty1 ->
  subst_skvar_Ty Ty1 skA1 Ty2 = close_Ty_wrt_Ty skA2 (subst_skvar_Ty Ty1 skA1 (open_Ty_wrt_Ty Ty2 (T_SkVar_f skA2))).
Proof.
unfold close_Ty_wrt_Ty; unfold open_Ty_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Ty_close_Ty_wrt_Ty_open_Ty_wrt_Ty : lngen.

Lemma subst_skvar_Sch_close_Sch_wrt_Ty_open_Sch_wrt_Ty :
forall Sch1 Ty1 skA1 skA2,
  skA2 `notin` free_skvars_Sch Sch1 ->
  skA2 `notin` free_skvars_Ty Ty1 ->
  skA2 <> skA1 ->
  lc_Ty Ty1 ->
  subst_skvar_Sch Ty1 skA1 Sch1 = close_Sch_wrt_Ty skA2 (subst_skvar_Sch Ty1 skA1 (open_Sch_wrt_Ty Sch1 (T_SkVar_f skA2))).
Proof.
unfold close_Sch_wrt_Ty; unfold open_Sch_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Sch_close_Sch_wrt_Ty_open_Sch_wrt_Ty : lngen.

Lemma subst_tm_e_close_e_wrt_e_open_e_wrt_e :
forall e2 e1 x1 x2,
  x2 `notin` free_xs_e e2 ->
  x2 `notin` free_xs_e e1 ->
  x2 <> x1 ->
  lc_e e1 ->
  subst_tm_e e1 x1 e2 = close_e_wrt_e x2 (subst_tm_e e1 x1 (open_e_wrt_e e2 (e_Var_f x2))).
Proof.
unfold close_e_wrt_e; unfold open_e_wrt_e; default_simp.
Qed.

#[export] Hint Resolve subst_tm_e_close_e_wrt_e_open_e_wrt_e : lngen.

Lemma subst_dskvar_DSch_DS_Forall :
forall dskA2 DSch1 DTy1 dskA1,
  lc_DTy DTy1 ->
  dskA2 `notin` free_dskvars_DTy DTy1 `union` free_dskvars_DSch DSch1 `union` singleton dskA1 ->
  subst_dskvar_DSch DTy1 dskA1 (DS_Forall DSch1) = DS_Forall (close_DSch_wrt_DTy dskA2 (subst_dskvar_DSch DTy1 dskA1 (open_DSch_wrt_DTy DSch1 (DT_SkVar_f dskA2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_dskvar_DSch_DS_Forall : lngen.

Lemma subst_skvar_Sch_S_Forall :
forall skA2 Sch1 Ty1 skA1,
  lc_Ty Ty1 ->
  skA2 `notin` free_skvars_Ty Ty1 `union` free_skvars_Sch Sch1 `union` singleton skA1 ->
  subst_skvar_Sch Ty1 skA1 (S_Forall Sch1) = S_Forall (close_Sch_wrt_Ty skA2 (subst_skvar_Sch Ty1 skA1 (open_Sch_wrt_Ty Sch1 (T_SkVar_f skA2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Sch_S_Forall : lngen.

Lemma subst_tm_e_e_Lam :
forall x2 e2 e1 x1,
  lc_e e1 ->
  x2 `notin` free_xs_e e1 `union` free_xs_e e2 `union` singleton x1 ->
  subst_tm_e e1 x1 (e_Lam e2) = e_Lam (close_e_wrt_e x2 (subst_tm_e e1 x1 (open_e_wrt_e e2 (e_Var_f x2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tm_e_e_Lam : lngen.

Lemma subst_tm_e_e_Let :
forall x2 e2 e3 e1 x1,
  lc_e e1 ->
  x2 `notin` free_xs_e e1 `union` free_xs_e e3 `union` singleton x1 ->
  subst_tm_e e1 x1 (e_Let e2 e3) = e_Let (subst_tm_e e1 x1 e2) (close_e_wrt_e x2 (subst_tm_e e1 x1 (open_e_wrt_e e3 (e_Var_f x2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tm_e_e_Let : lngen.

(* begin hide *)

Lemma subst_dskvar_DTy_intro_rec_mutual :
(forall DTy1 dskA1 DTy2 n1,
  dskA1 `notin` free_dskvars_DTy DTy1 ->
  open_DTy_wrt_DTy_rec n1 DTy2 DTy1 = subst_dskvar_DTy DTy2 dskA1 (open_DTy_wrt_DTy_rec n1 (DT_SkVar_f dskA1) DTy1)).
Proof.
apply_mutual_ind DTy_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dskvar_DTy_intro_rec :
forall DTy1 dskA1 DTy2 n1,
  dskA1 `notin` free_dskvars_DTy DTy1 ->
  open_DTy_wrt_DTy_rec n1 DTy2 DTy1 = subst_dskvar_DTy DTy2 dskA1 (open_DTy_wrt_DTy_rec n1 (DT_SkVar_f dskA1) DTy1).
Proof.
pose proof subst_dskvar_DTy_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_dskvar_DTy_intro_rec : lngen.
#[export] Hint Rewrite subst_dskvar_DTy_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_dskvar_DSch_intro_rec_mutual :
(forall DSch1 dskA1 DTy1 n1,
  dskA1 `notin` free_dskvars_DSch DSch1 ->
  open_DSch_wrt_DTy_rec n1 DTy1 DSch1 = subst_dskvar_DSch DTy1 dskA1 (open_DSch_wrt_DTy_rec n1 (DT_SkVar_f dskA1) DSch1)).
Proof.
apply_mutual_ind DSch_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dskvar_DSch_intro_rec :
forall DSch1 dskA1 DTy1 n1,
  dskA1 `notin` free_dskvars_DSch DSch1 ->
  open_DSch_wrt_DTy_rec n1 DTy1 DSch1 = subst_dskvar_DSch DTy1 dskA1 (open_DSch_wrt_DTy_rec n1 (DT_SkVar_f dskA1) DSch1).
Proof.
pose proof subst_dskvar_DSch_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_dskvar_DSch_intro_rec : lngen.
#[export] Hint Rewrite subst_dskvar_DSch_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_skvar_Ty_intro_rec_mutual :
(forall Ty1 skA1 Ty2 n1,
  skA1 `notin` free_skvars_Ty Ty1 ->
  open_Ty_wrt_Ty_rec n1 Ty2 Ty1 = subst_skvar_Ty Ty2 skA1 (open_Ty_wrt_Ty_rec n1 (T_SkVar_f skA1) Ty1)).
Proof.
apply_mutual_ind Ty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Ty_intro_rec :
forall Ty1 skA1 Ty2 n1,
  skA1 `notin` free_skvars_Ty Ty1 ->
  open_Ty_wrt_Ty_rec n1 Ty2 Ty1 = subst_skvar_Ty Ty2 skA1 (open_Ty_wrt_Ty_rec n1 (T_SkVar_f skA1) Ty1).
Proof.
pose proof subst_skvar_Ty_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Ty_intro_rec : lngen.
#[export] Hint Rewrite subst_skvar_Ty_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_skvar_Sch_intro_rec_mutual :
(forall Sch1 skA1 Ty1 n1,
  skA1 `notin` free_skvars_Sch Sch1 ->
  open_Sch_wrt_Ty_rec n1 Ty1 Sch1 = subst_skvar_Sch Ty1 skA1 (open_Sch_wrt_Ty_rec n1 (T_SkVar_f skA1) Sch1)).
Proof.
apply_mutual_ind Sch_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Sch_intro_rec :
forall Sch1 skA1 Ty1 n1,
  skA1 `notin` free_skvars_Sch Sch1 ->
  open_Sch_wrt_Ty_rec n1 Ty1 Sch1 = subst_skvar_Sch Ty1 skA1 (open_Sch_wrt_Ty_rec n1 (T_SkVar_f skA1) Sch1).
Proof.
pose proof subst_skvar_Sch_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Sch_intro_rec : lngen.
#[export] Hint Rewrite subst_skvar_Sch_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tm_e_intro_rec_mutual :
(forall e1 x1 e2 n1,
  x1 `notin` free_xs_e e1 ->
  open_e_wrt_e_rec n1 e2 e1 = subst_tm_e e2 x1 (open_e_wrt_e_rec n1 (e_Var_f x1) e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_e_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` free_xs_e e1 ->
  open_e_wrt_e_rec n1 e2 e1 = subst_tm_e e2 x1 (open_e_wrt_e_rec n1 (e_Var_f x1) e1).
Proof.
pose proof subst_tm_e_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_e_intro_rec : lngen.
#[export] Hint Rewrite subst_tm_e_intro_rec using solve [auto] : lngen.

Lemma subst_dskvar_DTy_intro :
forall dskA1 DTy1 DTy2,
  dskA1 `notin` free_dskvars_DTy DTy1 ->
  open_DTy_wrt_DTy DTy1 DTy2 = subst_dskvar_DTy DTy2 dskA1 (open_DTy_wrt_DTy DTy1 (DT_SkVar_f dskA1)).
Proof.
unfold open_DTy_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve subst_dskvar_DTy_intro : lngen.

Lemma subst_dskvar_DSch_intro :
forall dskA1 DSch1 DTy1,
  dskA1 `notin` free_dskvars_DSch DSch1 ->
  open_DSch_wrt_DTy DSch1 DTy1 = subst_dskvar_DSch DTy1 dskA1 (open_DSch_wrt_DTy DSch1 (DT_SkVar_f dskA1)).
Proof.
unfold open_DSch_wrt_DTy; default_simp.
Qed.

#[export] Hint Resolve subst_dskvar_DSch_intro : lngen.

Lemma subst_skvar_Ty_intro :
forall skA1 Ty1 Ty2,
  skA1 `notin` free_skvars_Ty Ty1 ->
  open_Ty_wrt_Ty Ty1 Ty2 = subst_skvar_Ty Ty2 skA1 (open_Ty_wrt_Ty Ty1 (T_SkVar_f skA1)).
Proof.
unfold open_Ty_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Ty_intro : lngen.

Lemma subst_skvar_Sch_intro :
forall skA1 Sch1 Ty1,
  skA1 `notin` free_skvars_Sch Sch1 ->
  open_Sch_wrt_Ty Sch1 Ty1 = subst_skvar_Sch Ty1 skA1 (open_Sch_wrt_Ty Sch1 (T_SkVar_f skA1)).
Proof.
unfold open_Sch_wrt_Ty; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Sch_intro : lngen.

Lemma subst_tm_e_intro :
forall x1 e1 e2,
  x1 `notin` free_xs_e e1 ->
  open_e_wrt_e e1 e2 = subst_tm_e e2 x1 (open_e_wrt_e e1 (e_Var_f x1)).
Proof.
unfold open_e_wrt_e; default_simp.
Qed.

#[export] Hint Resolve subst_tm_e_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
