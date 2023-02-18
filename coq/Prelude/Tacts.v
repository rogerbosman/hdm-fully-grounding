(* -*- company-coq-local-symbols: (("|=" . ?⊨) ("=|" . ?⫤) ("->>" . ?↠) ("=~" . ?≈) ("<|" . ?⟨) ("|>" . ?⟩) ); -*- *)
Set Warnings "-notation-overridden".

Require Export Metalib.Metatheory.
Require Export Cpdtlib.CpdtTactics.
Require Import Defs.HdmDefs.
Require Export LibTactics.LibTactics.
(* Require Export TLC.LibTactics. *)

(** induction *)
Ltac Sch_Ty_ind sch :=
    let ty := fresh "ty" in
    induction sch as [Ty | ?]; [induction Ty | idtac].
Ltac DSch_DTy_ind dsch :=
    let dty := fresh "dty" in
    induction dsch as [dty | ?]; [induction dty | idtac].

(** if elimination *)
Ltac ifdec :=
  repeat match goal with
    | [ |- context[if ?X then _ else _] ] => destruct X
    | [ H : context[if ?X then _ else _] |- _ ] => destruct X
  end.
Ltac ifdec' := ifdec; subst.

Ltac if_taut :=
  let EQ := fresh "EQ" in
  repeat match goal with
    | [ |- context[if ?X then _ else _] ]       => destruct X as [EQ|?]; try congruence; try clear EQ
    | [ H : context[if ?X then _ else _] |- _ ] => destruct X as [EQ|?]; try congruence; try clear EQ
  end.

(** ltdec *)
Ltac ltdec :=
  match goal with
      | [ |- context[lt_eq_lt_dec ?n1 ?n2] ] => destruct (lt_eq_lt_dec n1 n2)
      | [ |- context[lt_dec ?n1 ?n2] ] => destruct (lt_dec n1 n2)
  end.

(** Destr *)
Ltac destr :=
  repeat match goal with
    | [ H : ex (fun x => _) |- _ ] => let x := fresh x in destruct H as [x H]
    | [ H : _ \/ _ |- _ ] => destruct H
    | [ H : _ /\ _ |- _ ] => destruct H
    | [ H : (_,_) = (_,_) |- _ ] => inverts H
    end; subst.

Ltac destr' :=
  repeat match goal with
    | [ H : ex _ |- _ ] => destruct H
    | [ H : _ \/ _ |- _ ] => destruct H
    | [ H : _ /\ _ |- _ ] => destruct H
    | [ H : _ \notin _ |- _ ] => unfold not in H
    | [  |- _ \notin _ ] => unfold not; intro
    end; subst.

(** rewr *)
Ltac rewr_auto := autorewrite with core.
Tactic Notation "rewr_auto" "in" hyp(H) := autorewrite with core in H.
Tactic Notation "rewr_auto*" := autorewrite with core in *.

Ltac rewr_setprops := repeat ( simpl SEqual || simpl SSubset || simpl Sunion || simpl Sempty || simpl Selt || simpl Ssingleton || simpl SIn).
Tactic Notation "rewr_setprops" "in" hyp(H) :=
  repeat (simpl SEqual in H || simpl SSubset in H || simpl Sunion in H || simpl Sempty in H || simpl Selt in H || simpl Ssingleton in H || simpl SIn in H).
Tactic Notation "rewr_setprops*" :=
  repeat (simpl SEqual in * || simpl SSubset in * || simpl Sunion in * || simpl Sempty in * || simpl Selt in * || simpl Ssingleton in * || simpl SIn in *).

Ltac unfold_List_to_Set :=
           ( (try unfold varl     ); (try unfold DSub_dom     ); (try unfold DSub_codom     )
           ; (try unfold DSub_bindings     ); (try unfold DSub_codom_dskvars     ) ).
Tactic Notation "unfold_List_to_Set" "in" hyp(H) :=
           ( (try unfold varl in H); (try unfold DSub_dom in H); (try unfold DSub_codom in H)
           ; (try unfold DSub_bindings in H); (try unfold DSub_codom_dskvars in H) ).
Tactic Notation "unfold_List_to_Set*" :=
           ( (try unfold varl in *); (try unfold DSub_dom in *); (try unfold DSub_codom in *)
           ; (try unfold DSub_bindings in *); (try unfold DSub_codom_dskvars in *) ).

Ltac   fold_List_to_Set :=
           ( (try   fold varl     ); (try   fold DSub_dom     ); (try   fold DSub_codom     )
           ; (try   fold DSub_bindings     ); (try   fold DSub_codom_dskvars     ) ).
Tactic Notation "  fold_List_to_Set" "in" hyp(H) :=
           ( (try   fold varl in H); (try   fold DSub_dom in H); (try   fold DSub_codom in H)
           ; (try   fold DSub_bindings in H); (try   fold DSub_codom_dskvars in H) ).
Tactic Notation "  fold_List_to_Set*" :=
           ( (try   fold varl in *); (try   fold DSub_dom in *); (try   fold DSub_codom in *)
           ; (try   fold DSub_bindings in *); (try   fold DSub_codom_dskvars in *) ).


Ltac unfold_DEnv_to_Set :=
           ( (try unfold DEnv_dskvars     ); (try unfold DEnv_bindings     ); (try unfold DEnv_DSchs     )
           ; (try unfold DEnv_boundvars     ) ).
Tactic Notation "unfold_DEnv_to_Set" "in" hyp(H) :=
           ( (try unfold DEnv_dskvars in H); (try unfold DEnv_bindings in H); (try unfold DEnv_DSchs in H)
           ; (try unfold DEnv_boundvars in H) ).
Tactic Notation "unfold_DEnv_to_Set*" :=
           ( (try unfold DEnv_dskvars in *); (try unfold DEnv_bindings in *); (try unfold DEnv_DSchs in *)
           ; (try unfold DEnv_boundvars in *) ).

Ltac   fold_DEnv_to_Set :=
           ( (try   fold DEnv_dskvars     ); (try   fold DEnv_bindings     ); (try   fold DEnv_DSchs     )
           ; (try   fold DEnv_boundvars     ) ).
Tactic Notation "  fold_DEnv_to_Set" "in" hyp(H) :=
           ( (try   fold DEnv_dskvars in H); (try   fold DEnv_bindings in H); (try   fold DEnv_DSchs in H)
           ; (try   fold DEnv_boundvars in H) ).
Tactic Notation "  fold_DEnv_to_Set*" :=
           ( (try   fold DEnv_dskvars in *); (try   fold DEnv_bindings in *); (try   fold DEnv_DSchs in *)
           ; (try   fold DEnv_boundvars in *) ).


Ltac unfold_Env_to_Set :=
           ( (try unfold Env_skvars     ); (try unfold Env_exvars     ); (try unfold Env_Obj_exvars     )
           ; (try unfold Env_bindings     ); (try unfold Env_boundvars     ); (try unfold Env_Schs     ); (try unfold Env_Obj_Schs     ) ).
Tactic Notation "unfold_Env_to_Set" "in" hyp(H) :=
           ( (try unfold Env_skvars in H); (try unfold Env_exvars in H); (try unfold Env_Obj_exvars in H)
           ; (try unfold Env_bindings in H); (try unfold Env_boundvars in H); (try unfold Env_Schs in H); (try unfold Env_Obj_Schs in H) ).
Tactic Notation "unfold_Env_to_Set*" :=
           ( (try unfold Env_skvars in *); (try unfold Env_exvars in *); (try unfold Env_Obj_exvars in *)
           ; (try unfold Env_bindings in *); (try unfold Env_boundvars in *); (try unfold Env_Schs in *); (try unfold Env_Obj_Schs in *) ).

Ltac   fold_Env_to_Set :=
           ( (try   fold Env_skvars     ); (try   fold Env_exvars     ); (try   fold Env_Obj_exvars     )
           ; (try   fold Env_bindings     ); (try   fold Env_boundvars     ); (try   fold Env_Schs     ); (try   fold Env_Obj_Schs     ) ).
Tactic Notation "  fold_Env_to_Set" "in" hyp(H) :=
           ( (try   fold Env_skvars in H); (try   fold Env_exvars in H); (try   fold Env_Obj_exvars in H)
           ; (try   fold Env_bindings in H); (try   fold Env_boundvars in H); (try   fold Env_Schs in H); (try   fold Env_Obj_Schs in H) ).
Tactic Notation "  fold_Env_to_Set*" :=
           ( (try   fold Env_skvars in *); (try   fold Env_exvars in *); (try   fold Env_Obj_exvars in *)
           ; (try   fold Env_bindings in *); (try   fold Env_boundvars in *); (try   fold Env_Schs in *); (try   fold Env_Obj_Schs in *) ).

(** We insist on progress on the autorewrite, such that the unfold is rolled
back if we cannot optimize. We don't rollback if the fold fails because
sometimes it will optimize to something like the empty set, which cannot be
folded (nor should it) *)
Ltac rewr_List_to_Set :=
          (unfold_List_to_Set; progress (autorewrite with List_to_Set); fold_List_to_Set).
Tactic Notation "rewr_List_to_Set" "in" hyp(H) :=
           (unfold_List_to_Set in H; progress (autorewrite with List_to_Set in H); fold_List_to_Set in H).
Tactic Notation "rewr_List_to_Set*" :=
           (unfold_List_to_Set*; progress (autorewrite with List_to_Set in *); fold_List_to_Set*).

Ltac rewr_DEnv_to_Set :=
          (unfold_DEnv_to_Set; progress (autorewrite with DEnv_to_Set); fold_DEnv_to_Set).
Tactic Notation "rewr_DEnv_to_Set" "in" hyp(H) :=
           (unfold_DEnv_to_Set in H; progress (autorewrite with DEnv_to_Set in H); fold_DEnv_to_Set in H).
Tactic Notation "rewr_DEnv_to_Set*" :=
           (unfold_DEnv_to_Set*; progress (autorewrite with DEnv_to_Set in *); fold_DEnv_to_Set*).

Ltac rewr_Env_to_Set :=
          (unfold_Env_to_Set; progress (autorewrite with Env_to_Set); fold_Env_to_Set).
Tactic Notation "rewr_Env_to_Set" "in" hyp(H) :=
           (unfold_Env_to_Set in H; progress (autorewrite with Env_to_Set in H); fold_Env_to_Set in H).
Tactic Notation "rewr_Env_to_Set*" :=
           (unfold_Env_to_Set*; progress (autorewrite with Env_to_Set in *); fold_Env_to_Set*).

Ltac rewr :=
  repeat( rewr_auto || rewr_setprops || rewr_List_to_Set || rewr_DEnv_to_Set || rewr_Env_to_Set ).
Tactic Notation "rewr" "in" hyp(H) :=
  repeat( rewr_auto in H || rewr_setprops in H || rewr_List_to_Set in H || rewr_DEnv_to_Set in H || rewr_Env_to_Set in H).
Tactic Notation "rewr*" :=
  repeat( rewr_auto* || rewr_setprops* || rewr_List_to_Set* || rewr_DEnv_to_Set* || rewr_Env_to_Set*).

(** eqsimpl *)
Ltac eqsimpl := autorewrite with core equiv_simpl.
Tactic Notation "eqsimpl" "in" hyp(H) := autorewrite with core equiv_simpl in H.
Tactic Notation "eqsimpl*" := autorewrite with core equiv_simpl in *.

(** subdist *)
Ltac subdist := autorewrite with core subdist.
Tactic Notation "subdist" "in" hyp(H) := autorewrite with core subdist in H.
Tactic Notation "subdist*" := autorewrite with core subdist in *.

(** norm *)
Ltac norm := autorewrite with core norm.
Tactic Notation "norm" "in" hyp(H) := autorewrite with core norm in H.
Tactic Notation "norm*" := autorewrite with core norm in *.

(** conv *)
Ltac conv := autorewrite with core conv.
Tactic Notation "conv" "in" hyp(H) := autorewrite with core conv in H.
Tactic Notation "conv*" := autorewrite with core conv in *.

(** atom_fresh *)
Ltac fresh_atom := forwards [?x ?NIL]: atom_fresh.
Ltac fresh_atom' L := forwards [?x ?NIL]: atom_fresh L.

(** General fsetdec *)
Ltac fsetdec' := rewr_setprops*;
       match goal with
       | |- AtomSetImpl.Equal _ _ => AtomSetDecide.fsetdec
       | |- DTySI.Equal       _ _ => DTySD.fsetdec
       | |- DSchSI.Equal      _ _ => DSchSD.fsetdec
       | |- DTyPSI.Equal      _ _ => DTyPSD.fsetdec
       | |- DSchPSI.Equal     _ _ => DSchPSD.fsetdec
       (* | |- TySI.Equal        _ _ => TySD.fsetdec *)
       | |- SchSI.Equal       _ _ => SchSD.fsetdec
       (* | |- TyPSI.Equal       _ _ => TyPSD.fsetdec *)
       (* | |- SchPSI.Equal      _ _ => SchPSD.fsetdec *)

       | |- AtomSetImpl.Subset _ _ => AtomSetDecide.fsetdec
       | |- DTySI.Subset       _ _ => DTySD.fsetdec
       | |- DSchSI.Subset      _ _ => DSchSD.fsetdec
       | |- DTyPSI.Subset      _ _ => DTyPSD.fsetdec
       | |- DSchPSI.Subset     _ _ => DSchPSD.fsetdec
       (* | |- TySI.Subset        _ _ => TySD.fsetdec *)
       | |- SchSI.Subset       _ _ => SchSD.fsetdec
       (* | |- TyPSI.Subset       _ _ => TyPSD.fsetdec *)
       (* | |- SchPSI.Subset      _ _ => SchPSD.fsetdec *)

       | |- AtomSetImpl.In _ _ => AtomSetDecide.fsetdec
       | |- DTySI.In       _ _ => DTySD.fsetdec
       | |- DSchSI.In      _ _ => DSchSD.fsetdec
       | |- DTyPSI.In      _ _ => DTyPSD.fsetdec
       | |- DSchPSI.In     _ _ => DSchPSD.fsetdec
       (* | |- TySI.In        _ _ => TySD.fsetdec *)
       | |- SchSI.In       _ _ => SchSD.fsetdec
       (* | |- TyPSI.In       _ _ => TyPSD.fsetdec *)
       (* | |- SchPSI.In      _ _ => SchPSD.fsetdec *)
       end.

Ltac fsetdec'' := ( AtomSetDecide.fsetdec
                  || DTySD.fsetdec
                  || DSchSD.fsetdec
                  || DTyPSD.fsetdec
                  || DSchPSD.fsetdec
                  (* || TySD.fsetdec *)
                  || SchSD.fsetdec
                  (* || TyPSD.fsetdec *)
                  (* || SchPSD.fsetdec *)
                 ).

Ltac fsetdec_debug := ( (AtomSetDecide.fsetdec; idtac "AtomSetDecide.fsetdec")
                      || (DTySD.fsetdec; idtac "DTySD.fsetdec")
                      || (DSchSD.fsetdec; idtac "DSchSD.fsetdec")
                      || (DTyPSD.fsetdec; idtac "DTyPSD.fsetdec")
                      || (DSchPSD.fsetdec; idtac "DSchPSD.fsetdec")
                      || (TySD.fsetdec; idtac "TySD.fsetdec")
                      || (SchSD.fsetdec; idtac "SchSD.fsetdec")
                      || (TyPSD.fsetdec; idtac "TyPSD.fsetdec")
                      || (SchPSD.fsetdec; idtac "SchPSD.fsetdec")
                     ).

(*** Forwards *)
Tactic Notation "forwards>" ":" constr(E) :=
  forwards: ZifyClasses.rew_iff E.
Tactic Notation "forwards>" ":" constr(E0)
 constr(A1) :=
  forwards: ZifyClasses.rew_iff E0 A1.
Tactic Notation "forwards>" ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards: ZifyClasses.rew_iff E0 A1 A2.
Tactic Notation "forwards>" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards: ZifyClasses.rew_iff E0 A1 A2 A3.
Tactic Notation "forwards>" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards: ZifyClasses.rew_iff E0 A1 A2 A3 A4.

Tactic Notation "forwards>" simple_intropattern(I) ":" constr(E0) :=
  forwards I: ZifyClasses.rew_iff E0.
Tactic Notation "forwards>" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards I: ZifyClasses.rew_iff E0 A1 A2.
Tactic Notation "forwards>" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards I: ZifyClasses.rew_iff E0 A1 A2 A3.
Tactic Notation "forwards>" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards I: ZifyClasses.rew_iff E0 A1 A2 A3 A4.

Tactic Notation "forwards<" ":" constr(E) :=
  forwards: ZifyClasses.rew_iff_rev E.
Tactic Notation "forwards<" ":" constr(E0)
 constr(A1) :=
  forwards: ZifyClasses.rew_iff_rev E0 A1.
Tactic Notation "forwards<" ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards: ZifyClasses.rew_iff_rev E0 A1 A2.
Tactic Notation "forwards<" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards: ZifyClasses.rew_iff_rev E0 A1 A2 A3.
Tactic Notation "forwards<" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards: ZifyClasses.rew_iff_rev E0 A1 A2 A3 A4.

Tactic Notation "forwards<" simple_intropattern(I) ":" constr(E0) :=
  forwards I: ZifyClasses.rew_iff_rev E0.
Tactic Notation "forwards<" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards I: ZifyClasses.rew_iff_rev E0 A1 A2.
Tactic Notation "forwards<" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards I: ZifyClasses.rew_iff_rev E0 A1 A2 A3.
Tactic Notation "forwards<" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards I: ZifyClasses.rew_iff_rev E0 A1 A2 A3 A4.
