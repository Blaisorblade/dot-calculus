Set Implicit Arguments.

Require Import Arith.Wf_nat.
Require Import Coq.Program.Wf.
Import WfExtensionality.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Wellfounded.Lexicographic_Product.

Require Import LibLN.
Require Import Definitions.
Require Import Binding.
Require Import OperationalSemantics.

Require Import silr.

Require Import Program.

Definition nvset_monotone (nv : nvset) := forall j k v, j < k -> nv k v -> nv j v.
Hint Unfold nvset_monotone.

Ltac easy := (intuition; simpl in * |- *; try congruence; eauto).

Ltac inverse H := (inversion H; subst).

Ltac use H := (eapply H; easy).

Ltac break H := (destruct H; intuition).

Ltac remark_by H := (generalize H; intro). (* FIXME: Give a name. *)

Ltac match_case_analysis :=
  repeat
    match goal with
    | H : context f [match ?x with _ => _ end] |- _ =>
      destruct x; try solve [inverse H]
    end.

Ltac match_case_analysis_eauto :=
  repeat
    match goal with
    | H : context f [match ?x with _ => _ end] |- _ =>
      destruct x; try solve [inverse H; eauto]
    end.

Program Lemma val_type_monotone :
  forall T env,
    lc_sto env -> lc_at_typ (length env) T ->
       nvset_monotone (val_type env T).
Proof.
  autounfold.
  intros * HlcEnv HlcT * Hle Hval_k_v.
  rewrite val_type_unfold in Hval_k_v |- *.
  destruct Hval_k_v as [ Hlc_sto_env [ Hlc_typ_T [ Hlc_val_v Hv ] ] ].
  repeat split; try assumption.

  destruct v; destruct T; simpl; auto; match_case_analysis_eauto; simpl in *.
  - easy; ev; try eexists. split; eauto.
    introv Hxfresh.
    lets H1 : H0 Hxfresh.
    ev. eexists.
    + skip.
    + introv Hjle Hred.
      lets H2 : H1 v j0 Hred. omega.
      assert (j - 1 - j0 < k - 1 - j0) by omega.

      assert (HmonInd: (val_type (env & x0 ~ val_new t d) (open_typ x0 t1) (k - 1 - j0) v) ->
              (val_type (env & x0 ~ val_new t d) (open_typ x0 t1) (j - 1 - j0) v)) by skip.
      apply HmonInd. assumption.
  - (* Would follow with an inductive hypothesis, so let's skip. *)
    skip.
  - (* Ditto *)
    skip.
  -
    destruct Hv as [Hv1 Hv2]; split; try assumption.
    destruct Hv2 as [Hv3 Hv4]; split; try assumption.
    intros.
    assert (Hk0k : k0 < k) by omega.
    lets (rel & HvSpec): (Hv4 k0 va x H Hk0k) __. assumption.
    exists.
    +
      (* Prove term_rel from termRel. Probably this should be a tactic? *)
      unfold termRel, val_type_measure, open_typ in rel |- *. simpl in rel |- *.
      rewrite open_preserves_size_typ in rel |- *.
      inverse rel.
      * apply left_lex. omega.
      * apply right_lex. omega.
    +
      Ltac specialize_hyp_for_thesis H1 :=
        let x := fresh "v" in
        let H2 := fresh "H" in
        intro x; generalize (H1 x); clear H1; intro H2; try specialize_hyp_for_thesis H2.
      specialize_hyp_for_thesis HvSpec.
      assumption.

      (* (* intro v; remark_by (HvSpec v). *) *)
      (* (* intro v; remark_by (HvSpec v). *) *)
      (* (* intro v. *) *)
      (* (* remark_by  *) *)
      (* (* pose (H2 := HvSpec v). *) *)
      (* (* apply HvSpec in v. *) *)
      (* (* (let n := fresh in intro n; apply HvSpec in n). *) *)

      (* case_if_eq j (k - 1). *)
      (* * skip. *)
      (* * apply H2. *)
      (*   apply H1. *)
      (*   omega. *)


  (* (* pose (Hmeasure := termRel (val_type_measure T j) (val_type_measure T k)). *) *)
  (* (* program_solve_wf. *) *)
  (* (* autounfold in *. *) *)
  (* (* program_simpl. *) *)
  (* (* generalize (termRel (val_type_measure T j) (val_type_measure T k)); intro Hmeasure. *) *)
  (* (* induction Hmeasure. *) *)
  (* (* dependent induction Hv. *) *)
  (* dependent induction HlcT; *)
  (* dependent destruction v; auto. *)
  (* - destruct D; simpl; destruct H2; ev; *)
  (*     exists; intuition eauto. *)
  (*   exists. smaller_calls. *)
  (*   intuition eauto. *)
Admitted.

(* TODO:
 * checkout Chlipala's book.
 *)


Definition Contractive := True.