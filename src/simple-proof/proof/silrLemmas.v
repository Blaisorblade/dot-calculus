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

Definition nvset_monotone (nv : nvset) := forall j k v, j <= k -> nv k v -> nv j v.
Hint Unfold nvset_monotone.

Program Lemma val_type_monotone :
  forall T env,
    lc_sto env -> lc_at_typ (length env) T ->
       nvset_monotone (val_type env T).
Proof.
  autounfold.
  intros * HlcEnv HlcT * Hle Hval_k_v.
  rewrite val_type_unfold in Hval_k_v |- *.
  dependent induction HlcT;
  dependent destruction v; repeat split; ev; auto.
  - destruct D; simpl; destruct H2; ev;
      exists; intuition eauto.
    exists. smaller_calls.
    intuition eauto.
Admitted.


Definition Contractive := True.