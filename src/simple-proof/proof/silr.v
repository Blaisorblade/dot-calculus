Set Implicit Arguments.

Require Import Arith.Wf_nat.
Require Import Coq.Program.Wf.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Wellfounded.Lexicographic_Product.

Require Import LibLN.
Require Import Definitions.
Require Import Binding.
Require Import OperationalSemantics.

Definition nvset := nat -> val -> Prop.

Definition termRel := lexprod nat (fun _ => nat) lt (fun _ => lt).
Lemma wf_termRel : well_founded termRel.
Proof.
 apply wf_lexprod; try intro; apply lt_wf.
Qed.

Hint Resolve wf_termRel.

Fixpoint tsize_flat_typ(T: typ) :=
  match T with
    | typ_top => 1
    | typ_bot => 1
    | typ_all t1 t2 => S (tsize_flat_typ t1 + tsize_flat_typ t2)
    | typ_sel _ _ => 1
    | typ_rcd d => tsize_flat_dec d
    | typ_bnd t => S (tsize_flat_typ t)
    | typ_and T1 T2 => S (tsize_flat_typ T1 + tsize_flat_typ T2)
  end
with tsize_flat_dec(d : dec) :=
  match d with
  | dec_typ L T U => S (tsize_flat_typ T + tsize_flat_typ U)
  | dec_trm m T   => S (tsize_flat_typ T)
  end.

Lemma open_preserves_size_typ: forall T x j,
  tsize_flat_typ (open_rec_typ j x T) = tsize_flat_typ T
with open_preserves_size_dec: forall d x j,
  tsize_flat_dec (open_rec_dec j x d) = tsize_flat_dec d.
Proof.
  - induction T; intros; simpl; try reflexivity; erewrite ? open_preserves_size_dec; erewrite ? open_preserves_size_typ; try reflexivity.
  - induction d; intros; simpl; try reflexivity; erewrite ? open_preserves_size_dec; erewrite ? open_preserves_size_typ; try reflexivity.
Qed.

Inductive red_n : nat -> sto -> trm -> val -> Prop :=
| Red0 : forall e v, red_n 0 e (trm_val v) v
| RedS : forall n e t1 t2 v, red e t1 t2 -> red_n n e t2 v -> red_n (S n) e t1 v.

Definition nvsetFam := typ -> nvset.

Definition pre_exp_type (val_type: nvsetFam)  (T:typ) (n:nat) (t : trm) := False.

(* Since the semantics *does* use a store (ahem, environment) this *should* be
 * parameterized by an environment as well. *)

(* Beware: We just ignore type annotations in values, as usual in SILRs. *)

Program Fixpoint val_type (env: sto) (T:typ) (k:nat) (v:val)
        {measure (existT (fun _ => nat) (tsize_flat_typ T) k) (termRel)}: Prop :=
  lc_sto env /\
  (* let *)
  (*   exp_type (T : typ) (k : nat) (t: trm) := *)
  (*   forall v j, j < k -> *)
  (*          red_n j empty t v -> *)
  (*          val_type T (k - j) v *)
  (* in *)
  match v, T with
     | val_lambda T0 t, typ_all T1 T2 =>
       let
         exp_type_t2 x (env : sto) (k : nat) (t: trm) :=
         forall v j, j < k ->
                red_n j env t v ->
                val_type env (open_typ x T2) (k - j) v
       in
       lc_at_typ (length env) T1 /\ lc_at_typ (S (length env)) T2 /\
       forall j va x,
         j < k ->
         val_type env T1 j va ->
         x \notin fv_trm t ->
         exp_type_t2 x (env & ((x ~ v))) j t
     | _, typ_and T1 T2 =>
       val_type env T1 k v /\ val_type env T2 k v
     | _,_ =>
       False
  end.

Ltac smaller_calls :=
  Tactics.program_simpl;
  unfold termRel; apply left_lex;
  try unfold open_typ; try rewrite open_preserves_size_typ; simpl; try omega.
Ltac discriminatePlus := split; intros; let Habs := fresh "Habs" in intro Habs; destruct Habs; discriminate.
Solve Obligations with smaller_calls.
Solve Obligations with discriminatePlus.
