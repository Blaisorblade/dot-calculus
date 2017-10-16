Set Implicit Arguments.

Require Import LibLN.
Require Import Definitions.
Require Import OperationalSemantics.

Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.
Require Import Omega.
Require Import Coq.Program.Wf.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Wellfounded.Lexicographic_Product.

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
    (* | typ_mem t1 t2 => S (tsize_flat_typ t1 + tsize_flat_typ t2)	 *)
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

(** Reduction in an empty context *)
Notation "t '|->' u" := (empty [t |-> u]) (at level 50).

(* Definition red_n (n : nat) (t : trm) (v : val) := *)
(*   match n with *)
(*   | 0 -> t := *)
(* Inductive red_n (n : nat) : (t : trm) (v : val) : Prop := *)
Inductive red_n : nat -> sto -> trm -> val -> Prop :=
| Red0 : forall e v, red_n 0 e (trm_val v) v
| RedS : forall n e t1 t2 v, red e t1 t2 -> red_n n e t2 v -> red_n (S n) e t1 v.

Require Import Binding.

Definition nvsetFam := typ -> nvset.

Definition pre_exp_type (val_type: nvsetFam)  (T:typ) (n:nat) (t : trm) := False.

(* Since the semantics *does* use a store (ahem, environment) this *should* be
 * parameterized by an environment as well. *)
Program Fixpoint val_type (T:typ) (k:nat) (v:val)
        {measure (existT (fun _ => nat) (tsize_flat_typ T) k) (termRel)}: Prop :=
  (* let *)
  (*   exp_type (T : typ) (k : nat) (t: trm) := *)
  (*   forall v j, j < k -> *)
  (*          red_n j empty t v -> *)
  (*          val_type T (k - j) v *)
  (* in *)
  match v, T with
     | val_lambda T0 t, typ_all T1 T2 =>
       let
         exp_type_t2 (k : nat) (t: trm) :=
         forall v j, j < k ->
                red_n j empty t v ->
                val_type T2 (k - j) v
       in
       lc_at_typ 0 T1 /\ lc_at_typ 1 T2 /\
       forall j va x,
         j < k ->
         val_type T1 j va ->
         x \notin fv_trm t ->
         (* This line is especially fishy: is this building an application to
          * reduce, or reducing it already? Will this term take 1 step too much to
          * reduce? It seems not, this just increases the depth of the
          * derivation.
          * Still, let's fix this with a proper definition. *)
         exp_type_t2 j (trm_let (trm_val va) t)
         (* exists v, red_n k empty (trm_let (trm_val va) t) v /\ *)
         (* exists v, red_n k empty (trm_let (trm_val va) t) v /\ *)
         (*      (forall k, val_type (open_typ x T2) k v) *)
     (* exists (jj:nvset) v, t |-> v /\ *)
     (*                   (forall k, exp_type (open_typ x T2) k v) *)
     | _, typ_and T1 T2 =>
       val_type T1 k v /\ val_type T2 k v
     (* | _, TBind T1 => *)
     (*   val_type *)
     (*   closed 1 (length GH) (length env) T1 /\ *)
     | _,_ =>
       False
  end.

(* expr_type (T : typ) (n : nat) (t : trm) := False. *)


(* Program Fixpoint val_type (env: list nvset) (GH:list nvset) (T:typ) (n:nat) (v:val) *)
(*         {measure (existT (fun _ => nat) (tsize_flat_typ T) n) (termRel)}: Prop := *)
(*   match v,T with *)
(*     | val_lambda T0 t, typ_all T1 T2 => *)
(*       lc_at_typ 0 T1 /\ lc_at_typ 1 T2 *)
(*       (* /\ *) *)
(*     (*   forall jj vx, *) *)
(*     (*     (forall kx, (kx <= n -> val_type env GH T1 kx vx)) -> *) *)
(*     (*     exists (jj2:nvset) v, t v /\ (forall k, val_type env (jj::GH) (open_typ (avar_f (length GH)) T2) k v) *) *)
(*     | _, typ_and T1 T2 => *)
(*       val_type env GH T1 n v /\ val_type env GH T2 n v *)
(*     (* | _, TBind T1 => *) *)
(*     (*   val_type *) *)
(*     (*   closed 1 (length GH) (length env) T1 /\ *) *)
(*     | _,_ => *)
(*       False *)
(*   end. *)

Solve All Obligations.
Show Obligation Tactic.
Next Obligation. unfold termRel. apply left_lex. Tactics.program_simpl; try omega. Qed.
Next Obligation. unfold termRel. apply left_lex. Tactics.program_simpl; try omega. Qed.
Next Obligation. unfold termRel. apply left_lex. Tactics.program_simpl; try omega. Qed.
Next Obligation. unfold termRel. apply left_lex. Tactics.program_simpl; try omega. Qed.
Ltac discriminatePlus := (split; intros; let Xf := fresh "Habs" in intro Xf; destruct Xf; discriminate).
Obligation Tactic := discriminatePlus.
Solve All Obligations.
(* Next Obligation. split; intros; intro Habs; destruct Habs; discriminate. Qed. *)
(* Next Obligation. split; intros; intro Habs; destruct Habs; discriminate. Qed. *)
(* Next Obligation. split; intros; intro Habs; destruct Habs; discriminate. Qed. *)
(* Next Obligation. *)

(*                  apply left_lex. Tactics.program_simpl; try omega. Qed. *)
(*                  try unfold open; try rewrite <-open_preserves_size; try omega. Qed. *)

(* Next Obligation. unfold termRel. apply left_lex. Tactics.program_simpl; try unfold open; try rewrite <-open_preserves_size; try omega. Qed. *)

(* Next Obligation. unfold termRel; apply left_lex; Tactics.program_simpl. try unfold open; try rewrite <-open_preserves_size; omega. Qed. *)
(* Next Obligation. unfold termRel. apply left_lex; Tactics.program_simpl; try unfold open; try rewrite <-open_preserves_size; omega. Qed. *)

(* Next Obligation. split; Tactics.program_simpl; try unfold open; try rewrite <-open_preserves_size. Qed. *)

(* Next Obligation. split; Tactics.program_simpl; try unfold open; try rewrite <-open_preserves_size. Qed. *)

(* Next Obligation. split; Tactics.program_simpl; try unfold open; try rewrite <-open_preserves_size. Qed. *)

(* Next Obligation. split; Tactics.program_simpl; try unfold open; try rewrite <-open_preserves_size. Qed. *)

(* Next Obligation. split; Tactics.program_simpl; try unfold open; try rewrite <-open_preserves_size. Qed. *)

(* Next Obligation. split; Tactics.program_simpl; try unfold open; try rewrite <-open_preserves_size. Qed. *)

(* Next Obligation. split; Tactics.program_simpl; try unfold open; try rewrite <-open_preserves_size. Qed. *)
(* (* Next Obligation. *) *)
(* Next Obligation. split; Tactics.program_simpl; try unfold open; try rewrite <-open_preserves_size. Qed. *)

(* Next Obligation. split; Tactics.program_simpl; try unfold open; try rewrite <-open_preserves_size. Qed. *)
(* Next Obligation. split; Tactics.program_simpl; try unfold open; try rewrite <-open_preserves_size. Qed. *)