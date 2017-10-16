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

Definition nvset := nat -> val -> Prop.

Definition termRel := lexprod nat (fun _ => nat) lt (fun _ => lt).
Hint Unfold termRel.

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

Definition val_type_measure T k := (existT (fun _ => nat) (tsize_flat_typ T) k).
Hint Unfold val_type_measure.

(* Since the semantics *does* use a store (ahem, environment) this *should* be
 * parameterized by an environment as well. *)

(* Beware: We just ignore type annotations in values, as usual in SILRs. *)
(* Also: should probably use cofinite quantification, but not really sure why it's better than explicit free variable sets. *)
Program Fixpoint val_type (env: sto) (T: typ) (n: nat) (v: val)
        {measure (val_type_measure T n) (termRel)}: Prop :=
  (* Preliminary local closure hypotheses: *)
  lc_sto env /\ lc_at_typ (length env) T /\
  (* Really? *)
  lc_val v /\
  (* More likely. *)
  (* lc_at_val (length env) v /\ *)
  let
    exp_type (env1 : sto) (T1 : typ) (k : nat) (t: trm) (H : termRel (val_type_measure T1 k) (val_type_measure T n)) :=
    forall v j,
      j < k ->
      red_n j env1 t v ->
      val_type env1 T1 (k - j) v
  in
  match v, T with
     | val_lambda T0 t, typ_all T1 T2 =>
       lc_at_typ (length env) T1 /\ lc_at_typ (S (length env)) T2 /\
       forall k va x,
         x \notin fv_trm t ->
         k < n -> val_type env T1 k va ->
         exp_type (env & x ~ v) (open_typ x T2) k t _
     | _, typ_and T1 T2 =>
       val_type env T1 n v /\ val_type env T2 n v
     | _, typ_top =>
       True
     | _, typ_bot =>
       False
     | val_new T0 defs, typ_rcd (dec_typ l TL TU) =>
       exists T1,
       get_def (label_typ l) defs = Some (def_typ l T1) /\
       True
         (* Check the bounds are respected. This requires fixing the termination
         * order used here! The one on paper seems fine, but this one seems
         different by mistake. *)
       (* forall v', *)
       (*   (val_type env TL (n - 1) v' -> val_type env T1 (n - 1) v') /\ *)
       (*   (val_type env T1 (n - 1) v' -> val_type env TU (n - 1) v') *)
     | val_new T0 defs, typ_rcd (dec_trm l T1) =>
       exists t,
       get_def (label_trm l) defs = Some (def_trm l t) /\
       forall x, x \notin fv_trm t ->
       exp_type (env & x ~ v) (open_typ x T1) (n - 1) t _
     | _, typ_sel (avar_f x )L =>
       exists v, binds x v env /\
       False
     (* | typ_sel  : avar -> typ_label -> typ *)
     (* | typ_bnd  : typ -> typ *)
     | _,_ =>
       False
  end.

Ltac smaller_calls :=
  Tactics.program_simpl;
  autounfold; apply left_lex;
  unfold open_typ; try rewrite open_preserves_size_typ; simpl; omega.
Ltac discriminatePlus := repeat split; intros; let Habs := fresh "Habs" in intro Habs; destruct Habs; discriminate.

Next Obligation.
  (* Show that recursive calls in exp_type are well-founded. *)
  autounfold with *.
  inverts H.
  - apply left_lex. assumption.
  - apply right_lex. omega.
Qed.

(* Show that other recursive calls are well-founded. *)
Solve Obligations with smaller_calls.
(* Show that different branches are disjoint. *)
Solve Obligations with discriminatePlus.

Ltac ev := repeat match goal with
                  | H: exists _, _ |- _ => destruct H
                  | H: _ /\  _ |- _ => destruct H
                  end.

Lemma val_type_unfold: forall (env: sto) (T: typ) (n: nat) (v: val),
                         val_type env T n v =
  (* Copy-pasted. *)
  (* Preliminary local closure hypotheses: *)
  (lc_sto env /\ lc_at_typ (length env) T /\
  (* Really? *)
  lc_val v /\
  (* More likely. *)
  (* lc_at_val (length env) v /\ *)
  let
    exp_type (env1 : sto) (T1 : typ) (k : nat) (t: trm) (H : termRel (val_type_measure T1 k) (val_type_measure T n)) :=
    forall v j,
      j < k ->
      red_n j env1 t v ->
      val_type env1 T1 (k - j) v
  in
  match v, T with
     | val_lambda T0 t, typ_all T1 T2 =>
       lc_at_typ (length env) T1 /\ lc_at_typ (S (length env)) T2 /\
       forall k va x,
         x \notin fv_trm t ->
         k < n -> val_type env T1 k va ->
         exists H,
         exp_type (env & x ~ v) (open_typ x T2) k t H
     | _, typ_and T1 T2 =>
       val_type env T1 n v /\ val_type env T2 n v
     | _, typ_top =>
       True
     | _, typ_bot =>
       False
     | val_new T0 defs, typ_rcd (dec_typ l TL TU) =>
       exists T1,
       get_def (label_typ l) defs = Some (def_typ l T1) /\
       True
         (* Check the bounds are respected. This requires fixing the termination
         * order used here! The one on paper seems fine, but this one seems
         different by mistake. *)
       (* forall v', *)
       (*   (val_type env TL (n - 1) v' -> val_type env T1 (n - 1) v') /\ *)
       (*   (val_type env T1 (n - 1) v' -> val_type env TU (n - 1) v') *)
     | val_new T0 defs, typ_rcd (dec_trm l T1) =>
       exists t,
       get_def (label_trm l) defs = Some (def_trm l t) /\
       forall x, x \notin fv_trm t ->
            exists H,
       exp_type (env & x ~ v) (open_typ x T1) (n - 1) t H
     | _, typ_sel (avar_f x )L =>
       exists v, binds x v env /\
       False
     (* | typ_sel  : avar -> typ_label -> typ *)
     (* | typ_bnd  : typ -> typ *)
     | _,_ =>
       False
  end).
Proof.
  intros.
  unfold val_type at 1.
  unfold val_type_func.
  unfold_sub val_type (val_type env T n v). simpl.
  fequals. fequals. fequals.
  Require Import Program.
  dependent induction T;
  dependent destruction v; simpl; try reflexivity.
  - destruct d; eauto.
    apply prop_ext; split; intro H; destruct H as [t2 H']; eexists t2.
    + ev. split; [ assumption | intros * Hxfresh ].
      eexists.
      * smaller_calls.
      * introv Hle Hred.
        apply (H0 x Hxfresh v j Hle Hred).
    + ev. split; [ assumption | intros * Hxfresh * Hle Hred ].
      lets Hx: (H0 x Hxfresh).
      clear H0.
      destruct Hx as [Hlex H1].
      apply (H1 v j Hle Hred).
  - destruct a; auto.
  - destruct a; auto.
  - fequals. fequals.
    apply prop_ext; split; intro H; intros * Hxfresh * Hle Hva.
    (* Use extensionality the Agda way and keep proving equality, like Yann does. *)
    + eexists.
      * smaller_calls.
      *
        intros * Hle1 Hred.
        eapply H with (va := va); auto.
    + (* Here, we must use Hva
       *)
      intros * Hle1.
      intro Hred.
      simpl.
      lets Hts : (H k va x Hxfresh Hle Hva).
      clear Hva.
      (* Half of unfold_sub *)
      rewrite fix_sub_eq_ext. repeat fold_sub val_type. simpl proj1_sig.
      (* repeat fold_sub val_type in Hva. *)
      (* apply IHT2. *)

      simpl in *.
      destruct Hts as [Hterm Hres].
      assert (Hv:
         val_type (env & x ~ val_lambda t t0) (open_typ x T2) (k - j) v).
      * auto.
      *
        (* apply IHT2 in Hv. *)
        unfold val_type at 1 in Hv.
        unfold val_type_func in Hv.
        rewrite fix_sub_eq_ext in Hv.
        (* unfold_sub val_type (val_type env T n v).
           simpl. *)
        inverts Hv. simpl in *.
        clear Hres.
        ev.
        repeat split; auto.
Qed.
