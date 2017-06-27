Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Inert_types.
Require Import Invertible_typing.
Require Import Some_lemmas.

Lemma sel_replacement: forall G p A S U,
    inert G ->
    G |-#\||/ p : typ_rcd { A >: S <: U } ->
    G |-# typ_path p A <: U /\
    G |-# S <: typ_path p A.
Proof.
  introv Hi Hty.
  lets Hp: (tight_to_invertible_p Hi Hty).
  destruct (invertible_to_precise_typ_dec Hi Hp) as [T [Ht [Hs1 Hs2]]].
  split.
  - apply subtyp_sel1_t in Ht. apply* subtyp_trans_t.
  - apply subtyp_sel2_t in Ht. apply* subtyp_trans_t. apply* path_typing_norm_tight.
Qed.

Lemma sngl_replacement: forall G p r A S U,
    inert G ->
    G |-#\||/ p: typ_sngl r ->
    G |-# trm_path r: typ_rcd {A >: S <: U} ->
    G |-# typ_path r A <: typ_path p A /\ G |-# typ_path p A <: typ_path r A.
Proof.
  introv Hi Hp Hr. lets Hil: (tight_to_invertible_p Hi Hp).
  lets Hs: (invertible_to_precise_sngl Hi Hil). split.
  - destruct Hs as [Ht | Heq]. apply* subtyp_sngl_sel2_t. subst*.
  - destruct Hs as [Ht | Heq]. apply* subtyp_sngl_sel1_t. subst*.
Qed.

Lemma general_to_tight: forall G0, inert G0 ->
  (forall G t T,
     G |- t : T ->
     G = G0 ->
     G |-# t : T) /\
  (forall G p T,
     G |-\||/ p: T ->
     G = G0 ->
     G |-#\||/ p: T) /\
  (forall G S U,
     G |- S <: U ->
     G = G0 ->
     G |-# S <: U) /\
  (forall G p,
     norm G p ->
     G = G0 ->
     norm_t G p).
Proof.
  intros G0 Hi.
  apply ts_mutind; intros; subst; eauto; specialize (H eq_refl).
  - destruct m.
    assert (G0 |-# typ_rcd {a [strong] T} <: typ_rcd {a [gen] T}) as Hsg by auto.
    lets Hs: (ty_sub_t). specialize (Hs _ _ _ _ H Hsg). apply* ty_fld_elim_t.
    apply* ty_fld_elim_t.
  - apply* sel_replacement.
  - apply* sel_replacement.
  - apply* sngl_replacement.
  - specialize (H0 eq_refl). lets Hn: (path_typing_norm_tight H).
    apply (sngl_replacement Hi H H0).
Qed.

Lemma general_to_tight_typing: forall G t T,
  inert G ->
  G |- t : T ->
  G |-# t : T.
Proof.
  intros. apply* general_to_tight.
Qed.

Lemma general_to_tight_norm: forall G p,
    inert G ->
    G |- p \||/ ->
    G |-# p \||/.
Proof.
  intros. apply* general_to_tight.
Qed.
