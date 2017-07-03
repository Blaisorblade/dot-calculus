(** printing |-     %\vdash%         #&vdash;#                     *)
(** printing /-     %\vdash%         #&vdash;#                     *)
(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** printing ->     %\rightarrow%    #&rarr;#                      *)
(** printing =>     %\Rightarrow%    #&rArr;#                      *)
(** printing ~~     %\~\~%           #~~#                          *)
(** printing /\     %\wedge%         #&and;#                       *)
(** printing \/     %\vee%           #&or;#                        *)
(** printing forall %\forall%        #&forall;#                    *)
(** printing exists %\exists%        #&exist;#                     *)
(** printing lambda %\lambda%        #&lambda;#                    *)
(** printing mu     %\mu%            #&mu;#                        *)
(** printing nu     %\nu%            #&nu;#                        *)
(** printing Gamma  %\Gamma%         #&Gamma;#                     *)
(** printing top    %\top%           #&#8868;#                     *)
(** printing bottom %\bot%           #&perp;#                      *)
(** printing <>     %\ne%            #&ne;#                        *)
(** printing notin  %\notin%         #&notin;#                     *)
(** printing isin   %\in%            #&isin;#                      *)
(** remove printing ~ *)

(** This module reasons about the precise types of variables in inert contexts. *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Helper_lemmas.

(** * Precise Flow *)
(** Given a variable [x] is bound to type [T] in an inert environment [Gamma],
    the [precise_flow] relation describes all the types [U] that [x] can
    derive through precise typing ([|-!], see [ty_trm_p]).
    If [precise_flow x Gamma T U], then [Gamma(x) = T] and [Gamma |-! x: U].   #<br>#
    For example, if [Gamma(x) = mu(x: {a: T} /\ {B: S..U})], then we can derive the following
    precise flows for [x]:                                                     #<br>#
    [precise_flow x Gamma mu(x: {a: T} /\ {B: S..U}) mu(x: {a: T} /\ {B: S..U}]  #<br>#
    [precise_flow x Gamma mu(x: {a: T} /\ {B: S..U}) {a: T} /\ {B: S..U}]        #<br>#
    [precise_flow x Gamma mu(x: {a: T} /\ {B: S..U}) {a: T}]                    #<br>#
    [precise_flow x Gamma mu(x: {a: T} /\ {B: S..U}) {B: S..}]. *)
Inductive precise_flow : var -> ctx -> typ -> typ -> Prop :=
  | pf_bind : forall x G T,
      binds x T G ->
      precise_flow x G T T
  | pf_open : forall x G T U,
      precise_flow x G T (typ_bnd U) ->
      precise_flow x G T (open_typ x U)
  | pf_and1 : forall x G T U1 U2,
      precise_flow x G T (typ_and U1 U2) ->
      precise_flow x G T U1
  | pf_and2 : forall x G T U1 U2,
      precise_flow x G T (typ_and U1 U2) ->
      precise_flow x G T U2.

Hint Constructors precise_flow.

(** If [precise_flow x Gamma T U] then [Gamma(x) = T]. *)
Lemma pf_binds: forall G x T U,
    precise_flow x G T U ->
    binds x T G.
Proof.
  introv Pf. dependent induction Pf; auto.
Qed.

(** Introduces [precise_flow], given a variable's precise type. *)
Lemma precise_flow_lemma : forall U G x,
    G |-! trm_var (avar_f x) : U ->
    exists T, precise_flow x G T U.
Proof.
  introv H. dependent induction H; try (destruct* (IHty_trm _ eq_refl));
              try (destruct* (IHty_trm_p _ eq_refl)); eauto.
Qed.

(** If [Gamma(x) = forall(S)T], then [x]'s precise type can be only [forall(S)T]. *)
Lemma precise_flow_all_inv : forall p G S T U,
    precise_flow p G (typ_all S T) U ->
    U = typ_all S T.
Proof.
  introv Hpf.
  dependent induction Hpf; auto;
    specialize (IHHpf S T eq_refl); inversion IHHpf.
Qed.

(** The precise type of a value is inert. *)
Lemma precise_inert_typ : forall G v T,
    G |-! trm_val v : T ->
    inert_typ T.
Proof.
  introv Ht. inversions Ht; constructor; rename T0 into T.
  pick_fresh z. assert (Hz: z \notin L) by auto. specialize (H1 z Hz).
  pose proof (ty_defs_record_type H1).
  assert (Hz': z \notin fv_typ T) by auto.
  apply (record_type_open T Hz' H).
Qed.

(** The following two lemmas say that the type to which a variable is bound in an inert context is inert. *)
Lemma binds_inert : forall G x T,
    binds x T G ->
    inert G ->
    inert_typ T.
Proof.
  introv Bi Hinert. induction Hinert.
  - false * binds_empty_inv.
  - destruct (binds_push_inv Bi).
    + destruct H1. subst. assumption.
    + destruct H1. apply (IHHinert H2).
Qed.

(** See [binds_inert]. *)
Lemma pf_inert_T : forall G p T U,
    inert G ->
    precise_flow p G T U ->
    inert_typ T.
Proof.
  introv Hi Pf. induction Pf; eauto.
  apply (binds_inert H Hi).
Qed.

(** The following two lemmas say that if a variable is bound to a recursive
    type [mu(x: T)] in an inert context, then [T] is a record type (i.e.
    it is an intersection of declarations, among which the type declarations
    have equal bounds). *)
Lemma inert_typ_bnd_record : forall G x T,
    inert G ->
    binds x (typ_bnd T) G ->
    record_type T.
Proof.
  introv Bi Hgd.
  pose proof (binds_inert Hgd Bi).
  dependent induction H.
  assumption.
Qed.

(** See [inert_typ_bnd_record] *)
Lemma pf_rcd_T : forall G p T U,
    inert G ->
    precise_flow p G (typ_bnd T) U ->
    record_type T.
Proof.
  introv Hi Pf. apply pf_inert_T in Pf; inversions Pf; assumption.
Qed.

(** If [Gamma(x) = mu(x: T)], then [x]'s precise type can be only [mu(x: T)]
     or a record type. *)
Lemma pf_inert_or_rcd : forall G x T U,
    inert G ->
    precise_flow x G (typ_bnd T) U ->
    U = typ_bnd T \/ record_type U.
Proof.
  introv Hi Pf.
  dependent induction Pf; try solve [left*].
  - specialize (IHPf T Hi eq_refl). destruct IHPf as [eq | r].
    * inversions eq. right. lets Hr: (pf_rcd_T Hi Pf).
      apply* open_record_type.
    * inversion r. inversion H.
  - right. destruct (IHPf T Hi eq_refl) as [F | Hr]. inversion F.
    inversion Hr. inversions H.
    exists ls. assumption.
  - right. destruct (IHPf T Hi eq_refl) as [F | Hr]. inversion F.
    inversion Hr. inversions H.
    eexists. apply* rt_one.
Qed.

(** If [x]'s precise type is [mu(x: U)], then [Gamma(x) = mu(x: U)] *)
Lemma pf_inert_bnd_U: forall G x T U,
    inert G ->
    precise_flow x G T (typ_bnd U) ->
    T = typ_bnd U.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert_T Hi Pf). inversions HT; dependent induction Pf; auto.
  - destruct U0; inversions x.
    apply precise_flow_all_inv in Pf. inversion* Pf.
  - apply precise_flow_all_inv in Pf. inversion Pf.
  - apply precise_flow_all_inv in Pf. inversion Pf.
  - specialize (IHPf U0 Hi T0 eq_refl eq_refl H).
    destruct (pf_inert_or_rcd Hi Pf) as [Heq | Hr].
    * inversions Heq. destruct T0; inversions x. inversion H. inversion H0.
    * inversions IHPf. inversion Hr. inversions H0.
  - destruct (pf_inert_or_rcd Hi Pf) as [Heq | Hr].
    * inversions Heq.
    * inversions Hr. inversions H0. inversions H3.
  - destruct (pf_inert_or_rcd Hi Pf) as [Heq | Hr].
    * inversions Heq.
    * inversions Hr. inversions H0.
Qed.

(** If [x]'s precise type is a field or type declaration, then [Gamma(x)] is
    a recursive type. *)
Lemma pf_inert_rcd_U: forall G x T D,
    inert G ->
    precise_flow x G T (typ_rcd D) ->
    exists U, T = typ_bnd U.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert_T Hi Pf). inversions HT; dependent induction Pf; auto.
  - apply precise_flow_all_inv in Pf. inversion Pf.
  - apply precise_flow_all_inv in Pf. inversion Pf.
  - apply precise_flow_all_inv in Pf. inversion Pf.
  - apply (pf_inert_bnd_U Hi) in Pf. exists* U.
  - exists* T0.
  - exists* T0.
Qed.

(** If [x]'s precise type is a record type, then [Gamma(x)] is a recursive type. *)
Lemma pf_inert_rcd_typ_U: forall G x T Ds,
    inert G ->
    precise_flow x G T Ds ->
    record_type Ds ->
    exists U, T = typ_bnd U.
Proof.
  introv Hi Pf Hr.
  lets HT: (pf_inert_T Hi Pf). inversions HT; dependent induction Pf; auto.
  - inversion Hr. inversion H0.
  - apply precise_flow_all_inv in Pf. inversion Pf.
  - apply precise_flow_all_inv in Pf. inversion Pf.
  - apply precise_flow_all_inv in Pf. inversion Pf.
  - inversion Hr. inversion H1.
  - apply (pf_inert_bnd_U Hi) in Pf. exists* U.
  - apply* IHPf. destruct (pf_inert_or_rcd Hi Pf) as [H1 | H1].
    inversion H1. assumption.
  - apply* IHPf. destruct (pf_inert_or_rcd Hi Pf) as [H1 | H1].
    inversion H1. assumption.
Qed.

(** If [x]'s precise type is a recursive type [mu(x: U)], then [U] is a record type. *)
Lemma pf_inert_rcd_bnd_U : forall G x T U,
    inert G ->
    precise_flow x G T (typ_bnd U) ->
    record_type U.
Proof.
  introv Hi Pf. lets HT: (pf_inert_bnd_U Hi Pf). subst.
  lets HiT: (pf_rcd_T Hi Pf). assumption.
Qed.

(** The following two lemmas express that if [x]'s precise type is a function type,
    then [Gamma(x)] is the same function type. *)
Lemma pf_inert_lambda_U : forall x G S T U,
    inert G ->
    precise_flow x G U (typ_all S T) ->
    U = typ_all S T.
Proof.
  introv Hi Pf.
  lets Hiu: (pf_inert_T Hi Pf).
  inversions Hiu.
  - apply precise_flow_all_inv in Pf. inversion* Pf.
  - destruct (pf_inert_or_rcd Hi Pf) as [H1 | H1]; inversions H1.
    inversion H0.
Qed.

(** See [pf_inert_lambda_U]. *)
Lemma inert_precise_all_inv : forall x G S T,
    inert G ->
    G |-! trm_var (avar_f x) : typ_all S T ->
    binds x (typ_all S T) G.
Proof.
  introv Hgd Htyp.
  destruct (precise_flow_lemma Htyp) as [V Pf].
  pose proof (pf_inert_lambda_U Hgd Pf) as H. subst.
  apply* pf_binds.
Qed.

(** The following two lemmas say that in an inert context, the precise type of a variable
    cannot be bottom. *)
Lemma pf_bot_false : forall G x T,
    inert G ->
    precise_flow x G T typ_bot ->
    False.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert_T Hi Pf). inversions HT.
  - apply precise_flow_all_inv in Pf. inversion Pf.
  - destruct (pf_inert_or_rcd Hi Pf); inversion H0. inversion H1.
Qed.

(** See [pf_bot_false]. *)
Lemma precise_bot_false : forall G x,
    inert G ->
    G |-! trm_var (avar_f x) : typ_bot ->
    False.
Proof.
  introv Hi Hp. destruct (precise_flow_lemma Hp) as [T Pf].
  apply* pf_bot_false.
Qed.

(** The following two lemmas say that in an inert context, the precise type of
    a variable cannot be type selection. *)
Lemma pf_psel_false : forall G T x y A,
    inert G ->
    precise_flow x G T (typ_sel y A) ->
    False.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert_T Hi Pf). inversions HT.
  - apply precise_flow_all_inv in Pf. inversion Pf.
  - destruct (pf_inert_or_rcd Hi Pf); inversion H0. inversion H1.
Qed.

(** See [pf_psel_false]. *)
Lemma precise_psel_false : forall G x y A,
    inert G ->
    G |-! trm_var (avar_f x) : typ_sel y A ->
    False.
Proof.
  introv Hi Hp. destruct (precise_flow_lemma Hp) as [T Pf].
  apply* pf_psel_false.
Qed.

(** If [Gamma(x) = mu(T)], and [Gamma |-! x: ... /\ D /\ ...], then [T^x = ... /\ D /\ ...]. *)
Lemma pf_record_sub : forall x G T T' D,
    inert G ->
    precise_flow x G (typ_bnd T) T' ->
    record_has T' D ->
    record_has (open_typ x T) D.
Proof.
  introv Hi Pf Hr. dependent induction Pf.
  - inversions Hr.
  - apply (pf_inert_bnd_U Hi) in Pf. inversion* Pf.
  - apply* IHPf.
  - apply* IHPf.
Qed.

(** If [Gamma(x) = mu(S)] and [Gamma |-! x: D], where [D] is a field or type declaration,
    then [S^x = ... /\ D /\ ...]. *)
Lemma precise_flow_record_has: forall S G x D,
    inert G ->
    precise_flow x G (typ_bnd S) (typ_rcd D) ->
    record_has (open_typ x S) D.
Proof.
  introv Hi Pf. apply* pf_record_sub.
Qed.

(** If
    - [Gamma(x) = mu(T)]
    - [Gamma |-! x: {A: T1..T1}]
    - [Gamma |-! x: {A: T2..T2}]
    then [T1 = T2]. *)
Lemma pf_record_unique_tight_bounds_rec : forall G x T A T1 T2,
    inert G ->
    precise_flow x G (typ_bnd T) (typ_rcd (dec_typ A T1 T1)) ->
    precise_flow x G (typ_bnd T) (typ_rcd (dec_typ A T2 T2)) ->
    T1 = T2.
Proof.
  introv Hi Pf1 Pf2.
  pose proof (precise_flow_record_has Hi Pf1) as H1.
  pose proof (precise_flow_record_has Hi Pf2) as H2.
  eapply unique_rcd_typ; eauto. apply (pf_rcd_T Hi) in Pf1.
  apply* open_record_type.
Qed.

(** If
    - [Gamma |-! x: {A: T1..T1}]
    - [Gamma |-! x: {A: T2..T2}]
    then [T1 = T2]. *)(** *)
Lemma pf_inert_unique_tight_bounds : forall G x T T1 T2 A,
    inert G ->
    precise_flow x G T (typ_rcd (dec_typ A T1 T1)) ->
    precise_flow x G T (typ_rcd (dec_typ A T2 T2)) ->
    T1 = T2.
Proof.
  introv Hi Pf1 Pf2.
  assert (record_type (typ_rcd (dec_typ A T1 T1))) as Hrt. {
    unfold record_type. eexists. apply* rt_one.
    constructor.
  }
  lets Hr: (pf_inert_rcd_typ_U Hi Pf1 Hrt). destruct Hr as [U Heq]. subst.
  apply* pf_record_unique_tight_bounds_rec.
Qed.

(** If [Gamma |-! x: T1] and [Gamma |-! x: T2], where both [T1] and [T2] are inert,
    then [T1 = T2]. *)
Lemma inert_pt_unique: forall G x T T1 T2,
    inert G ->
    precise_flow x G T T1 ->
    precise_flow x G T T2 ->
    inert_typ T1 ->
    inert_typ T2 ->
    T1 = T2.
Proof.
  introv Hi P1 P2 I1 I2. inversions I1; inversions I2.
  - apply (pf_inert_lambda_U Hi) in P1.
    apply (pf_inert_lambda_U Hi) in P2. inversions* P2.
  - apply (pf_inert_bnd_U Hi) in P2.
    apply (pf_inert_lambda_U Hi) in P1. inversions* P2.
  - apply (pf_inert_bnd_U Hi) in P1.
    apply (pf_inert_lambda_U Hi) in P2. inversions* P2.
  - apply (pf_inert_bnd_U Hi) in P2.
    apply (pf_inert_bnd_U Hi) in P1. inversions* P2.
Qed.

(** If [Gamma |-! x: {a: U1}] and [Gamma |-! x: {a: U2}], then [U1 = U2]. *)
Lemma pf_rcd_unique: forall G x T a U1 U2,
    inert G ->
    precise_flow x G T (typ_rcd (dec_trm a U1)) ->
    precise_flow x G T (typ_rcd (dec_trm a U2 )) ->
    U1 = U2.
Proof.
  introv Hi Pf1 Pf2. dependent induction Pf1.
  - apply (binds_inert H) in Hi. inversion Hi.
  - assert (record_type (typ_rcd (dec_trm a U2))) as Hrt. {
      eexists. apply* rt_one. constructor.
    }
    destruct (pf_inert_rcd_typ_U Hi Pf2 Hrt) as [S Heq]. subst.
    destruct U; inversions x. destruct d; inversions H0.
    apply (pf_inert_bnd_U Hi) in Pf1. inversions Pf1.
    lets Hr: (precise_flow_record_has Hi Pf2). inversion* Hr.
  - assert (record_type (typ_rcd (dec_trm a U2))) as Hrt. {
      eexists. apply* rt_one. constructor.
    }
    destruct (pf_inert_rcd_typ_U Hi Pf2 Hrt) as [S Heq]. subst.
    assert (record_has (typ_and (typ_rcd (dec_trm a U1)) U0) (dec_trm a U1))
      as H by (apply* rh_andl).
    lets Hr1: (pf_record_sub Hi Pf1 H).
    lets Hr2: (precise_flow_record_has Hi Pf2).
    assert (record_type (open_typ x S)) as Hs. {
      apply open_record_type. apply pf_inert_T in Pf1; auto. inversion* Pf1.
    }
    apply* unique_rcd_trm.
  - assert (record_type (typ_rcd (dec_trm a U2))) as Hrt. {
      eexists. apply* rt_one. constructor.
    }
    destruct (pf_inert_rcd_typ_U Hi Pf2 Hrt) as [S Heq]. subst.
    assert (record_has (typ_and U3 (typ_rcd (dec_trm a U1))) (dec_trm a U1))
      as H by (apply* rh_andr).
    lets Hr1: (pf_record_sub Hi Pf1 H).
    lets Hr2: (precise_flow_record_has Hi Pf2).
    assert (record_type (open_typ x S)) as Hs. {
      apply open_record_type. apply pf_inert_T in Pf1; auto. inversion* Pf1.
    }
    apply* unique_rcd_trm.
Qed.

(** The type to which a variable is bound in an environment is unique. *)
Lemma x_bound_unique: forall G x T1 T2 U1 U2,
    inert G ->
    precise_flow x G T1 U1 ->
    precise_flow x G T2 U2 ->
    T1 = T2.
Proof.
  introv Hi Pf1. gen T2 U2. induction Pf1; intros;
                              try solve [apply* IHPf1]; auto.
  apply pf_binds in H0. apply (binds_func H H0).
Qed.

(** See [pf_inert_unique_tight_bound]. *)
Lemma inert_unique_tight_bounds : forall G x T1 T2 A,
    inert G ->
    G |-! trm_var (avar_f x) : typ_rcd (dec_typ A T1 T1) ->
    G |-! trm_var (avar_f x) : typ_rcd (dec_typ A T2 T2) ->
    T1 = T2.
Proof.
  introv Hi H1 H2.
  destruct (precise_flow_lemma H1) as [T1' Pf1].
  destruct (precise_flow_lemma H2) as [T2' Pf2].
  lets Heq: (x_bound_unique Hi Pf1 Pf2). subst.
  apply* pf_inert_unique_tight_bounds.
Qed.

(** If a typing context is inert, then the variables in its domain are distinct. #<br>#
    Note: [ok] is defined in [TLC.LibEnv.v]. *)
Lemma inert_ok : forall G,
    inert G ->
    ok G.
Proof.
  intros G HG. induction G using env_ind.
  auto.
  inversions HG. false* empty_push_inv.
  destruct (eq_push_inv H) as [Hx [HT HG]]. subst.
  apply* ok_push.
Qed.

Hint Resolve inert_ok.

(** The following two lemmas express that if [Gamma |-! x: {A: S..U}] then [S = U]. *)
Lemma pf_dec_typ_inv : forall G x T A S U,
    inert G ->
    precise_flow x G T (typ_rcd (dec_typ A S U)) ->
    S = U.
Proof.
  introv Hi Pf. destruct (pf_inert_rcd_U Hi Pf) as [V H]. subst.
  destruct (pf_inert_or_rcd Hi Pf) as [H1 | H1]; inversions H1. inversions H.
  inversions* H1.
Qed.

(** See [pf_dec_typ_inv]. *)
Lemma precise_dec_typ_inv : forall G x A S U,
    inert G ->
    G |-! trm_var (avar_f x) : typ_rcd (dec_typ A S U) ->
    S = U.
Proof.
  introv Hi Hpt. destruct (precise_flow_lemma Hpt) as [V Pf].
  apply* pf_dec_typ_inv.
Qed.
