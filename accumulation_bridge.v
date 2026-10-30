(* A semantic bridge to Kellogg, Shadab, Sridharan, and Ernst,
   "Accumulation Analysis", ECOOP 2022, Sections 3.2--3.3.

   Definition 6 (p. 10:5) singles out a first error; Definition 7 preserves
   that final operation while deleting earlier operations.  We encode the
   resulting endpoint-error condition on the viable traces of this paper.
   The deleted history may itself already have failed: we do not require its
   last operation to be its first error.  Section 3.3's subsequence intuition
   then yields the safe-extension law below.

   On viable histories the condition is equivalent to residual shuffle
   closure.  Completion is additional structure in this development.  We
   state its stability separately and prove a sufficient contract for our
   existing complete-history shuffle and residual-shuffle certificates.
   This is not a formalization
   of their calculus, analysis algorithm, or Theorem 9's characterization. *)
From Coq Require Import List Bool.
From Accumulation Require Import trace_languages protocols copying_typestate.
Import ListNotations.
Set Implicit Arguments.

Inductive trace_subsequence {A : Type} : list A -> list A -> Prop :=
| trace_subsequence_nil : trace_subsequence [] []
| trace_subsequence_keep a u v :
    trace_subsequence u v -> trace_subsequence (a :: u) (a :: v)
| trace_subsequence_skip a u v :
    trace_subsequence u v -> trace_subsequence u (a :: v).

Lemma trace_subsequence_refl {A} (u : list A) : trace_subsequence u u.
Proof. induction u; constructor; assumption. Qed.

Lemma trace_subsequence_empty {A} (u : list A) : trace_subsequence [] u.
Proof. induction u; constructor; assumption. Qed.

Lemma trace_subsequence_app {A} (u v u' v' : list A) :
  trace_subsequence u v -> trace_subsequence u' v' ->
  trace_subsequence (u ++ u') (v ++ v').
Proof. intros H; induction H; simpl; intros; auto using trace_subsequence. Qed.

Lemma trace_subsequence_app_right {A} (u v w : list A) :
  trace_subsequence u v -> trace_subsequence u (v ++ w).
Proof.
  intros H. rewrite <- (app_nil_r u).
  apply trace_subsequence_app; auto using trace_subsequence_empty.
Qed.

Lemma shuffle_trace_subsequence_left {A} (u v w : list A) :
  shuffle u v w -> trace_subsequence u w.
Proof. intros H; induction H; constructor; assumption. Qed.

Lemma shuffle_trace_subsequence_right {A} (u v w : list A) :
  shuffle u v w -> trace_subsequence v w.
Proof. intros H; induction H; constructor; assumption. Qed.

(* P denotes safe histories.  For P = prefix_language K, P v guarantees
   that appending a is the first loss of viability in the full history. *)
Definition kellogg_error_closed {A} (P : language A) :=
  forall u v a, trace_subsequence u v -> P v ->
    ~ P (v ++ [a]) -> ~ P (u ++ [a]).

Definition subsequence_safe_extension {A} (P : language A) :=
  forall u v a, trace_subsequence u v -> P v ->
    P (u ++ [a]) -> P (v ++ [a]).

Lemma safe_extension_kellogg_error_closed {A} (P : language A) :
  subsequence_safe_extension P -> kellogg_error_closed P.
Proof. unfold subsequence_safe_extension, kellogg_error_closed; eauto. Qed.

Theorem kellogg_error_closed_iff_safe_extension {A} (P : language A) :
  (forall w, {P w} + {~ P w}) ->
  (kellogg_error_closed P <-> subsequence_safe_extension P).
Proof.
  intros Hdec. split; [|apply safe_extension_kellogg_error_closed].
  intros HE u v a Hsub Hv Hua.
  destruct (Hdec (v ++ [a])) as [Hyes|Hno]; [exact Hyes|].
  exfalso. exact (HE u v a Hsub Hv Hno Hua).
Qed.

(* Completion is preserved by adding observations, provided the resulting
   full history remains viable.  This is our additional completion premise,
   not an assertion that Kellogg et al. formalize mandatory termination. *)
Definition completion_stable {A} (K : language A) :=
  forall u v, trace_subsequence u v -> K u ->
    prefix_language K v -> K v.

Definition accumulation_contract {A} (K : language A) :=
  subsequence_safe_extension (prefix_language K) /\ completion_stable K.

Lemma bridge_prefix_app_inv {A} (K : language A) u v :
  prefix_language K (u ++ v) -> prefix_language K u.
Proof. intros [w H]. exists (v ++ w). now rewrite app_assoc. Qed.

(* Each branch history is a subsequence of the accumulated global history.
   Processing a shuffled next event preserves viability by safe extension.
   Separate branch prefixes allow a shared past to be included only once. *)
Lemma safe_extension_shuffle_prefixes {A} (K : language A) :
  subsequence_safe_extension (prefix_language K) ->
  forall u v w, shuffle u v w ->
  forall p q r,
    trace_subsequence p r -> trace_subsequence q r ->
    prefix_language K (p ++ u) -> prefix_language K (q ++ v) ->
    prefix_language K r -> prefix_language K (r ++ w).
Proof.
  intros Hsafe u v w Hsh. induction Hsh; intros p q r Hp Hq Hu Hv Hr.
  - now rewrite app_nil_r.
  - assert (Hpa : prefix_language K (p ++ [a])).
    { apply (@bridge_prefix_app_inv A K (p ++ [a]) u).
      now rewrite <- app_assoc. }
    assert (Hra : prefix_language K (r ++ [a])) by
      (exact (Hsafe p r a Hp Hr Hpa)).
    change (prefix_language K (r ++ ([a] ++ w))).
    rewrite app_assoc.
    apply (IHHsh (p ++ [a]) q (r ++ [a])).
    + apply trace_subsequence_app; auto using trace_subsequence_refl.
    + now apply trace_subsequence_app_right.
    + now rewrite <- app_assoc.
    + exact Hv.
    + exact Hra.
  - assert (Hqa : prefix_language K (q ++ [a])).
    { apply (@bridge_prefix_app_inv A K (q ++ [a]) v).
      now rewrite <- app_assoc. }
    assert (Hra : prefix_language K (r ++ [a])) by
      (exact (Hsafe q r a Hq Hr Hqa)).
    change (prefix_language K (r ++ ([a] ++ w))).
    rewrite app_assoc.
    apply (IHHsh p (q ++ [a]) (r ++ [a])).
    + now apply trace_subsequence_app_right.
    + apply trace_subsequence_app; auto using trace_subsequence_refl.
    + exact Hu.
    + now rewrite <- app_assoc.
    + exact Hra.
Qed.

Theorem subsequence_safe_extension_residual_prefix_shuffle_closed
    {A} (K : language A) :
  subsequence_safe_extension (prefix_language K) ->
  residual_shuffle_closed (prefix_language K).
Proof.
  intros Hsafe p u v w Hu Hv Hsh. unfold residual in *.
  eapply (safe_extension_shuffle_prefixes Hsafe Hsh);
    eauto using trace_subsequence_refl, bridge_prefix_app_inv.
Qed.

(* Conversely, residual closure can insert each omitted operation at its
   original position.  The full history's viability makes that operation
   a viable continuation of the shared prefix. *)
Lemma residual_prefix_shuffle_closed_safe_extension_at
    {A} (K : language A) :
  residual_shuffle_closed (prefix_language K) ->
  forall u v, trace_subsequence u v ->
  forall p a,
    prefix_language K (p ++ v) ->
    prefix_language K (p ++ (u ++ [a])) ->
    prefix_language K (p ++ (v ++ [a])).
Proof.
  intros Hclosed u v Hsub. induction Hsub; intros p b Hv Hub.
  - exact Hub.
  - change (prefix_language K (p ++ ([a] ++ (v ++ [b])))).
    rewrite app_assoc. apply (IHHsub (p ++ [a]) b).
    + now rewrite <- app_assoc.
    + now rewrite <- app_assoc.
  - change (prefix_language K (p ++ ([a] ++ (v ++ [b])))).
    rewrite app_assoc. apply (IHHsub (p ++ [a]) b).
    + now rewrite <- app_assoc.
    + assert (Hpa : prefix_language K (p ++ [a])).
      { apply (@bridge_prefix_app_inv A K (p ++ [a]) v).
        now rewrite <- app_assoc. }
      rewrite <- app_assoc.
      exact (Hclosed p [a] (u ++ [b]) ([a] ++ (u ++ [b]))
        Hpa Hub (shuffle_concat [a] (u ++ [b]))).
Qed.

Theorem residual_prefix_shuffle_closed_subsequence_safe_extension
    {A} (K : language A) :
  residual_shuffle_closed (prefix_language K) ->
  subsequence_safe_extension (prefix_language K).
Proof.
  intros Hclosed u v a Hsub Hv Hua.
  exact (@residual_prefix_shuffle_closed_safe_extension_at
    A K Hclosed u v Hsub [] a Hv Hua).
Qed.

Theorem subsequence_safe_extension_iff_residual_prefix_shuffle_closed
    {A} (K : language A) :
  subsequence_safe_extension (prefix_language K) <->
  residual_shuffle_closed (prefix_language K).
Proof.
  split; [apply subsequence_safe_extension_residual_prefix_shuffle_closed|
    apply residual_prefix_shuffle_closed_subsequence_safe_extension].
Qed.

Theorem kellogg_error_closed_iff_residual_prefix_shuffle_closed
    {A} (K : language A) :
  (forall w, {prefix_language K w} + {~ prefix_language K w}) ->
  (kellogg_error_closed (prefix_language K) <->
    residual_shuffle_closed (prefix_language K)).
Proof.
  intros Hdec.
  rewrite (kellogg_error_closed_iff_safe_extension (prefix_language K) Hdec).
  apply subsequence_safe_extension_iff_residual_prefix_shuffle_closed.
Qed.

(* Residual closure of complete histories also gives residual closure of
   viable histories.  Combined with the previous equivalence, this shows
   that our copying certificate implies the encoded Kellogg safety law.
   It does not imply completion_stable. *)
Lemma bridge_prefix_residual {A} (K : language A) p u :
  prefix_language (residual K p) u <->
  residual (prefix_language K) p u.
Proof.
  unfold prefix_language, residual. split; intros [v Hv]; exists v;
    now rewrite app_assoc in *.
Qed.

Theorem residual_shuffle_closed_prefix {A} (K : language A) :
  residual_shuffle_closed K -> residual_shuffle_closed (prefix_language K).
Proof.
  intros Hclosed p u v w Hu Hv Hsh.
  apply bridge_prefix_residual.
  apply (@prefix_shuffle_closed A (residual K p) (Hclosed p) u v w).
  - now apply bridge_prefix_residual.
  - now apply bridge_prefix_residual.
  - exact Hsh.
Qed.

Theorem residual_shuffle_closed_kellogg_error_closed {A} (K : language A) :
  residual_shuffle_closed K -> kellogg_error_closed (prefix_language K).
Proof.
  intros H. apply safe_extension_kellogg_error_closed.
  apply residual_prefix_shuffle_closed_subsequence_safe_extension.
  now apply residual_shuffle_closed_prefix.
Qed.

Theorem accumulation_contract_residual_shuffle_closed {A} (K : language A) :
  accumulation_contract K -> residual_shuffle_closed K.
Proof.
  intros [Hsafe Hcomplete] p u v w Hu Hv Hsh. unfold residual in *.
  apply (Hcomplete (p ++ u) (p ++ w)).
  - apply trace_subsequence_app; [apply trace_subsequence_refl|].
    exact (shuffle_trace_subsequence_left Hsh).
  - exact Hu.
  - exact (@subsequence_safe_extension_residual_prefix_shuffle_closed
      A K Hsafe p u v w (@prefix_includes A K (p ++ u) Hu) (@prefix_includes A K (p ++ v) Hv) Hsh).
Qed.

Theorem accumulation_contract_shuffle_closed {A} (K : language A) :
  accumulation_contract K -> shuffle_closed K.
Proof.
  intros H. exact (@accumulation_contract_residual_shuffle_closed A K H []).
Qed.

(* The protocol interface supplies the only decision needed for the
   negative-to-positive translation; no classical axiom is introduced. *)
Lemma protocol_prefix_decidable {A} (P : protocol_family A) c w :
  {prefix_language (protocol P c) w} +
  {~ prefix_language (protocol P c) w}.
Proof.
  destruct (viable P c w) eqn:H.
  - left. now apply viable_prefix.
  - right. intros HF. apply viable_prefix in HF. congruence.
Qed.

Theorem kellogg_protocol_residual_shuffle_closed {A}
    (P : protocol_family A) c :
  kellogg_error_closed (prefix_language (protocol P c)) ->
  completion_stable (protocol P c) ->
  residual_shuffle_closed (protocol P c).
Proof.
  intros HE HC. apply accumulation_contract_residual_shuffle_closed.
  split; [|exact HC].
  apply (kellogg_error_closed_iff_safe_extension
    (prefix_language (protocol P c)) (protocol_prefix_decidable P c)). exact HE.
Qed.

Theorem kellogg_protocol_copying_certified {A}
    (P : protocol_family A) copy_history :
  (forall c, kellogg_error_closed (prefix_language (protocol P c))) ->
  (forall c, completion_stable (protocol P c)) ->
  copying_certified P copy_history.
Proof.
  intros HE HC. split.
  - intros c. exact (@kellogg_protocol_residual_shuffle_closed A P c
      (HE c) (HC c) []).
  - intros c _. exact (@kellogg_protocol_residual_shuffle_closed A P c (HE c) (HC c)).
Qed.
