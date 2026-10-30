(* The extracted accumulation laws discharge the existing certification and
   client-soundness interfaces.  No new checker or runtime semantics is used. *)
From Coq Require Import List Bool.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import regexp.
From Accumulation Require Import pumping certification regular_protocols
  trace_languages protocols syntax semantics copying_typestate copying_soundness
  residual_certification accumulation_bridge.
Set Implicit Arguments.

(* Kellogg et al., Section 2 (p. 10:4), explain acceptance by a legal
   "go out of scope" observation.  Treating completion as an observable
   permission makes our two premises instances of one persistence law.
   These observations are specifications, not added runtime instructions:
   in particular, the existing Finish instruction still emits no event. *)
Inductive protocol_observation (A : Type) :=
| ObserveCall (a : A)
| ObserveCompletion.
Arguments ObserveCall {A} _.
Arguments ObserveCompletion {A}.

Definition observation_permitted {A} (K : language A) u
    (o : protocol_observation A) :=
  match o with
  | ObserveCall a => prefix_language K (u ++ [::a])
  | ObserveCompletion => K u
  end.

Definition observations_accumulate {A} (K : language A) :=
  forall u v o, trace_subsequence u v -> prefix_language K v ->
    observation_permitted K u o -> observation_permitted K v o.

Theorem observations_accumulate_iff_contract {A} (K : language A) :
  observations_accumulate K <-> accumulation_contract K.
Proof.
  split.
  - intros H. split.
    + intros u v a HS HV HU. exact (H u v (ObserveCall a) HS HV HU).
    + intros u v HS HU HV. exact (H u v ObserveCompletion HS HV HU).
  - intros [HS HC] u v [a|] Hsub HV HU; simpl in *.
    + exact (HS u v a Hsub HV HU).
    + exact (HC u v Hsub HU HV).
Qed.

Section RegularCertificates.
Variable A : finType.
Variable default : A.
Variable spec : nat -> regexp A.

Theorem kellogg_regular_certificates c :
  kellogg_error_closed (prefix_language (protocol (regular_family spec) c)) ->
  completion_stable (protocol (regular_family spec) c) ->
  certify_regex (spec c) = true /\ certify_copying_regex (spec c) = true.
Proof.
  intros HE HC.
  pose proof (kellogg_protocol_residual_shuffle_closed HE HC) as HR.
  split.
  - apply (proj2 (certify_regex_spec default (spec c))).
    intros u v w Hu Hv Hs.
    apply (proj1 (regular_family_language default spec c w)).
    apply (HR [::] u v w).
    + apply (proj2 (regular_family_language default spec c u)). exact Hu.
    + apply (proj2 (regular_family_language default spec c v)). exact Hv.
    + now apply interleaving_shuffle.
  - apply (proj2 (certify_copying_regex_spec spec c)). exact HR.
Qed.
End RegularCertificates.

Section ClientConsequences.
Context {A : Type} (P : protocol_family A).
Variable FT : class -> field -> class.
Variable copy_history : class -> bool.
Hypothesis errors_accumulate :
  forall c, kellogg_error_closed (prefix_language (protocol P c)).
Hypothesis completion_persists : forall c, completion_stable (protocol P c).

Theorem kellogg_program_prefix_sound s m :
  check_program_with_copy P FT copy_history s = true ->
  program_prefix s initial_machine m ->
  forall l, (l < next_loc m)%coq_nat ->
  prefix_language (protocol P (classes m l)) (object_history m l).
Proof.
  apply copying_program_prefix_sound.
  apply kellogg_protocol_copying_certified; assumption.
Qed.

Theorem kellogg_program_completion_sound s m :
  check_program_with_copy P FT copy_history s = true ->
  program_execution s initial_machine m ->
  forall l, (l < next_loc m)%coq_nat ->
  protocol P (classes m l) (object_history m l).
Proof.
  apply copying_program_completion_sound.
  apply kellogg_protocol_copying_certified; assumption.
Qed.
End ClientConsequences.
