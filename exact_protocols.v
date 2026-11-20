(* Exact-language adapters.  Unlike regular_family, these interpret their
   argument as the protocol itself and do not take a pumping closure. *)
From Coq Require Import List Bool.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import dfa regexp.
From Accumulation Require Import trace_languages protocols regular_protocols
  residual_certification syntax semantics typestate soundness.
Set Implicit Arguments.

Section ExactProtocols.
Variable A : finType.

Definition exact_dfa_family (spec : nat -> dfa A) : protocol_family A :=
  {| accepts := fun c w => w \in dfa_lang (spec c);
     viable := fun c w => dfa_viable (spec c) w;
     viable_spec := fun c w => dfa_viable_spec (spec c) w |}.

Theorem exact_dfa_family_language spec c w :
  protocol (exact_dfa_family spec) c w <-> (w \in dfa_lang (spec c)) = true.
Proof. reflexivity. Qed.

Theorem exact_dfa_family_viable spec c w :
  viable (exact_dfa_family spec) c w = true <->
  exists v, (w ++ v \in dfa_lang (spec c)) = true.
Proof. apply dfa_viable_spec. Qed.

(* This exact finite decision procedure works on the original DFA.  Its
   reference implementation enumerates bounded words in a product automaton;
   the theorem also permits a structural proof of closure to discharge the
   certificate, without evaluating that enumeration. *)
Definition certify_exact_dfa (D : dfa A) := state_shuffle_certified D (dfa_s D).

Theorem certify_exact_dfa_spec D : certify_exact_dfa D = true <->
  shuffle_closed (fun w => (w \in dfa_lang D) = true).
Proof. exact (@state_shuffle_certified_spec A D (dfa_s D)). Qed.

Theorem exact_dfa_family_certified spec :
  (forall c, certify_exact_dfa (spec c) = true) -> certified (exact_dfa_family spec).
Proof. intros H c; exact (proj1 (certify_exact_dfa_spec (spec c)) (H c)). Qed.

Definition exact_regex_family (spec : nat -> regexp A) : protocol_family A :=
  exact_dfa_family (fun c => re_to_dfa (spec c)).

Theorem exact_regex_family_language spec c w :
  protocol (exact_regex_family spec) c w <-> (w \in spec c) = true.
Proof.
  change ((w \in dfa_lang (re_to_dfa (spec c))) = true <-> (w \in spec c) = true).
  by rewrite re_to_dfa_correct.
Qed.

Theorem exact_regex_family_viable spec c w :
  viable (exact_regex_family spec) c w = true <->
  exists v, (w ++ v \in spec c) = true.
Proof.
  rewrite exact_dfa_family_viable. split; intros [v Hv]; exists v;
    by move: Hv; rewrite re_to_dfa_correct.
Qed.

Definition certify_exact_regex (r : regexp A) := certify_exact_dfa (re_to_dfa r).

Theorem certify_exact_regex_spec r : certify_exact_regex r = true <->
  shuffle_closed (fun w => (w \in r) = true).
Proof.
  rewrite /certify_exact_regex certify_exact_dfa_spec /shuffle_closed.
  split; intros H u v w Hu Hv Hs.
  - rewrite -re_to_dfa_correct. apply (H u v w); try assumption;
      by rewrite re_to_dfa_correct.
  - rewrite re_to_dfa_correct. apply (H u v w); try assumption;
      by move: Hu Hv; rewrite !re_to_dfa_correct; tauto.
Qed.

Theorem exact_regex_family_certified spec :
  (forall c, certify_exact_regex (spec c) = true) -> certified (exact_regex_family spec).
Proof. apply exact_dfa_family_certified. Qed.

(* Both adapters are instances of protocol_family, so the existing generic
   checker and all its soundness results apply to the unchanged language. *)
Theorem exact_dfa_program_completion_sound spec FT s m :
  (forall c, certify_exact_dfa (spec c) = true) ->
  check_program (exact_dfa_family spec) FT s = true ->
  program_execution s initial_machine m ->
  forall l, (l < next_loc m)%coq_nat ->
  (object_history m l \in dfa_lang (spec (classes m l))) = true.
Proof.
  intros HC HS HE l Hl.
  exact (typestate_completion_sound FT (exact_dfa_family_certified HC) HS HE Hl).
Qed.
End ExactProtocols.
