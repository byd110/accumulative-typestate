(* Verified adapter: arbitrary regular seeds -> executable client protocols. *)
From Coq Require Import List Bool.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import languages dfa regexp.
From Accumulation Require Import pumping trace_languages protocols certification coverage coverage_simulation.
Set Implicit Arguments.

Section RegularProtocols.
Variable A : finType.
Variable default : A.

Definition closure_regex (r : regexp A) : regexp A :=
  \big[Plus/Void]_(s <- normalized_seeds r) pumping_singleton_re A s.
Theorem closure_regex_correct r w :
  (w \in closure_regex r) <-> @pumping_closure A default (regex_lang A r) w.
Proof.
  rewrite normalized_closure /closure_regex.
  split.
  - move/big_plus_seqP=> [s Hs Hw].
    apply: (@pumping_closure_lift_singleton A default (seed_language (normalized_seeds r)) s w Hs).
    exact: (proj2 (pumping_closure_singleton_correct A default s w) Hw).
  - move/(proj1 (pumping_closure_seed_corpus A default (seed_language (normalized_seeds r)) w))=> [s Hs Hw].
    apply/big_plus_seqP; exists s => //.
    exact: (proj1 (pumping_closure_singleton_correct A default s w) Hw).
Qed.

Definition restart (D : dfa A) (q : D) : dfa A :=
  {| dfa_state := D; dfa_s := q; dfa_fin := dfa_fin D; dfa_trans := @dfa_trans A D |}.
Lemma restart_delta (D : dfa A) (q p : D) v :
  @delta A (restart D q) p v = @delta A D p v.
Proof. by elim: v p => [|a v IH] p //=; apply IH. Qed.
Lemma restart_accept (D : dfa A) u v :
  (v \in dfa_lang (restart D (delta (dfa_s D) u))) = (u ++ v \in dfa_lang D).
Proof. by rewrite !inE /dfa_accept /= restart_delta delta_cat. Qed.
Definition dfa_viable (D : dfa A) u : bool :=
  dfa_inhab (restart D (delta (dfa_s D) u)).
Lemma dfa_viable_spec (D : dfa A) u : dfa_viable D u = true <->
  exists v, (u ++ v \in dfa_lang D) = true.
Proof.
  split.
  - move/dfa_inhabP=> [v Hv]; exists v. by rewrite -restart_accept.
  - move=> [v Hv]; apply/dfa_inhabP; exists v. by rewrite restart_accept.
Qed.

Lemma closure_regex_covered r w :
  (w \in closure_regex r) = coveredb A (normalized_seeds r) w.
Proof.
  apply/idP/idP.
  - move/big_plus_seqP=> [s Hs Hw]. apply List.existsb_exists; exists s; split.
    + apply mem_list_in; exact Hs.
    + by rewrite /coverb covers_simulation_correct coverage.covers_regex.
  - move/List.existsb_exists=> [s [Hs Hw]]. apply/big_plus_seqP; exists s.
    + apply mem_list_in; exact Hs.
    + by move: Hw; rewrite /coverb covers_simulation_correct coverage.covers_regex.
Qed.

Lemma regular_queries (spec : nat -> regexp A) c w :
  dfa_viable (re_to_dfa (closure_regex (spec c))) w = true <->
  exists v, coveredb A (normalized_seeds (spec c)) (w ++ v) = true.
Proof.
  rewrite dfa_viable_spec. split; move=> [v Hv]; exists v;
    by move: Hv; rewrite re_to_dfa_correct closure_regex_covered.
Qed.
Definition regular_family (spec : nat -> regexp A) : protocol_family A :=
  {| accepts := fun c w => coveredb A (normalized_seeds (spec c)) w;
     viable := fun c w => dfa_viable (re_to_dfa (closure_regex (spec c))) w;
     viable_spec := regular_queries spec |}.

Theorem regular_family_language spec c w :
  protocol (regular_family spec) c w <->
  @pumping_closure A default (regex_lang A (spec c)) w.
Proof.
  unfold protocol, regular_family; simpl.
  rewrite <- closure_regex_covered. apply closure_regex_correct.
Qed.

Theorem regular_family_certified spec :
  (forall c, certify_regex (spec c) = true) -> certified (regular_family spec).
Proof.
  intros H c u v w Hu Hv Hs. apply regular_family_language.
  apply (proj1 (certify_regex_spec default (spec c)) (H c)) with u v.
  - now apply regular_family_language.
  - now apply regular_family_language.
  - now apply interleaving_shuffle.
Qed.
End RegularProtocols.
