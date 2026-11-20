(* Exhaustively checked finite frontier certificates relate the independently
   defined persistent machines to the manuscript's seed sets, for all words. *)
From mathcomp Require Import all_ssreflect.
From RegLang Require Import dfa.
From Accumulation Require Import pumping certification protocols
  monotone_regular persistent_pattern_queries milestone_service_patterns
  coverage_simulation pattern_seed_automata milestone_service_seed_tables.
Set Implicit Arguments.

Module MilestoneSeedProof.
Import MilestoneSeedTable.
Local Notation A := milestone_alphabet.
Definition model_dfa := @machine_dfa A milestone_state milestone_machine
  milestone_enabled milestone_complete milestone_initial.
Lemma frontier_final z :
  has (fun x : state A => x.2 == [::]) (seed_frontier z) =
  (z \in dfa_fin seed_dfa).
Proof. by rewrite inE. Qed.
Lemma frontier_step z a :
  perm_eq (advance (seed_frontier z) a)
    (seed_frontier (@dfa_trans A seed_dfa z a)).
Proof.
  case: z => [n Hn].
  do 5 (case: n Hn => [|n] Hn;
    first by case: a => [[|]|]; vm_compute).
  by [].
Qed.
Lemma frontier_initial :
  perm_eq (seed_frontier (dfa_s seed_dfa)) [seq ([::],s) | s <- seeds].
Proof. vm_compute. reflexivity. Qed.
Lemma seed_dfa_exact w : coveredb A seeds w = (w \in dfa_lang seed_dfa).
Proof.
  rewrite coveredb_simulate.
  rewrite -(simulate_frontier_ext _ _ w (perm_mem frontier_initial)).
  exact (@frontier_accept A seed_dfa seed_frontier frontier_final frontier_step _ w).
Qed.
Lemma simulation_initial : seed_semantic (dfa_s seed_dfa) = dfa_s model_dfa.
Proof. reflexivity. Qed.
Lemma simulation_final z :
  (z \in dfa_fin seed_dfa) = (seed_semantic z \in dfa_fin model_dfa).
Proof.
  rewrite !inE. case: z => [n Hn].
  do 5 (case: n Hn => [|n] Hn; first by vm_compute).
  by [].
Qed.
Lemma simulation_step z a :
  seed_semantic (@dfa_trans A seed_dfa z a) =
  @dfa_trans A model_dfa (seed_semantic z) a.
Proof.
  case: z => [n Hn].
  do 5 (case: n Hn => [|n] Hn;
    first by case: a => [[|]|]; vm_compute).
  by [].
Qed.
Lemma coverage_exact w : coveredb A seeds w = accepts milestone_family 0 w.
Proof.
  rewrite seed_dfa_exact.
  rewrite (@pattern_dfa_simulation_correct A seed_dfa model_dfa seed_semantic
    simulation_initial simulation_final simulation_step).
  apply/idP/idP.
  - move=> H. apply persistent_accept_spec;
      [exact milestone_enabled_spec|exact milestone_complete_spec|].
    apply (@machine_dfa_language A milestone_state milestone_machine
      milestone_enabled milestone_complete milestone_enabled_spec milestone_complete_spec).
    exact H.
  - move=> H. apply (@machine_dfa_language A milestone_state milestone_machine
      milestone_enabled milestone_complete milestone_enabled_spec milestone_complete_spec).
    apply persistent_accept_spec in H;
      [exact H|exact milestone_enabled_spec|exact milestone_complete_spec].
Qed.
End MilestoneSeedProof.

Theorem milestone_displayed_seeds_exact w :
  @pumping_closure milestone_alphabet (@None bool)
    (@seed_language milestone_alphabet MilestoneSeedTable.seeds) w <->
  accepts milestone_family 0 w = true.
Proof.
  change (@pumping_closure_lang milestone_alphabet (@None bool)
    (@seed_language milestone_alphabet MilestoneSeedTable.seeds) w <->
    accepts milestone_family 0 w = true).
  rewrite pumping_closure_seed_corpus -coveredb_spec.
  by rewrite MilestoneSeedProof.coverage_exact.
Qed.

Module ServiceSeedProof.
Import ServiceSeedTable.
Local Notation A := service_alphabet.
Definition model_dfa := @machine_dfa A service_state service_machine
  service_enabled service_complete service_initial.
Lemma frontier_final z :
  has (fun x : state A => x.2 == [::]) (seed_frontier z) =
  (z \in dfa_fin seed_dfa).
Proof. by rewrite inE. Qed.
Lemma frontier_step z a :
  perm_eq (advance (seed_frontier z) a)
    (seed_frontier (@dfa_trans A seed_dfa z a)).
Proof.
  case: z => [n Hn].
  do 20 (case: n Hn => [|n] Hn;
    first by case: a => [[] []]; vm_compute).
  by [].
Qed.
Lemma frontier_initial :
  perm_eq (seed_frontier (dfa_s seed_dfa)) [seq ([::],s) | s <- seeds].
Proof. vm_compute. reflexivity. Qed.
Lemma seed_dfa_exact w : coveredb A seeds w = (w \in dfa_lang seed_dfa).
Proof.
  rewrite coveredb_simulate.
  rewrite -(simulate_frontier_ext _ _ w (perm_mem frontier_initial)).
  exact (@frontier_accept A seed_dfa seed_frontier frontier_final frontier_step _ w).
Qed.
Lemma simulation_initial : seed_semantic (dfa_s seed_dfa) = dfa_s model_dfa.
Proof. reflexivity. Qed.
Lemma simulation_final z :
  (z \in dfa_fin seed_dfa) = (seed_semantic z \in dfa_fin model_dfa).
Proof.
  rewrite !inE. case: z => [n Hn].
  do 20 (case: n Hn => [|n] Hn; first by vm_compute).
  by [].
Qed.
Lemma simulation_step z a :
  seed_semantic (@dfa_trans A seed_dfa z a) =
  @dfa_trans A model_dfa (seed_semantic z) a.
Proof.
  case: z => [n Hn].
  do 20 (case: n Hn => [|n] Hn;
    first by case: a => [[] []]; vm_compute).
  by [].
Qed.
Lemma coverage_exact w : coveredb A seeds w = accepts service_family 0 w.
Proof.
  rewrite seed_dfa_exact.
  rewrite (@pattern_dfa_simulation_correct A seed_dfa model_dfa seed_semantic
    simulation_initial simulation_final simulation_step).
  apply/idP/idP.
  - move=> H. apply persistent_accept_spec;
      [exact service_enabled_spec|exact service_complete_spec|].
    apply (@machine_dfa_language A service_state service_machine
      service_enabled service_complete service_enabled_spec service_complete_spec).
    exact H.
  - move=> H. apply (@machine_dfa_language A service_state service_machine
      service_enabled service_complete service_enabled_spec service_complete_spec).
    apply persistent_accept_spec in H;
      [exact H|exact service_enabled_spec|exact service_complete_spec].
Qed.
End ServiceSeedProof.

Theorem service_displayed_seeds_exact w :
  @pumping_closure service_alphabet (false,false)
    (@seed_language service_alphabet ServiceSeedTable.seeds) w <->
  accepts service_family 0 w = true.
Proof.
  change (@pumping_closure_lang service_alphabet (false,false)
    (@seed_language service_alphabet ServiceSeedTable.seeds) w <->
    accepts service_family 0 w = true).
  rewrite pumping_closure_seed_corpus -coveredb_spec.
  by rewrite ServiceSeedProof.coverage_exact.
Qed.
