(* Exact correspondence of the displayed six seeds with two-name capacity.
   The finite table is only a certificate: all transitions are checked here. *)
From mathcomp Require Import all_ssreflect.
From RegLang Require Import dfa.
From Accumulation Require Import pumping certification coverage_simulation
  pattern_seed_automata capacity_patterns capacity_seed_table
  residual_certification_examples regular_protocols protocols.
Set Implicit Arguments.
Local Notation A := (Finite.clone (option bool) _).
Local Notation I := (Finite.clone bool _).

Lemma capacity_frontier_final q :
  has (fun r : state A => r.2 == [::]) (capacity_seed_frontier q) =
  (q \in dfa_fin capacity_seed_dfa).
Proof.
  rewrite inE. case: q => [n Hn].
  do 18 (case: n Hn => [|n] Hn; first by vm_compute).
  by [].
Qed.

Lemma capacity_frontier_step q a :
  perm_eq (advance (capacity_seed_frontier q) a)
    (capacity_seed_frontier (@dfa_trans A capacity_seed_dfa q a)).
Proof.
  case: q => [n Hn].
  do 18 (case: n Hn => [|n] Hn;
    first by case: a => [[|]|]; vm_compute).
  by [].
Qed.

Lemma capacity_frontier_initial :
  perm_eq (capacity_seed_frontier (dfa_s capacity_seed_dfa))
    [seq ([::],s) | s <- separating_seeds].
Proof. vm_compute. reflexivity. Qed.

Theorem capacity_seed_dfa_exact w :
  coveredb A separating_seeds w = (w \in dfa_lang capacity_seed_dfa).
Proof.
  rewrite coveredb_simulate.
  rewrite -(simulate_frontier_ext _ _ w (perm_mem capacity_frontier_initial)).
  exact (@frontier_accept A capacity_seed_dfa capacity_seed_frontier
    capacity_frontier_final capacity_frontier_step _ w).
Qed.

Definition capacity_seed_semantic (q : capacity_seed_state) : capacity_state I :=
  match val q with
  | 0 => Some (capacity_cap I 0, set0)
  | 1 => Some (capacity_cap I 1, set0)
  | 2 => None
  | 3 => Some (capacity_cap I 2, set0)
  | 4 => Some (capacity_cap I 1, [set false])
  | 5 => Some (capacity_cap I 1, [set true])
  | 6 | 8 | 10 => Some (capacity_cap I 2, [set false])
  | 7 | 9 | 12 => Some (capacity_cap I 2, [set true])
  | _ => Some (capacity_cap I 2, setT)
  end.

Lemma capacity_bool_cap_value n : val (capacity_cap I n) = minn 2 n.
Proof. by rewrite /capacity_cap /= card_bool. Qed.
Lemma capacity_bool_cap_three : capacity_cap I 3 = capacity_cap I 2.
Proof. apply/val_inj. by rewrite !capacity_bool_cap_value. Qed.
Lemma capacity_bool_cap_next n :
  capacity_cap I (minn #|I| n).+1 = capacity_cap I n.+1.
Proof. exact: capacity_cap_succ. Qed.
Lemma capacity_bool_full_budget n :
  (#|[set: I]| <= val (capacity_cap I n)) = (2 <= n).
Proof. by rewrite capacity_cap_budget cardsT card_bool. Qed.

Lemma capacity_seed_simulation_initial :
  capacity_seed_semantic (dfa_s capacity_seed_dfa) = dfa_s (capacity_dfa I).
Proof. reflexivity. Qed.

Lemma capacity_seed_simulation_final q :
  (q \in dfa_fin capacity_seed_dfa) =
  (capacity_seed_semantic q \in dfa_fin (capacity_dfa I)).
Proof.
  rewrite !inE. case: q => [n Hn].
  do 18 (case: n Hn => [|n] Hn;
    first by rewrite /capacity_seed_semantic /capacity_final /=
      -?cards_eq0 ?cards0 ?cards1 ?cardsT ?card_bool).
  by [].
Qed.

Lemma capacity_seed_simulation_step q a :
  capacity_seed_semantic (@dfa_trans A capacity_seed_dfa q a) =
  @dfa_trans A (capacity_dfa I) (capacity_seed_semantic q) a.
Proof.
  case: q => [n Hn].
  do 18 (case: n Hn => [|n] Hn;
    first (case: a => [[|]|];
      cbv beta iota zeta delta [dfa_trans capacity_seed_dfa capacity_seed_transition
        capacity_seed_index capacity_seed_rows nth val capacity_seed_semantic
        capacity_dfa capacity_transition];
      repeat (progress (rewrite ?setUT ?capacity_bool_full_budget
        ?capacity_cap_budget ?capacity_bool_cap_value
        ?cardsU1 ?cards0 ?cards1 ?cardsT ?card_bool ?inE
        ?capacity_bool_cap_next ?capacity_bool_cap_three /=));
      try reflexivity;
      do 2 f_equal; apply/setP; intros []; by rewrite !inE)).
  by [].
Qed.

Theorem capacity_six_seeds_complete w :
  coveredb A separating_seeds w = @capacity_complete I w.
Proof.
  rewrite capacity_seed_dfa_exact.
  rewrite (@pattern_dfa_simulation_correct A capacity_seed_dfa (capacity_dfa I)
    capacity_seed_semantic capacity_seed_simulation_initial
    capacity_seed_simulation_final capacity_seed_simulation_step).
  exact: capacity_dfa_correct.
Qed.

Theorem capacity_six_seeds_exact w :
  @pumping_closure A None (@seed_language A separating_seeds) w <->
  @capacity_complete I w = true.
Proof.
  change (@pumping_closure_lang A None (@seed_language A separating_seeds) w <->
    @capacity_complete I w = true).
  rewrite pumping_closure_seed_corpus -coveredb_spec.
  by rewrite capacity_six_seeds_complete.
Qed.

Lemma capacity_separating_normalized_seeds :
  normalized_seeds separating_regex = separating_seeds.
Proof. vm_compute. reflexivity. Qed.

Theorem capacity_separating_family_exact c w :
  accepts separating_family c w = @capacity_complete I w.
Proof.
  change (coveredb A (normalized_seeds separating_regex) w = @capacity_complete I w).
  rewrite capacity_separating_normalized_seeds.
  exact: capacity_six_seeds_complete.
Qed.
