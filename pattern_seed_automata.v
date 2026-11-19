(* Small, independently checked automata connect displayed seed sets to the
   parameterized pattern models.  The certificate checks every state and
   transition; its consequence quantifies over all words. *)
From mathcomp Require Import all_ssreflect.
From RegLang Require Import dfa regexp.
From Accumulation Require Import pumping coverage_simulation certification.
Set Implicit Arguments.

Section SeedAutomata.
Variable A : finType.

Lemma simulate_frontier_ext (xs ys : seq (state A)) w :
  (forall q, (q \in xs) = (q \in ys)) ->
  @simulate A xs w = @simulate A ys w.
Proof.
  move=> Heq. apply/idP/idP;
    move/simulateP=> [q Hq Hr]; apply/simulateP; exists q => //.
  - by rewrite -Heq.
  - by rewrite Heq.
Qed.

Lemma coveredb_simulate seeds w :
  coveredb A seeds w = @simulate A [seq ([::],s) | s <- seeds] w.
Proof.
  apply/idP/idP.
  - move/List.existsb_exists=> [s [Hs Hw]].
    apply/simulateP. exists ([::],s).
    + apply/mapP. exists s => //. apply mem_list_in; exact Hs.
    + change (covers_simulation A s w = true) in Hw.
      move/simulateP: Hw => [q Hq Hr].
      move: Hq; rewrite in_cons in_nil orbF => /eqP Hq. subst q. exact Hr.
  - move/simulateP=> [q /mapP [s Hs ->] Hr].
    apply List.existsb_exists. exists s; split.
    + apply mem_list_in; exact Hs.
    + change (covers_simulation A s w = true).
      apply/simulateP. exists ([::],s) => //.
      by rewrite mem_seq1.
Qed.

Variable D : dfa A.
Variable frontier : D -> seq (state A).
Hypothesis frontier_final : forall q,
  has (fun r : state A => r.2 == [::]) (frontier q) = (q \in dfa_fin D).
Hypothesis frontier_step : forall q a,
  perm_eq (@advance A (frontier q) a) (frontier (dfa_trans q a)).

Lemma frontier_accept q w : @simulate A (frontier q) w = dfa_accept q w.
Proof.
  elim: w q => [|a w IH] q /=.
  - by rewrite accept_nil frontier_final.
  - rewrite accept_cons.
    rewrite (simulate_frontier_ext _ _ w (perm_mem (frontier_step q a))).
    exact: IH.
Qed.

Theorem finite_seed_automaton_correct seeds :
  frontier (dfa_s D) = [seq ([::],s) | s <- seeds] ->
  forall w, coveredb A seeds w = (w \in dfa_lang D).
Proof.
  move=> Hinit w. rewrite coveredb_simulate -Hinit frontier_accept.
  reflexivity.
Qed.
End SeedAutomata.

Section AutomatonSimulation.
Variable A : finType.
Variables D E : dfa A.
Variable f : D -> E.
Hypothesis simulation_initial : f (dfa_s D) = dfa_s E.
Hypothesis simulation_final : forall q, (q \in dfa_fin D) = (f q \in dfa_fin E).
Hypothesis simulation_step : forall q a, f (dfa_trans q a) = dfa_trans (f q) a.

Lemma pattern_dfa_simulation_delta q w : f (@delta A D q w) = @delta A E (f q) w.
Proof. by elim: w q => [|a w IH] q //=; rewrite IH simulation_step. Qed.

Theorem pattern_dfa_simulation_correct w :
  (w \in dfa_lang D) = (w \in dfa_lang E).
Proof.
  rewrite !inE /dfa_accept simulation_final pattern_dfa_simulation_delta.
  by rewrite simulation_initial.
Qed.
End AutomatonSimulation.
