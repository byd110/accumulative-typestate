(* Conjunction and inclusive disjunction over a two-feature API, including
   an accepted inherited-history client and its concrete terminating run. *)
From Coq Require Import List Bool.
From mathcomp Require Import all_ssreflect.
From Accumulation Require Import prerequisite_patterns certification
  protocols trace_languages syntax semantics typestate copying_typestate.
Set Implicit Arguments.

Local Notation F := (Finite.clone bool _).
Local Notation A := (prerequisite_alphabet F).
Local Notation a := (Some false).
Local Notation b := (Some true).
Local Notation x := (@None bool).

Definition builder_prerequisites := @all_prerequisites F setT.
Definition builder_protocol := prerequisite_protocol builder_prerequisites.
Lemma two_features_nonempty : [set: F] != set0.
Proof. apply/set0Pn; exists false. by rewrite in_setT. Qed.
Definition alternative_prerequisites := @any_prerequisites F setT two_features_nonempty.
Definition alternative_protocol := prerequisite_protocol alternative_prerequisites.

Lemma builder_guard_eval (acquired : {set F}) :
  prerequisite_guard builder_prerequisites acquired =
  ((false \in acquired) && (true \in acquired)).
Proof.
  change ((setT \subset acquired) =
    ((false \in acquired) && (true \in acquired))).
  apply/idP/idP.
  - move/subsetP => H. apply/andP; split; apply H; by rewrite in_setT.
  - move/andP => [Hf Ht]. apply/subsetP; intros [] _; assumption.
Qed.
Lemma alternative_guard_eval (acquired : {set F}) :
  prerequisite_guard alternative_prerequisites acquired =
  ((false \in acquired) || (true \in acquired)).
Proof.
  change ([exists f : F, (f \in setT) && (f \in acquired)] =
    ((false \in acquired) || (true \in acquired))).
  apply/idP/idP.
  - move/existsP => [[] /andP [_ H]]; apply/orP; auto.
  - move/orP => [H|H]; apply/existsP; [exists false|exists true];
      by rewrite in_setT H.
Qed.

Lemma two_features_all_eval (acquired : {set F}) :
  (setT \subset acquired) = ((false \in acquired) && (true \in acquired)).
Proof. exact: builder_guard_eval. Qed.
Lemma two_features_any_eval (acquired : {set F}) :
  [exists f : F, (f \in setT) && (f \in acquired)] =
  ((false \in acquired) || (true \in acquired)).
Proof. exact: alternative_guard_eval. Qed.

Ltac compute_prerequisites :=
  repeat (progress (cbv beta iota zeta delta [builder_protocol alternative_protocol prerequisite_protocol
    accepts viable prerequisite_accept prerequisite_viable prerequisite_run
    prerequisite_enabled prerequisite_step prerequisite_initial
    check_program check_program_with_copy check_stmt check_stmt_with_copy
    check_step check_step_with_copy instrument finish_freeb sequence
    check_bind retirable all_complete get put List.forallb List.app Nat.eqb andb fst];
    rewrite ?builder_guard_eval ?alternative_guard_eval
      ?two_features_all_eval ?two_features_any_eval ?inE /=)); reflexivity.

Example empty_conjunction_completes :
  prerequisite_accept (@all_prerequisites F set0) [::x] = true.
Proof.
  rewrite /prerequisite_accept /= /prerequisite_enabled /all_prerequisites /= sub0set.
  reflexivity.
Qed.
Example builder_no_use_incomplete : accepts builder_protocol 0 [::a;b] = false.
Proof. compute_prerequisites. Qed.
Example builder_requires_both : accepts builder_protocol 0 [::a;x] = false.
Proof. compute_prerequisites. Qed.
Example builder_complete : accepts builder_protocol 0 [::a;b;x] = true.
Proof. compute_prerequisites. Qed.
Example builder_reverse_complete : accepts builder_protocol 0 [::b;a;x] = true.
Proof. compute_prerequisites. Qed.
Example builder_post_use_setter : accepts builder_protocol 0 [::a;b;x;a;x] = true.
Proof. compute_prerequisites. Qed.
Example builder_missing_prerequisite_dead : viable builder_protocol 0 [::a;x] = false.
Proof. compute_prerequisites. Qed.
Example builder_partial_viable : viable builder_protocol 0 [::a] = true.
Proof. compute_prerequisites. Qed.
Example alternative_requires_one : accepts alternative_protocol 0 [::x] = false.
Proof. compute_prerequisites. Qed.
Example alternative_left_complete : accepts alternative_protocol 0 [::a;x] = true.
Proof. compute_prerequisites. Qed.
Example alternative_right_complete : accepts alternative_protocol 0 [::b;x] = true.
Proof. compute_prerequisites. Qed.
Example alternative_mixed_complete : accepts alternative_protocol 0 [::a;x;b;x] = true.
Proof. compute_prerequisites. Qed.

(* Direct seed certificates accompany the exact state-model
   correspondences proved below. *)
Definition builder_seeds : seq (seq A) := [::[::a;b;x];[::b;a;x]].
Definition alternative_seeds : seq (seq A) :=
  [::[::a;x];[::b;x];[::a;b;x];[::a;x;b];[::b;a;x];[::b;x;a]].
Example builder_seed_certificate : @certify_seeds A builder_seeds = true.
Proof. vm_compute; reflexivity. Qed.
Example alternative_seed_certificate : @certify_seeds A alternative_seeds = true.
Proof. vm_compute; reflexivity. Qed.
Example alternative_mixed_seed_is_needed :
  @certify_seeds A [::[::a;x];[::b;x]] = false.
Proof. vm_compute; reflexivity. Qed.

Definition prerequisite_fields (_ _ : nat) := 0.
Definition prerequisite_copy_all (_ : nat) := true.
Definition builder_alias_client : statement A := sequence
  [::New 0 0; Call 0 a; Copy 1 0; Call 0 b; Call 1 b; Call 0 x; Call 1 x].

Example builder_alias_client_accepted :
  check_program_with_copy builder_protocol prerequisite_fields
    prerequisite_copy_all builder_alias_client = true.
Proof. unfold builder_alias_client, prerequisite_copy_all. compute_prerequisites. Qed.
Example builder_alias_client_needs_inheritance :
  check_program builder_protocol prerequisite_fields builder_alias_client = false.
Proof. unfold builder_alias_client. compute_prerequisites. Qed.
Example builder_source_obligation_remains :
  check_program_with_copy builder_protocol prerequisite_fields prerequisite_copy_all
    (sequence [::New 0 0; Call 0 a; Call 0 b; Copy 1 0; Call 1 x]) = false.
Proof. unfold prerequisite_copy_all. compute_prerequisites. Qed.

Definition builder_alias_final : machine A :=
  let m := allocate initial_machine 0 0 in
  let m := emit m 0 a in
  let m := bind m 1 0 in
  let m := emit m 0 b in
  let m := emit m 1 b in
  clear_refs (emit (emit m 0 x) 1 x).

Example builder_alias_terminates :
  program_execution builder_alias_client initial_machine builder_alias_final.
Proof.
  unfold builder_alias_final. apply source_execution_instrument; [reflexivity|].
  unfold builder_alias_client; cbn [sequence].
  repeat (eapply execution_seq; [apply execution_primitive; econstructor; reflexivity|]);
    constructor.
Qed.
Example builder_alias_object_history :
  next_loc builder_alias_final = 1 /\
  object_history builder_alias_final 0 = [::a;b;b;x;x].
Proof. vm_compute; auto. Qed.

Theorem builder_alias_completion m :
  program_execution builder_alias_client initial_machine m ->
  forall l, (l < next_loc m)%coq_nat ->
    protocol builder_protocol (classes m l) (object_history m l).
Proof.
  apply (@prerequisite_checked_completion F builder_prerequisites
    prerequisite_fields prerequisite_copy_all).
  exact builder_alias_client_accepted.
Qed.

(* Exact finite-seed presentations. The auxiliary DFA stores a finite
   coverage frontier; every transition is checked and then mapped into the
   guarded state model, so the conclusion covers words of every length. *)
From RegLang Require Import dfa.
From Accumulation Require Import monotone_regular coverage_simulation
  pattern_seed_automata.

Definition prerequisite_code := Finite.clone (bool * bool * bool * bool)%type _.
Definition prerequisite_code_index (q : prerequisite_code) : nat :=
  let '(((b3,b2),b1),b0) := q in
  (if b3 then 8 else 0) + (if b2 then 4 else 0) +
  (if b1 then 2 else 0) + (if b0 then 1 else 0).
Definition prerequisite_code_of (n : nat) : prerequisite_code :=
  match n with
  | 0 => (false,false,false,false)
  | 1 => (false,false,false,true)
  | 2 => (false,false,true,false)
  | 3 => (false,false,true,true)
  | 4 => (false,true,false,false)
  | 5 => (false,true,false,true)
  | 6 => (false,true,true,false)
  | 7 => (false,true,true,true)
  | 8 => (true,false,false,false)
  | 9 => (true,false,false,true)
  | 10 => (true,false,true,false)
  | 11 => (true,false,true,true)
  | 12 => (true,true,false,false)
  | 13 => (true,true,false,true)
  | 14 => (true,true,true,false)
  | 15 => (true,true,true,true)
  | _ => (false,false,true,true)
  end.

Definition builder_frontier (q : prerequisite_code) : seq (state A) :=
  match prerequisite_code_index q with
  | 0 => [::([::],[::a;b;x]);([::],[::b;a;x])]
  | 1 => [::([::a],[::b;x])]
  | 2 => [::([::b],[::a;x])]
  | 3 => [::]
  | 4 => [::([::b;a],[::x])]
  | 5 => [::([::a;b],[::x])]
  | 6 => [::([::x;b;a],[::])]
  | 7 => [::([::x;a;b],[::])]
  | _ => [::]
  end.
Definition builder_frontier_step (q : prerequisite_code) (e : A) :=
  prerequisite_code_of (match prerequisite_code_index q, e with
  | 0, Some false => 1
  | 0, Some true => 2
  | 0, None => 3
  | 1, Some false => 1
  | 1, Some true => 4
  | 1, None => 3
  | 2, Some false => 5
  | 2, Some true => 2
  | 2, None => 3
  | 3, Some false => 3
  | 3, Some true => 3
  | 3, None => 3
  | 4, Some false => 4
  | 4, Some true => 4
  | 4, None => 6
  | 5, Some false => 5
  | 5, Some true => 5
  | 5, None => 7
  | 6, Some false => 6
  | 6, Some true => 6
  | 6, None => 6
  | 7, Some false => 7
  | 7, Some true => 7
  | 7, None => 7
  | _, _ => 3
  end).
Definition builder_frontier_dfa : dfa A :=
  {| dfa_state := prerequisite_code;
     dfa_s := prerequisite_code_of 0;
     dfa_fin := [set q | has (fun r : state A => r.2 == [::]) (builder_frontier q)];
     dfa_trans := builder_frontier_step |}.
Lemma builder_frontier_final q :
  has (fun r : state A => r.2 == [::]) (builder_frontier q) =
  (q \in dfa_fin builder_frontier_dfa).
Proof. by rewrite inE. Qed.
Lemma builder_frontier_transition q e :
  perm_eq (@advance A (builder_frontier q) e)
    (builder_frontier (@dfa_trans A builder_frontier_dfa q e)).
Proof.
  case: q => [[[[] []] []] []]; case: e => [[]|]; vm_compute; reflexivity.
Qed.
Lemma builder_seed_frontier_exact w :
  coveredb A builder_seeds w = (w \in dfa_lang builder_frontier_dfa).
Proof.
  apply (@finite_seed_automaton_correct A builder_frontier_dfa builder_frontier
    builder_frontier_final builder_frontier_transition builder_seeds).
  reflexivity.
Qed.

Definition builder_model_dfa := @machine_dfa A (prerequisite_states F)
  (prerequisite_machine builder_prerequisites)
  (prerequisite_enabled builder_prerequisites) (@prerequisite_completeb F)
  (prerequisite_initial F).
Definition builder_frontier_model (q : prerequisite_code) : option (prerequisite_states F) :=
  match prerequisite_code_index q with
  | 0 => Some (set0,false)
  | 1 => Some ([set false],false)
  | 2 => Some ([set true],false)
  | 3 => None
  | 4 => Some (setT,false)
  | 5 => Some (setT,false)
  | 6 => Some (setT,true)
  | 7 => Some (setT,true)
  | _ => None
  end.
Lemma builder_model_initial :
  builder_frontier_model (dfa_s builder_frontier_dfa) = dfa_s builder_model_dfa.
Proof. reflexivity. Qed.
Lemma builder_model_final q :
  (q \in dfa_fin builder_frontier_dfa) =
  (builder_frontier_model q \in dfa_fin builder_model_dfa).
Proof.
  case: q => [[[[] []] []] []]; rewrite !inE; reflexivity.
Qed.
Lemma builder_model_transition q e :
  builder_frontier_model (@dfa_trans A builder_frontier_dfa q e) =
  @dfa_trans A builder_model_dfa (builder_frontier_model q) e.
Proof.
  case: q => [[[[] []] []] []]; case: e => [[]|];
    cbv beta iota zeta delta [dfa_trans builder_frontier_dfa builder_frontier_step
      prerequisite_code_index prerequisite_code_of addn
      builder_frontier_model builder_model_dfa machine_dfa prerequisite_machine
      prerequisite_enabled prerequisite_step];
    repeat (progress (rewrite ?builder_guard_eval ?alternative_guard_eval
      ?two_features_all_eval ?two_features_any_eval ?inE /=));
    try reflexivity;
    do 2 f_equal; apply/setP; intros []; by rewrite !inE.
Qed.
Lemma builder_frontier_model_exact w :
  (w \in dfa_lang builder_frontier_dfa) = (w \in dfa_lang builder_model_dfa).
Proof.
  exact (@pattern_dfa_simulation_correct A builder_frontier_dfa builder_model_dfa
    builder_frontier_model builder_model_initial builder_model_final
    builder_model_transition w).
Qed.
Theorem builder_displayed_seeds_exact w :
  coveredb A builder_seeds w = accepts builder_protocol 0 w.
Proof.
  rewrite builder_seed_frontier_exact builder_frontier_model_exact.
  apply/idP/idP.
  - move=> H. apply prerequisite_accept_spec.
    apply (@machine_dfa_language A (prerequisite_states F)
      (prerequisite_machine builder_prerequisites)
      (prerequisite_enabled builder_prerequisites) (@prerequisite_completeb F)
      (prerequisite_enabled_spec builder_prerequisites)
      (prerequisite_completeb_spec builder_prerequisites)). exact H.
  - move=> H. apply (@machine_dfa_language A (prerequisite_states F)
      (prerequisite_machine builder_prerequisites)
      (prerequisite_enabled builder_prerequisites) (@prerequisite_completeb F)
      (prerequisite_enabled_spec builder_prerequisites)
      (prerequisite_completeb_spec builder_prerequisites)).
    apply prerequisite_accept_spec. exact H.
Qed.

Definition alternative_frontier (q : prerequisite_code) : seq (state A) :=
  match prerequisite_code_index q with
  | 0 => [::([::],[::a;x]);([::],[::b;x]);([::],[::a;b;x]);([::],[::a;x;b]);([::],[::b;a;x]);([::],[::b;x;a])]
  | 1 => [::([::a],[::x]);([::a],[::b;x]);([::a],[::x;b])]
  | 2 => [::([::b],[::x]);([::b],[::a;x]);([::b],[::x;a])]
  | 3 => [::]
  | 4 => [::([::b;a],[::x])]
  | 5 => [::([::x;a],[::]);([::x;a],[::b])]
  | 6 => [::([::a;b],[::x])]
  | 7 => [::([::x;b],[::]);([::x;b],[::a])]
  | 8 => [::([::x;b;a],[::])]
  | 9 => [::([::b;x;a],[::])]
  | 10 => [::([::x;a;b],[::])]
  | 11 => [::([::a;x;b],[::])]
  | _ => [::]
  end.
Definition alternative_frontier_step (q : prerequisite_code) (e : A) :=
  prerequisite_code_of (match prerequisite_code_index q, e with
  | 0, Some false => 1
  | 0, Some true => 2
  | 0, None => 3
  | 1, Some false => 1
  | 1, Some true => 4
  | 1, None => 5
  | 2, Some false => 6
  | 2, Some true => 2
  | 2, None => 7
  | 3, Some false => 3
  | 3, Some true => 3
  | 3, None => 3
  | 4, Some false => 4
  | 4, Some true => 4
  | 4, None => 8
  | 5, Some false => 5
  | 5, Some true => 9
  | 5, None => 5
  | 6, Some false => 6
  | 6, Some true => 6
  | 6, None => 10
  | 7, Some false => 11
  | 7, Some true => 7
  | 7, None => 7
  | 8, Some false => 8
  | 8, Some true => 8
  | 8, None => 8
  | 9, Some false => 9
  | 9, Some true => 9
  | 9, None => 9
  | 10, Some false => 10
  | 10, Some true => 10
  | 10, None => 10
  | 11, Some false => 11
  | 11, Some true => 11
  | 11, None => 11
  | _, _ => 3
  end).
Definition alternative_frontier_dfa : dfa A :=
  {| dfa_state := prerequisite_code;
     dfa_s := prerequisite_code_of 0;
     dfa_fin := [set q | has (fun r : state A => r.2 == [::]) (alternative_frontier q)];
     dfa_trans := alternative_frontier_step |}.
Lemma alternative_frontier_final q :
  has (fun r : state A => r.2 == [::]) (alternative_frontier q) =
  (q \in dfa_fin alternative_frontier_dfa).
Proof. by rewrite inE. Qed.
Lemma alternative_frontier_transition q e :
  perm_eq (@advance A (alternative_frontier q) e)
    (alternative_frontier (@dfa_trans A alternative_frontier_dfa q e)).
Proof.
  case: q => [[[[] []] []] []]; case: e => [[]|]; vm_compute; reflexivity.
Qed.
Lemma alternative_seed_frontier_exact w :
  coveredb A alternative_seeds w = (w \in dfa_lang alternative_frontier_dfa).
Proof.
  apply (@finite_seed_automaton_correct A alternative_frontier_dfa alternative_frontier
    alternative_frontier_final alternative_frontier_transition alternative_seeds).
  reflexivity.
Qed.

Definition alternative_model_dfa := @machine_dfa A (prerequisite_states F)
  (prerequisite_machine alternative_prerequisites)
  (prerequisite_enabled alternative_prerequisites) (@prerequisite_completeb F)
  (prerequisite_initial F).
Definition alternative_frontier_model (q : prerequisite_code) : option (prerequisite_states F) :=
  match prerequisite_code_index q with
  | 0 => Some (set0,false)
  | 1 => Some ([set false],false)
  | 2 => Some ([set true],false)
  | 3 => None
  | 4 => Some (setT,false)
  | 5 => Some ([set false],true)
  | 6 => Some (setT,false)
  | 7 => Some ([set true],true)
  | 8 => Some (setT,true)
  | 9 => Some (setT,true)
  | 10 => Some (setT,true)
  | 11 => Some (setT,true)
  | _ => None
  end.
Lemma alternative_model_initial :
  alternative_frontier_model (dfa_s alternative_frontier_dfa) = dfa_s alternative_model_dfa.
Proof. reflexivity. Qed.
Lemma alternative_model_final q :
  (q \in dfa_fin alternative_frontier_dfa) =
  (alternative_frontier_model q \in dfa_fin alternative_model_dfa).
Proof.
  case: q => [[[[] []] []] []]; rewrite !inE; reflexivity.
Qed.
Lemma alternative_model_transition q e :
  alternative_frontier_model (@dfa_trans A alternative_frontier_dfa q e) =
  @dfa_trans A alternative_model_dfa (alternative_frontier_model q) e.
Proof.
  case: q => [[[[] []] []] []]; case: e => [[]|];
    cbv beta iota zeta delta [dfa_trans alternative_frontier_dfa alternative_frontier_step
      prerequisite_code_index prerequisite_code_of addn
      alternative_frontier_model alternative_model_dfa machine_dfa prerequisite_machine
      prerequisite_enabled prerequisite_step];
    repeat (progress (rewrite ?builder_guard_eval ?alternative_guard_eval
      ?two_features_all_eval ?two_features_any_eval ?inE /=));
    try reflexivity;
    do 2 f_equal; apply/setP; intros []; by rewrite !inE.
Qed.
Lemma alternative_frontier_model_exact w :
  (w \in dfa_lang alternative_frontier_dfa) = (w \in dfa_lang alternative_model_dfa).
Proof.
  exact (@pattern_dfa_simulation_correct A alternative_frontier_dfa alternative_model_dfa
    alternative_frontier_model alternative_model_initial alternative_model_final
    alternative_model_transition w).
Qed.
Theorem alternative_displayed_seeds_exact w :
  coveredb A alternative_seeds w = accepts alternative_protocol 0 w.
Proof.
  rewrite alternative_seed_frontier_exact alternative_frontier_model_exact.
  apply/idP/idP.
  - move=> H. apply prerequisite_accept_spec.
    apply (@machine_dfa_language A (prerequisite_states F)
      (prerequisite_machine alternative_prerequisites)
      (prerequisite_enabled alternative_prerequisites) (@prerequisite_completeb F)
      (prerequisite_enabled_spec alternative_prerequisites)
      (prerequisite_completeb_spec alternative_prerequisites)). exact H.
  - move=> H. apply (@machine_dfa_language A (prerequisite_states F)
      (prerequisite_machine alternative_prerequisites)
      (prerequisite_enabled alternative_prerequisites) (@prerequisite_completeb F)
      (prerequisite_enabled_spec alternative_prerequisites)
      (prerequisite_completeb_spec alternative_prerequisites)).
    apply prerequisite_accept_spec. exact H.
Qed.
