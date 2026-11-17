(* A seed-certified protocol whose viable-prefix language violates
   Kellogg et al.'s first-error subsequence condition (ECOOP 2022, Def. 7).
   K = pc{ab, ac, aabc, abac, aacb, acab} is shuffle closed, so the
   fresh-history checker is sound for it, yet acb is a first error whose
   subsequence ab is viable. *)
From Coq Require Import List Bool.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import dfa regexp.
From Accumulation Require Import pumping certification regular_protocols protocols trace_languages
  residual_certification_examples accumulation_bridge syntax semantics typestate copying_typestate.
Set Implicit Arguments.

(* Pumping never creates a prefix of pairwise distinct letters: an inserted
   letter copies an earlier letter, which then occurs twice in that prefix. *)
Section UniqPrefix.
Variable char : finType.
Variable d0 : char.

Lemma pump_at_take_uniq (w : seq char) k i n :
  i <= k -> k < size w -> uniq (take n (pump_at char d0 w k i)) ->
  take n (pump_at char d0 w k i) = take n w.
Proof.
  move=> Hik Hk.
  have Hsz : size (take k.+1 w) = k.+1 by rewrite size_takel.
  rewrite /pump_at take_cat Hsz.
  case: ltnP => Hn; first by rewrite take_takel // ltnW.
  move: Hn; rewrite leq_eqVlt => /orP [/eqP <-|Hn].
    by rewrite subnn take0 cats0.
  case E: (n - k.+1) => [|m]; first by move/eqP: E; rewrite subn_eq0 leqNgt Hn.
  have Hx : nth d0 w i \in take k.+1 w
    by rewrite -(nth_take d0 (n0 := k.+1) (i := i)) ?ltnS // mem_nth // Hsz.
  by rewrite cat_uniq /= Hx /= andbF.
Qed.

Lemma pumping_take_uniq (w w' : seq char) n :
  pumping char d0 w w' -> uniq (take n w') -> take n w' = take n w.
Proof.
  move/hasP=> [k _ /andP [Hk /hasP [i _ /andP [Hik /eqP ->]]]].
  exact: (@pump_at_take_uniq w k i n Hik Hk).
Qed.

Lemma pumping_closure_take_uniq (L : pred (seq char)) w n :
  pumping_closure char d0 L w -> uniq (take n w) ->
  exists2 s, L s & take n s = take n w.
Proof.
  elim=> [u Hu | u v _ IH Hp] Hun; first by exists u.
  have E := @pumping_take_uniq u v n Hp Hun.
  rewrite E in Hun *. exact: IH.
Qed.
End UniqPrefix.

Local Notation B := (Finite.clone (option bool) _).
Local Notation a := (@None bool).
Local Notation b := (Some false).
Local Notation c := (Some true).

Lemma separating_seeds_avoid_acb :
  all (fun s => take 3 s != [:: a; c; b]) (normalized_seeds separating_regex).
Proof. by vm_compute. Qed.

(* acb has no completion: no seed starts with acb, and pumping preserves
   prefixes of distinct letters. *)
Lemma separating_acb_not_viable : viable separating_family 0 [:: a; c; b] = false.
Proof.
  apply Bool.not_true_is_false; rewrite viable_spec; move=> [v Hv].
  change (coveredb B (normalized_seeds separating_regex) ([:: a; c; b] ++ v) = true) in Hv.
  move/(@coveredb_spec B a _ _): Hv => [s Hs Hcov].
  have Hun : uniq (take 3 ([:: a; c; b] ++ v)) by rewrite /= take0; vm_compute.
  have [s' /eqP Es' Htake] := @pumping_closure_take_uniq _ _ _ _ 3 Hcov Hun.
  subst s'.
  move/allP/(_ s Hs): separating_seeds_avoid_acb.
  by rewrite Htake /= take0 eqxx.
Qed.

(* ac is viable and acb is a first error, but its subsequence ab is viable. *)
Example separating_prefix_not_kellogg :
  ~ kellogg_error_closed (prefix_language (protocol separating_family 0)).
Proof.
  intros H.
  have Hsub : trace_subsequence [:: a] [:: a; c].
  { constructor. constructor 3. constructor. }
  have Hac : prefix_language (protocol separating_family 0) [:: a; c].
  { apply viable_prefix, complete_viable, separating_ac_complete. }
  have Hacb : ~ prefix_language (protocol separating_family 0) [:: a; c; b].
  { rewrite -viable_prefix separating_acb_not_viable. discriminate. }
  apply (H [:: a] [:: a; c] b Hsub Hac Hacb).
  apply viable_prefix, complete_viable, separating_ab_complete.
Qed.

Theorem separating_certified_not_kellogg :
  certified separating_family /\
  ~ kellogg_error_closed (prefix_language (protocol separating_family 0)).
Proof.
  split; last exact: separating_prefix_not_kellogg.
  apply: (@regular_family_certified B a) => _.
  exact: separating_original_certificate.
Qed.

(* Ordinary shuffle certification is insufficient when assignments inherit
   histories.  This example deliberately runs the local copying checker
   without its required residual certificate.  The residual certificate used
   by check_regular_program_with_copy rejects this protocol, as witnessed by
   separating_copy_certificate_rejected in residual_certification_examples. *)
Local Fixpoint separating_block (instrs : list (instruction B)) : statement B :=
  match instrs with
  | nil => Skip
  | i :: rest => Seq (Do i) (separating_block rest)
  end.
Local Lemma separating_block_path instrs : path (separating_block instrs) instrs.
Proof.
  induction instrs as [|i instrs IH]; simpl; [constructor|].
  change (path (Seq (Do i) (separating_block instrs)) ([::i] ++ instrs)).
  constructor; [constructor|exact IH].
Qed.
Local Definition separating_fields (cl : class) (_ : field) := cl.

Definition separating_copy_program := separating_block
  [:: New 0 0; Call 0 a; Copy 1 0; Call 0 c; Call 1 b; Finish 0; Finish 1].

Local Lemma separating_initial_viable : viable separating_family 0 [::] = true.
Proof. apply viable_spec; exists [::a;b]; exact separating_ab_complete. Qed.
Local Lemma separating_a_viable : viable separating_family 0 [::a] = true.
Proof. apply viable_spec; exists [::b]; exact separating_ab_complete. Qed.
Local Lemma separating_ac_viable : viable separating_family 0 [::a;c] = true.
Proof. apply complete_viable; exact separating_ac_complete. Qed.
Local Lemma separating_ab_viable : viable separating_family 0 [::a;b] = true.
Proof. apply complete_viable; exact separating_ab_complete. Qed.

Example separating_copy_accepted_without_certificate :
  check_program_with_copy separating_family separating_fields (fun _ => true)
    separating_copy_program = true.
Proof.
  unfold check_program_with_copy, separating_copy_program.
  cbn [paths separating_block List.flat_map List.map List.app List.forallb
    check_trace_with_copy check_step_with_copy check_step check_bind retirable
    get put andb Nat.eqb].
  unfold check_bind, retirable; cbn [get andb Nat.eqb].
  rewrite separating_initial_viable.
  cbn [check_trace_with_copy check_step_with_copy check_step check_bind retirable
    get put andb Nat.eqb List.app].
  rewrite separating_a_viable.
  cbn [check_trace_with_copy check_step_with_copy check_step check_bind retirable
    get put andb Nat.eqb List.app].
  rewrite separating_ac_viable.
  cbn [check_trace_with_copy check_step_with_copy check_step check_bind retirable
    get put andb Nat.eqb List.app].
  rewrite separating_ab_viable.
  cbn [check_trace_with_copy check_step_with_copy check_step check_bind retirable
    get put andb Nat.eqb List.app].
  rewrite separating_ac_complete.
  cbn [check_trace_with_copy check_step_with_copy check_step check_bind retirable
    get put andb Nat.eqb List.app].
  rewrite separating_ab_complete.
  reflexivity.
Qed.

Definition separating_copy_final : machine B :=
  let m := allocate initial_machine 0 0 in
  let m := emit m 0 a in
  let m := bind m 1 0 in
  let m := emit m 0 c in
  let m := emit m 1 b in
  let m := retire m 0 in
  retire m 1.

Example separating_copy_terminates :
  program_execution separating_copy_program initial_machine separating_copy_final.
Proof.
  exists [:: New 0 0; Call 0 a; Copy 1 0; Call 0 c; Call 1 b; Finish 0; Finish 1].
  split; first exact: separating_block_path.
  unfold separating_copy_final.
  repeat (eapply execution_cons; [econstructor; reflexivity|]); constructor.
Qed.

Example separating_copy_actual_history :
  next_loc separating_copy_final = 1 /\ classes separating_copy_final 0 = 0 /\
  object_history separating_copy_final 0 = [::a;c;b].
Proof. vm_compute; auto. Qed.

Example separating_copy_actual_history_not_viable :
  ~ prefix_language (protocol separating_family (classes separating_copy_final 0))
    (object_history separating_copy_final 0).
Proof.
  change (~ prefix_language (protocol separating_family 0) [::a;c;b]).
  rewrite -viable_prefix separating_acb_not_viable. discriminate.
Qed.

Theorem separating_copy_unsound_without_residual_certificate :
  check_program_with_copy separating_family separating_fields (fun _ => true)
    separating_copy_program = true /\
  program_execution separating_copy_program initial_machine separating_copy_final /\
  (0 < next_loc separating_copy_final)%coq_nat /\
  ~ prefix_language (protocol separating_family (classes separating_copy_final 0))
    (object_history separating_copy_final 0).
Proof.
  split; first exact: separating_copy_accepted_without_certificate.
  split; first exact: separating_copy_terminates.
  split; first by compute.
  exact: separating_copy_actual_history_not_viable.
Qed.
