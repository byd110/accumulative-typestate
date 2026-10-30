(* Finite, executable certification of normalized regular seeds. *)
From Coq Require Import List Bool.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import regexp.
From Accumulation Require Import pumping trace_languages finite_shuffles coverage coverage_simulation.
Set Implicit Arguments.

Section Certification.
Variable A : finType.
Variable default : A.

Lemma mem_list_in (T : eqType) (x : T) xs : (x \in xs) <-> List.In x xs.
Proof.
  elim: xs => [|y ys IH] /=; first by split.
  rewrite seq.in_cons. split.
  - move/orP=> [/eqP ->|/IH H]; by [left|right].
  - case=> [->|/IH H]; apply/orP; [left; apply/eqP|right]; auto.
Qed.

Lemma interleaving_shuffle (u v w : seq A) :
  @pumping.interleaving A u v w <-> trace_languages.shuffle u v w.
Proof.
  split.
  - intros H; induction H.
    + apply shuffle_nil_left.
    + apply shuffle_nil_right.
    + now apply shuffle_left.
    + now apply shuffle_right.
  - intros H; induction H.
    + apply interleaving_nil_l.
    + now apply interleaving_left.
    + now apply interleaving_right.
Qed.

Definition coverb (seed w : seq A) := covers_simulation A seed w.
Lemma coverb_spec seed w : coverb seed w = true <-> @seed_covers A default seed w.
Proof. unfold coverb; rewrite covers_simulation_correct; apply (covers_spec A default). Qed.
Definition coveredb (seeds : seq (seq A)) w := List.existsb (fun seed => coverb seed w) seeds.
Definition certify_seeds (seeds : seq (seq A)) :=
  List.forallb (fun u => List.forallb (fun v =>
    List.forallb (coveredb seeds) (shuffles u v)) seeds) seeds.
Definition seed_language (seeds : seq (seq A)) : dlang_base A :=
  [pred w | w \in seeds].

Lemma coveredb_spec seeds w : coveredb seeds w = true <->
  @covered_by A default (seed_language seeds) w.
Proof.
  unfold coveredb, covered_by; rewrite List.existsb_exists; split.
  - intros [s [Hin Hc]]; exists s.
    + apply mem_list_in; exact Hin.
    + now apply coverb_spec.
  - intros [s Hin Hc]; exists s; split.
    + apply mem_list_in; exact Hin.
    + now apply coverb_spec.
Qed.

Theorem certify_seeds_spec seeds : certify_seeds seeds = true <->
  @pumping.shuffle_closed A (@pumping_closure_lang A default (seed_language seeds)).
Proof.
  rewrite <- base_shuffle_coveredP.
  unfold certify_seeds, base_shuffle_covered, seed_shuffle_covered.
  rewrite List.forallb_forall; split.
  - intros H u v w Hu Hv Hw.
    apply coveredb_spec.
    specialize (H u (proj1 (mem_list_in u seeds) Hu)).
    rewrite List.forallb_forall in H.
    specialize (H v (proj1 (mem_list_in v seeds) Hv)).
    rewrite List.forallb_forall in H. apply H.
    apply shuffles_spec, interleaving_shuffle; exact Hw.
  - intros H u Hu; apply List.forallb_forall; intros v Hv.
    apply List.forallb_forall; intros w Hw; apply coveredb_spec.
    apply H with u v.
    + apply mem_list_in; exact Hu.
    + apply mem_list_in; exact Hv.
    + apply interleaving_shuffle, shuffles_spec; exact Hw.
Qed.

Definition normalized_seeds (r : regexp A) := words_of_star_free A (eliminate_star A r).
Definition certify_regex (r : regexp A) := certify_seeds (normalized_seeds r).

Lemma normalized_closure r w :
  @pumping_closure A default (regex_lang A r) w <->
  @pumping_closure A default (seed_language (normalized_seeds r)) w.
Proof.
  rewrite (pumping_normalize_correct A default r w) pumping_normalize_is_union_strings.
  split; apply: pumping_closure_monotone => u;
    by rewrite /regex_lang /seed_language /= union_strings_correct.
Qed.

Theorem certify_regex_spec r : certify_regex r = true <->
  @pumping.shuffle_closed A (@pumping_closure_lang A default (regex_lang A r)).
Proof.
  unfold certify_regex; rewrite certify_seeds_spec.
  unfold pumping.shuffle_closed, pumping_closure_lang; split; intros H u v w Hu Hv Hs.
  - apply normalized_closure. apply H with u v; auto; now apply normalized_closure.
  - apply normalized_closure. apply H with u v; auto; now apply normalized_closure.
Qed.

(* Rejection returns a checked witness, not a timeout or an inconclusive result. *)
Definition shuffle_candidates (seeds : seq (seq A)) :=
  List.flat_map (fun u => List.flat_map (fun v =>
    List.map (fun w => (u,v,w)) (shuffles u v)) seeds) seeds.
Definition counterexample seeds :=
  List.find (fun t => negb (coveredb seeds (snd t))) (shuffle_candidates seeds).

Lemma shuffle_candidates_spec seeds u v w :
  List.In (u,v,w) (shuffle_candidates seeds) <->
  List.In u seeds /\ List.In v seeds /\ @interleaving A u v w.
Proof.
  unfold shuffle_candidates; rewrite List.in_flat_map; split.
  - intros [u' [Hu Hrest]]; apply List.in_flat_map in Hrest.
    destruct Hrest as [v' [Hv Hrest]]; apply List.in_map_iff in Hrest.
    destruct Hrest as [w' [E Hw]]; inversion E; subst.
    repeat split; auto. apply interleaving_shuffle, shuffles_spec; exact Hw.
  - intros [Hu [Hv Hw]]; exists u; split; auto.
    apply List.in_flat_map; exists v; split; auto.
    apply List.in_map_iff; exists w; split; auto.
    apply shuffles_spec, interleaving_shuffle; exact Hw.
Qed.

Theorem counterexample_sound seeds u v w : counterexample seeds = Some (u,v,w) ->
  @pumping_closure A default (seed_language seeds) u /\
  @pumping_closure A default (seed_language seeds) v /\
  @interleaving A u v w /\
  ~ @pumping_closure A default (seed_language seeds) w.
Proof.
  unfold counterexample; intros H; apply List.find_some in H.
  destruct H as [Hin Hbad]; apply shuffle_candidates_spec in Hin.
  destruct Hin as [Hu [Hv Hw]]; simpl in Hbad.
  repeat split.
  - apply pumping_closure_base, mem_list_in; exact Hu.
  - apply pumping_closure_base, mem_list_in; exact Hv.
  - exact Hw.
  - intros HC. apply negb_true_iff in Hbad.
    assert (coveredb seeds w = true).
    { apply coveredb_spec. apply (proj1 (pumping_closure_seed_corpus A default (seed_language seeds) w)); exact HC. }
    congruence.
Qed.

Theorem counterexample_none seeds : counterexample seeds = None <-> certify_seeds seeds = true.
Proof.
  split.
  - intros Hnone. apply certify_seeds_spec, (proj1 (base_shuffle_coveredP A default (seed_language seeds))).
    intros u v w Hu Hv Hw. apply coveredb_spec.
    assert (Hin : List.In (u,v,w) (shuffle_candidates seeds)).
    { apply shuffle_candidates_spec; repeat split; auto; apply mem_list_in; assumption. }
    assert (H : negb (coveredb seeds w) = false).
    { exact (@List.find_none _ (fun t => negb (coveredb seeds (snd t))) _ Hnone (u,v,w) Hin). }
    apply negb_false_iff in H; exact H.
  - intros HC; destruct (counterexample seeds) as [[[u v] w]|] eqn:E; auto.
    exfalso; destruct (counterexample_sound seeds E) as [Hu [Hv [Hs Hbad]]].
    apply Hbad; apply (proj1 (certify_seeds_spec seeds) HC) with u v; assumption.
Qed.

Definition regex_counterexample (r : regexp A) := counterexample (normalized_seeds r).
Theorem regex_counterexample_sound r u v w : regex_counterexample r = Some (u,v,w) ->
  @pumping_closure A default (regex_lang A r) u /\
  @pumping_closure A default (regex_lang A r) v /\
  @interleaving A u v w /\
  ~ @pumping_closure A default (regex_lang A r) w.
Proof.
  intros H; apply counterexample_sound in H; destruct H as [Hu [Hv [Hs Hw]]].
  repeat split; auto; try (apply normalized_closure; assumption).
  intros E; apply Hw; now apply normalized_closure.
Qed.
End Certification.
