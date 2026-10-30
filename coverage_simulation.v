(* Reachable-state simulation for the singleton automaton. A state records
   consumed milestones (in reverse order) and the remaining seed suffix. *)
From Coq Require Import List.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import regexp.
From Accumulation Require Import pumping coverage.
Set Implicit Arguments.

Section Simulation.
Variable A : finType.
Notation word := (seq A).
Definition state := (word * word)%type.

Inductive replay : word -> word -> word -> Prop :=
| replay_done seen : replay seen [::] [::]
| replay_loop seen seed a out : a \in seen -> replay seen seed out ->
    replay seen seed (a::out)
| replay_next seen a seed out : replay (a::seen) seed out ->
    replay seen (a::seed) (a::out).

Lemma replay_block seen seed block out : all (fun a => a \in seen) block ->
  replay seen seed out -> replay seen seed (block ++ out).
Proof.
  elim: block => [|a block IH] //= /andP [Ha Hb] Hr.
  apply: replay_loop Ha _. exact: IH Hb Hr.
Qed.

Lemma replay_to_blocks seen seed out : replay seen seed out ->
  forall (X : {set A}), (forall c, (c \in X) = (c \in seen)) ->
  exists block rest, [/\ all (fun c => c \in seen) block,
    @pump_semantic A X seed rest & out = block ++ rest ].
Proof.
  move=> H; elim: H => [seen0|seen0 seed0 a out0 Ha Hr IH|seen0 a seed0 out0 Hr IH] X HX.
  - exists [::], [::]; split=> //; constructor.
  - have [block [rest [Hb Hsem ->]]] := IH X HX.
    exists (a::block), rest; split=> //=. by rewrite Ha Hb.
  - have HX' : forall c, (c \in X :|: [set a]) = (c \in a::seen0).
    { move=> c; by rewrite !inE HX orbC. }
    have [block [rest [Hb Hsem ->]]] := IH (X :|: [set a]) HX'.
    exists [::], (a::block ++ rest); split=> //.
    apply: pump_semantic_cons Hsem.
    apply/allP=> c Hc; have H := (allP Hb) c Hc. by rewrite HX'.
Qed.

Lemma semantic_to_replay X seed out : @pump_semantic A X seed out ->
  forall seen, (forall c, (c \in X) = (c \in seen)) -> replay seen seed out.
Proof.
  move=> H; elim: H => [X0|X0 a seed0 block out0 Hb Hr IH] seen HX.
  - constructor.
  - apply replay_next. apply: replay_block.
    + apply/allP=> c Hc; have H := (allP Hb) c Hc.
      by move: H; rewrite !inE HX orbC.
    + apply IH => c; by rewrite !inE HX orbC.
Qed.

Lemma replay_initial seed out : replay [::] seed out <-> @pump_semantic A set0 seed out.
Proof.
  split.
  - move=> H.
    have HX : forall c : A, (c \in set0) = (c \in [::]) by move=> c; rewrite inE.
    have [block [rest [Hb Hsem Heq]]] := replay_to_blocks H HX.
    case: block Hb Heq => [|a block] //= _ ->. exact Hsem.
  - move=> H; apply: (semantic_to_replay H). by move=> c; rewrite inE.
Qed.

Inductive transition (a : A) : state -> state -> Prop :=
| transition_loop seen seed : a \in seen -> transition a (seen,seed) (seen,seed)
| transition_next seen seed : transition a (seen,a::seed) (a::seen,seed).
Definition next_states (a : A) (q : state) : seq state :=
  (if a \in q.1 then [:: q] else [::]) ++
  match q.2 with
  | [::] => [::]
  | b::rest => if a == b then [:: (b::q.1,rest)] else [::]
  end.
Lemma next_statesP a p q : q \in next_states a p <-> transition a p q.
Proof.
  case: p => seen seed; rewrite /next_states /= mem_cat.
  split.
  - move/orP=> [H|H].
    + case: ifP H => Ha //; rewrite mem_seq1; move/eqP=> ->; exact: transition_loop.
    + case: seed => [|b rest] //= in H *.
      case: ifP H => [/eqP Hab|] //; rewrite mem_seq1; move/eqP=> ->; subst b; constructor.
  - move=> H; inversion H; subst.
    + apply/orP; left. have Ha : a \in seen by assumption. by rewrite Ha mem_seq1 eq_refl.
    + apply/orP; right. by rewrite eq_refl mem_seq1 eq_refl.
Qed.

Definition advance (frontier : seq state) a :=
  undup (flatten [seq next_states a q | q <- frontier]).
Fixpoint simulate (frontier : seq state) (out : word) :=
  match out with
  | [::] => has (fun q => q.2 == [::]) frontier
  | a::rest => simulate (advance frontier a) rest
  end.

Lemma advanceP frontier a q : q \in advance frontier a <->
  exists2 p, p \in frontier & transition a p q.
Proof.
  rewrite /advance mem_undup; split.
  - move/flattenP=> [qs /mapP [p Hp ->] Hq].
    exists p=> //; now apply next_statesP.
  - move=> [p Hp Hq]; apply/flattenP; exists (next_states a p).
    + apply/mapP; by exists p.
    + now apply next_statesP.
Qed.

Lemma simulateP out frontier : simulate frontier out <->
  exists2 q, q \in frontier & replay q.1 q.2 out.
Proof.
  elim: out frontier => [|a out IH] frontier /=.
  - split.
    + move/hasP=> [[seen seed] Hq /= /eqP Hseed]; subst seed.
      exists (seen,[::])=> //; constructor.
    + move=> [[seen seed] Hq H]; simpl in H; inversion H; subst.
      apply/hasP; exists (seen,[::])=> //; exact: eq_refl.
  - rewrite IH; split.
    + move=> [q /advanceP [p Hp Ht] Hr]. exists p=> //.
      inversion Ht; subst; simpl in *; [apply: replay_loop; eauto|apply: replay_next; eauto].
    + move=> [[seen seed] Hp Hr]. simpl in Hr; inversion Hr; subst.
      * exists (seen,seed); [apply advanceP; exists (seen,seed)=> //; constructor; assumption|assumption].
      * exists (a::seen,seed0); [apply advanceP; exists (seen,a::seed0)=> //; constructor|assumption].
Qed.

Definition covers_simulation seed out := simulate [:: ([::],seed)] out.
Theorem covers_simulation_correct seed out : covers_simulation seed out = covers A seed out.
Proof.
  apply/idP/idP.
  - move/simulateP=> [q]; rewrite mem_seq1; move/eqP=> -> /= Hr.
    rewrite covers_regex; apply/(pump_semanticP A set0 seed out).
    now apply replay_initial.
  - move=> H; apply/simulateP; exists ([::],seed).
    + by rewrite mem_seq1 eq_refl.
    + apply replay_initial. apply/(pump_semanticP A set0 seed out).
      by move: H; rewrite covers_regex.
Qed.

(* These configurations encode exactly the milestone positions 0..|seed|. *)
Definition state_origin (seed : word) (q : state) := rev q.1 ++ q.2 = seed.
Definition positions (seed : word) :=
  [seq (rev (take k seed), drop k seed) | k <- iota 0 (size seed).+1].
Lemma state_origin_position seed q : state_origin seed q -> q \in positions seed.
Proof.
  case: q => seen rest /=; rewrite /state_origin /= => <-.
  apply/mapP; exists (size seen).
  - rewrite mem_iota add0n leq0n size_cat size_rev ltnS; exact: leq_addr.
  - rewrite take_size_cat ?size_rev // drop_size_cat ?size_rev // revK; reflexivity.
Qed.
Lemma transition_origin seed a p q : state_origin seed p -> transition a p q -> state_origin seed q.
Proof.
  move=> H Hp; destruct Hp; auto.
  move: H; rewrite /state_origin /= rev_cons cat_rcons; auto.
Qed.
Lemma advance_origin seed frontier a :
  (forall q, q \in frontier -> state_origin seed q) ->
  forall q, q \in advance frontier a -> state_origin seed q.
Proof.
  move=> H q /advanceP [p Hp Ht]. apply: transition_origin Ht. exact: H Hp.
Qed.
Fixpoint run_states (frontier : seq state) (out : word) :=
  match out with [::] => frontier | a::rest => run_states (advance frontier a) rest end.
Lemma simulate_states out frontier :
  simulate frontier out = has (fun q => q.2 == [::]) (run_states frontier out).
Proof. by elim: out frontier => [|a out IH] frontier //=; apply IH. Qed.
Lemma run_states_origin seed out frontier :
  (forall q, q \in frontier -> state_origin seed q) ->
  forall q, q \in run_states frontier out -> state_origin seed q.
Proof.
  elim: out frontier => [|a out IH] frontier //= H.
  apply IH. exact: advance_origin H.
Qed.
Lemma run_states_uniq out frontier : uniq frontier -> uniq (run_states frontier out).
Proof.
  elim: out frontier => [|a out IH] frontier //= _.
  apply IH; exact: undup_uniq.
Qed.
Theorem simulation_state_bound seed out :
  size (run_states [:: ([::],seed)] out) <= (size seed).+1.
Proof.
  have HU : uniq (run_states [:: ([::],seed)] out) by apply run_states_uniq.
  have HO : forall q, q \in run_states [:: ([::],seed)] out -> state_origin seed q.
  { apply run_states_origin => q; rewrite mem_seq1; move/eqP=> ->; reflexivity. }
  have HM : {subset run_states [:: ([::],seed)] out <= positions seed}.
  { move=> q Hq; exact: state_origin_position (HO q Hq). }
  have Hsize := uniq_leq_size HU HM.
  by move: Hsize; rewrite /positions size_map size_iota.
Qed.
End Simulation.
