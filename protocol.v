(* definition for protocol and its compliance at language level *)

Require Import RegLang.languages.
Require Import RegLang.nfa RegLang.dfa.
Require Import RegLang.regexp.

Require Import String List.
Import ListNotations.
Open Scope string_scope.

From mathcomp Require Import all_ssreflect.
Require Import Coq.Strings.String.

Section FormalLanguage.
  (* Use types from RegLang/languages.v *)
  Variable char : eqType.
  Definition word_base := RegLang.languages.word char.
  Definition dlang_base := RegLang.languages.dlang char.

  Variable a : char.

  (* only_a_dlang: words containing only "a" *)
  Definition only_a_dlang : dlang_base :=
    [pred w | all (fun x => x == a) w].

  Lemma aa_in_only_a_dlang : [:: a; a] \in only_a_dlang.
  Proof.
    rewrite /only_a_dlang inE /= eq_refl//.
  Qed.

  Definition even_a_dlang : dlang_base :=
    [pred w | ~~ odd (count (fun x => x == a) w)].


End FormalLanguage.

Section PumpingWord.
  (* Placeholder for pumping word lemma or definitions *)
  (* Use types from RegLang/languages.v *)
  Variable char : finType.
  Definition word := word_base char.
  Definition dlang := dlang_base char.
  Definition lang := RegLang.languages.lang char.

  (* First, define pumping operation *)
  Variable d0 : char.

  (* The way to interprete it: pumping w at position k with the letter at position i *)
  Definition pump_at (w : word) (k i : nat) : word :=
    take (k.+1) w ++ nth d0 w i :: drop (k.+1) w.

    (* `has` is bool definition of exists. `has pred set`: exists x in set st. pred x = true *)
    (* pumping is defined as: there exists a integer k in range [0, size w - 1], such that
    k < size w, and there exists another i in range [0, k] such that w' is obtained by 
    pumping w at position k with the letter at position i *)
  Definition pumping (w w' : word) : bool :=
    has (fun k =>
           (k < size w) &&
           has (fun i => (i <= k) && (w' == pump_at w k i))
               (iota 0 (k.+1)))
        (iota 0 (size w)).

  Variables a1 a2 a3 a4 : char.

  Definition w_abcd := [:: a1; a2; a3; a4].
  Definition w_abcd_pumped := [:: a1; a2; a3; a2; a4].

  Lemma pumping_w_abcd_pumped :
    pumping w_abcd w_abcd_pumped.
  Proof.
    rewrite /pumping.
    apply/hasP. exists 2. by []. apply/andP. split. by [].
    apply/hasP. exists 1. by []. apply/andP. by [].
  Qed.

  (* The closure is defined with two cases: 
  1. the langauge L is in the closure,
  2. for any word in the closure, all the pumping word of that word are also in the closure *)
  Inductive pumping_closure (L : dlang) : lang :=
  | pumping_closure_base w :
      L w -> pumping_closure L w
  | pumping_closure_step w w' :
      pumping_closure L w -> pumping w w' ->
      pumping_closure L w'.

    (* `flatten` smash a seq of seq into a single seq via concatenation.
       `map` applies a function to each element of a seq. `map ._+1 [:: 1; 2]` = [:: 2; 3] *)
    (* The succs obtains all the pumping word of a given word u. It first loop over pumping
    position k in range [0, size u - 1], then internally loops over letter position i in 
    range [0, k]. Finally, it flatten the resulting words into a single seq. *)
  Definition pump_succs (u : word) : seq word :=
    flatten (map (fun k => map (fun i => pump_at u k i) (iota 0 (k.+1)))
                 (iota 0 (size u))).

  Lemma pump_succs_sound (u v : word) :
    v \in pump_succs u -> pumping u v.
  Proof.
    move/flattenP=> [ks ks_in v_in].
    move/mapP: ks_in => [k k_in ks_eq]. rewrite ks_eq in v_in. 
    move/mapP: v_in => [i i_in ->].
    apply/hasP; exists k.
      by move: k_in; rewrite mem_iota. apply/andP; split. 
      by move: k_in; rewrite mem_iota.  
    apply/hasP; exists i; first by [].
      apply/andP; split.
        by move: i_in; rewrite mem_iota. 
        by rewrite eq_refl.
  Qed.
                
  (* reachable is defining this transitive closure, i.e. either
  1. u == v, or
  2. there exists u' such that u' is a pumping of u and reachable (m-1) u' v *)
  (* reachable m u v : there is a chain of m pump steps from u to v *)
  Fixpoint reachable (m : nat) (u v : word) : bool :=
    if m is m'.+1 then has (fun u' => reachable m' u' v) (pump_succs u)
    else (u == v).

  (* decidable pumping-closure for a singleton language w0:
     w is in the closure of [pred1 w0] iff size w >= size w0 and
     there is a chain of (size w - size w0) pump steps from w0 to w. *)
  Definition pumping_closure_singleton_dlang (w0 : word) : dlang :=
    fun w => if size w < size w0 then false else reachable (size w - size w0) w0 w.

  (* Lemma: reachable is closed under one more pumping step *)
  Lemma reachable_step m u v v' :
    reachable m u v -> pumping v v' -> reachable m.+1 u v'.
  Proof.
    elim: m u v v' => [|m IH] u v v' //=.
      (* m = 0: reachable 0 u v means u == v, so u = v. *)
      (* pumping v v' means pump_succs u contains v', so reachable 1 u v' *)
      move/eqP; move=> <- Hpump.
      have : v' \in pump_succs u.
      { rewrite /pump_succs. (* pumping v v' gives existence of k,i such that ... *)
        (* we unfold pumping to expose the witness *)
        rewrite /pumping in Hpump. move /hasP : Hpump => [k Hk].
        move/andP => [Hk1 Hk2]. move/hasP : Hk2 => [i Hi].
        move/andP => [Hi1 /eqP Hi2]. apply/flattenP. exists [seq pump_at u k i0  | i0 <- iota 0 k.+1].
        apply/mapP. by exists k. apply/mapP. by exists i.
      }
      move => Hin //=. apply/hasP. by exists v'.
    (* m > 0: apply inductive hypothesis *)
    - move/hasP => [u1 Hu1] Hrec Hpump. have H1 := IH u1 v v' Hrec Hpump.
      apply/hasP. by exists u1. 
  Qed.

  (* Forward direction: inductive pumping_closure -> there exists m with reachable m w0 w *)
  Lemma pumping_closure_to_reachable (w0 : word) :
    forall w, (pumping_closure (pred1 w0) w) -> exists m, reachable m w0 w = true.
  Proof.
    move=> w Hw.
    elim: Hw => [w' Hbase | w1 w2 Hclosure Hrec Hpump].
    - (* base: w' is w0 *)
      move/eqP in Hbase. rewrite /pred1 in Hbase.
      rewrite /reachable. exists 0. by apply/eqP.
    - (* step *)
      move: Hrec => [m Hrec].
      (* Hm : reachable m w0 w1 = true, Hpump : pumping w1 w2 *)
      exists m.+1.
      by apply: (reachable_step m w0 w1 w2 Hrec Hpump).
  Qed.

  (* Backward direction: reachable implies inductive pumping_closure (for singleton w0) *)
  Lemma reachable_closure (w0 : word) :
    forall m u w,
      pumping_closure (pred1 w0) u ->
      reachable m u w ->
      pumping_closure (pred1 w0) w.
  Proof.
    elim=> [|m IH] u w Hu /=.
    - move/eqP=> <-; exact Hu.
    - move/hasP=> [u' u'_in hreach].
      have Hstep : pumping u u' := pump_succs_sound _ _ u'_in.
      have Hu' : pumping_closure (pred1 w0) u' :=
        pumping_closure_step (pred1 w0) u u' Hu Hstep.
      exact: (IH _ _ Hu' hreach).
  Qed.

  Lemma reachable_to_pumping_closure (w0 : word) :
    forall m w, reachable m w0 w -> pumping_closure (pred1 w0) w.
  Proof.
    move=> m w hreach.
    apply: (reachable_closure w0 m w0 w).
    - by apply pumping_closure_base, eq_refl.
    - exact hreach.
  Qed.

  Lemma pump_at_size (w : word) (k i : nat) :
    k < size w -> size (pump_at w k i) = size w + 1.
  Proof.
    move=> Hk. rewrite /pump_at size_cat size_take /= size_drop. 
    rewrite addn1. case: ifP=> Hlt.
      have hk : k.+1 <= size w := ltnW Hlt.
      rewrite addnS.
      by rewrite (subnKC hk).
      
      have Hge : size w <= k.+1 by rewrite leqNgt Hlt. Search "leq_".
      have hke : k.+1 = size w. apply/eqP. by rewrite eqn_leq Hk Hge.
      by rewrite hke subnn addn1.
  Qed.

  Lemma pumping_size (w w' : word) :
    pumping w w' -> size w' = size w + 1.
  Proof.
    rewrite /pumping.
    move/hasP=> [k Hk].
    move/andP=> [Hklt Hk2].
    move/hasP: Hk2 => [i Hi].
    move/andP=> [_ /eqP ->].
    exact: pump_at_size Hklt.
  Qed.

  Lemma reachable_size m u v :
    reachable m u v -> size v = size u + m.
  Proof.
    elim: m u v=> [|m IH] u v /=.
    - move/eqP=> <-. by rewrite addn0.
    - move/hasP=> [u' Hu' Hrec].
      have Hpump : pumping u u' := pump_succs_sound _ _ Hu'.
      have Hsize : size u' = size u + 1 := pumping_size u u' Hpump.
      have Hsize' : size v = size u' + m := IH _ _ Hrec.
      by rewrite Hsize' Hsize -addnA add1n.
  Qed.

  (* Equivalence: pumping_closure of singleton equals the decidable predicate pumping_closure_singleton_dlang *)
  Lemma pumping_closure_singleton_eq (w0 w : word) :
    (pumping_closure (pred1 w0) w) <-> (pumping_closure_singleton_dlang w0 w).
Proof.
    split.
    - move=> Hc.
      have [m Hreach] := pumping_closure_to_reachable w0 w Hc.
      have Hsize : size w = size w0 + m := reachable_size m w0 w Hreach.
      have Hge : size w0 <= size w by rewrite Hsize; exact: leq_addr.
      rewrite /pumping_closure_singleton_dlang.
      have hlt : size w < size w0 -> false. 
      { move=> Hlt. rewrite ltnNge in Hlt. by move/negP: Hlt => Hlt. }
      case: ifP => Hlt. by apply: hlt. have Hsize': size w = m + size w0 by rewrite addnC.
      by rewrite Hsize' addnK. 
    - move=> H.
      rewrite /pumping_closure_singleton_dlang in H.
      case: ifP H=> Hlt H; first by [].
      exact: (reachable_to_pumping_closure w0 _ _ H).
Qed. 

  Variable w0 : word.
  Let n := size w0.

  (* 0..n states that track the longest matched prefix of w0 *)
  Definition state := 'I_(n.+1).
  Definition q0 : state := inord 0.
  Definition is_final (q : state) : bool := (q == inord n).

  (* alphabet test used in transitions *)
  Definition sym_eq_nth (k : nat) (c : char) : bool := (c == nth d0 w0 k).

  (* NFA transitions from j on symbol c:
     - copy to any k <= j where c == w0[k]
     - advance to j+1 if j < n and c == w0[j] *)
  Definition nfa_delta (j : state) (c : char) : seq state :=
    let jn := val j in
    let copies := [seq inord k | k <- iota 0 jn.+1] in
    let copies' := [seq s <- copies | sym_eq_nth (val s) c] in
    let adv := if (jn < n) && sym_eq_nth jn c then [:: inord jn.+1] else [::] in
    copies' ++ adv.

  (* NFA acceptance as a boolean (epsilon-free, so list search suffices) *)
  Fixpoint nfa_accepts_aux (q : state) (u : word) : bool :=
    if u is x :: xs
    then has (fun t => nfa_accepts_aux t xs) (nfa_delta q x)
    else is_final q.

  Definition nfa_accepts (w : word) : bool := nfa_accepts_aux q0 w.

  (* key equivalence: the NFA recognizes the same language as your decidable closure *)
  Lemma nfa_accepts_eq_pumping_closure_dlang (w : word) :
    nfa_accepts w = pumping_closure_dlang w0 w.
  Proof.
    (* Sketch:
       - Prove a stronger invariant: for any j, nfa_accepts_aux j w iff
         size w >= (n - j) and reachable (size w - (n - j)) (drop j w0) w,
         where the “reachable” is your step semantics, generalized from the seed.
       - Instantiate with j = 0 and simplify.
       Use structural induction on w. Each step matches your pumping “copy-or-advance”
       and is mirrored by the transition structure. *)
  Admitted.

  (* Approach B: regularity via a regular expression decomposition *)
    (* For each prefix j, the “stay” alphabet is the finite set S_j = {w0[k] | k ≤ j} *)
    Definition Sj (j : nat) : {set char} :=
    [set x | x \in [seq nth d0 w0 k | k <- iota 0 (minn (j.+1) (size w0))]].

    (* Regex for a finite set X: big union of singletons *)
    Definition re_of_set (X : {set char}) : RegLang.regexp.regexp char :=
      \big[RegLang.regexp.alt/RegLang.regexp.empty]_(c in X) RegLang.regexp.char c.

    (* Product regex: S0* · w0[0] · S1* · w0[1] · ... · Sn* *)
    Definition pumping_re : RegLang.regexp.regexp char :=
      let fix build (j : nat) :=
        match j with
        | 0    => RegLang.regexp.star (re_of_set (Sj 0))
        | j'.+1 =>
            RegLang.regexp.cat
              (build j')
              (RegLang.regexp.cat
                 (RegLang.regexp.char (nth d0 w0 j'))
                 (RegLang.regexp.star (re_of_set (Sj j'.+1))))
        end in build n.

    (* Semantics of the regex matches your decidable predicate *)
    Lemma pumping_re_correct (w : word) :
      RegLang.regexp.matches pumping_re w = pumping_closure_dlang w0 w.
    Proof.
      (* Induction over j with the invariant that “state j” language equals
         Sj* · w0[j] · Sj+1* · ... · Sn*; combine:
         - correctness of star/cat/alt semantics,
         - that Sj enumerates exactly the letters allowed by the pumping step,
         - and size-indexed reachable equals “number of steps” in your definition. *)
    Admitted.

    Theorem pumping_closure_singleton_regular_RE :
      RegLang.languages.regular (pumping_closure_dlang w0).
    Proof.
      (* RegLang provides that every regexp denotes a regular language *)
      have -> : pumping_closure_dlang w0 =1 RegLang.regexp.matches pumping_re.
      { by move=> w; rewrite -pumping_re_correct. }
      exact: RegLang.regexp.regular_of_regexp.
    Qed.

  (* Pick either theorem as the final statement. *)
  Theorem pumping_closure_singleton_regular :
    RegLang.languages.regular (pumping_closure_dlang w0).
  Proof. exact: pumping_closure_singleton_regular_RE. Qed.

(* Approach A: regularity via NFA -> DFA (subset construction in RegLang) *)
    (* Reuse RegLang's NFA API; names below follow RegLang/nfa.v and dfa.v.
       If names differ locally, adapt according to your install. *)

    (* Package the finite NFA structure expected by RegLang. *)
    (* States carry an eqType structure; 'I_(n.+1) has one already. *)
    Definition NFA_states := state.
    Definition NFA_start : NFA_states := q0.
    Definition NFA_final : {set NFA_states} := [set inord n].
    Definition NFA_step (q : NFA_states) (a : char) : {set NFA_states} :=
      [set t | t \in nfa_delta q a].

    Definition my_nfa : nfa char :=
      NFA.mk NFA_states NFA_start NFA_final NFA_step.

    (* Show the library NFA language equals nfa_accepts. *)
    Lemma nfa_lang_eq_accepts : RegLang.nfa.nfa_lang my_nfa =1 nfa_accepts.
    Proof.
      (* Unfold nfa_lang (path semantics) and show it coincides with
         nfa_accepts_aux; standard “has over step set” vs. small-step
         list recursion equivalence. *)
    Admitted.

    (* Conclude regularity using RegLang’s determinization theorem. *)
    Theorem pumping_closure_singleton_regular_NFA :
      RegLang.languages.regular (pumping_closure_dlang w0).
    Proof.
      (* determinize my_nfa to a DFA and use correctness *)
      have -> : pumping_closure_dlang w0 =1 nfa_accepts.
      { move=> w; rewrite -nfa_accepts_eq_pumping_closure_dlang. by []. }
      have -> : nfa_accepts =1 RegLang.nfa.nfa_lang my_nfa.
      { by move=> w; rewrite -nfa_lang_eq_accepts. }
      (* RegLang provides: regular (nfa_lang N) via subset construction *)
      exact: RegLang.nfa.nfa_regular.
    Qed.

  (* Variable w0 : word.
  Let n := size w0.

  (* finite states 0 .. n *)
  Definition state := 'I_(n.+1).

  (* convenience: ordinal -> nat *)
  Definition state_to_nat (s : state) : nat := val s.

  (* final/accepting state: n *)
  Definition is_final (s : state) : bool := (s == inord n).

  (* compare a character with nth char of w0 at index k *)
  Definition sym_eq_nth (k : nat) (c : char) : bool := (c == nth d0 w0 k).

  (* transitions from state j on symbol c:
      - copy transitions to every k <= j where c == nth w0 k
      - advance transition to j+1 if j < n and c == nth w0 j
      We enumerate targets as a seq state so acceptance can be defined by has/exists.
      (Implementation uses iota/map/filter; proofs about indexes will use mem_iota.) *)
  Definition delta (j : state) (c : char) : seq state :=
    let jn := state_to_nat j in
    let copies := map inord (iota 0 jn.+1) in
    let copies' := filter (fun s => sym_eq_nth (state_to_nat s) c) copies in
    let adv := if (jn < n) && sym_eq_nth jn c then [:: inord jn.+1] else [::] in
    copies' ++ adv.

  (* acceptance as a recursive boolean predicate over input word *)
  Fixpoint accepts_aux (s : state) (u : word) : bool :=
    if u is x :: xs
    then has (fun t => (t \in delta s x) && accepts_aux t xs) (delta s x)
    else is_final s.

  Definition accepts (w : word) : bool := accepts_aux (inord 0) w.

  (* Soundness: if automaton accepts w then reachable (size w - n) w0 w *)
  Lemma accepts_sound (w : word) :
    accepts w -> size w >= n /\ reachable (size w - n) w0 w.
  Proof. admit. Qed.

  (* Completeness: if reachable (size w - n) w0 w then automaton accepts w *)
  Lemma accepts_complete (w : word) :
    size w >= n -> reachable (size w - n) w0 w -> accepts w.
  Proof. admit. Qed.

  (* Pointwise boolean equality between accepts and pumping_closure_dlang *)
  Lemma accepts_eq_pumping_closure_dlang (w : word) :
    accepts w = (if size w < n then false else reachable (size w - n) w0 w).
  Proof.
    rewrite /accepts.
    case: ifP => Hlt.
    - (* size w < n -> both sides false (automaton cannot reach final) *)
      admit.
    - (* size w >= n: use soundness/completeness to equate booleans *)
      admit.
  Admitted.

  (* Conclude regularity: pumping_closure_dlang w0 is recognised by this finite automaton.
      Here we state the theorem in terms of RegLang's notion of regularity.
      Use RegLang.nfa / languages results to finish the formal connection. *)
  Theorem pumping_closure_singleton_regular (w0' : word) :
    w0' = w0 -> RegLang.languages.regular (pumping_closure_dlang w0).
  Proof.
    move=> ->.
    (* replace pumping_closure_dlang by accepts using accepts_eq_pumping_closure_dlang,
        then build a RegLang.nfa from the finite structure {0..n} with delta/is_final and
        use the library lemma that nfa-recognisable => regular. *)
    admit.
  Qed. *)
End PumpingWord.
