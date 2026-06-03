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

Section Pumping.
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
      
      have Hge : size w <= k.+1 by rewrite leqNgt Hlt.
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
End Pumping.

Section PumpingClosureRegularity.
  Variable char : finType.
  Notation word := (RegLang.languages.word char).
  Notation lang := (RegLang.languages.lang char).
  Notation dlang := (RegLang.languages.dlang char).

  Import RegLang.regexp.
  
  Notation regexp := (RegLang.regexp.regexp char).
  Variable d0 : char.

  (* Union of singleton symbols from the alphabet `X` *)
  Definition re_of_set (X : {set char}) : regexp :=
    \big[@Plus char / @Void char]_(c in X)
      (Atom c).

  Definition regex_lang (r : regexp) : dlang :=
    [pred w | w \in r].

  Definition closure_equiv (r s : regexp) :=
    forall w,
      @pumping_closure char d0 (regex_lang r) w <->
      @pumping_closure char d0 (regex_lang s) w.

  Fixpoint regexp_power (n : nat) (r : regexp) : regexp :=
    if n is n'.+1 then Conc r (regexp_power n' r) else Eps.

  Definition bounded_star_basis (r : regexp) : regexp :=
    \big[@Plus char / @Void char]_(k : 'I_(#|char|).+1)
      (regexp_power k r).

  Lemma bounded_star_basisP (r : regexp) (w : word) :
    reflect
      (exists k : 'I_(#|char|).+1, w \in regexp_power k r)
      (w \in bounded_star_basis r).
  Proof.
    rewrite /bounded_star_basis.
    apply: (iffP (big_plusP _ _ _)) => [[k _ Hk] | [k Hk]].
    - by exists k.
    - by exists k.
  Qed.

  Definition concat_word_lists (xs ys : seq word) : seq word :=
    flatten [seq [seq x ++ y | y <- ys] | x <- xs].

  Lemma concat_word_listsP xs ys w :
    reflect
      (exists x y, [/\ x \in xs, y \in ys & w = x ++ y])
      (w \in concat_word_lists xs ys).
  Proof.
    rewrite /concat_word_lists.
    apply: (iffP flattenP).
    - move=> [zs /mapP [x Hx ->] /mapP [y Hy ->]].
      by exists x, y; split.
    - move=> [x [y [Hx Hy ->]]].
      exists [seq x ++ y | y <- ys].
      + by apply/mapP; exists x.
      + by apply/mapP; exists y.
  Qed.

  Fixpoint star_free (r : regexp) : bool :=
    match r with
    | Void => true
    | Eps => true
    | Atom _ => true
    | Star _ => false
    | Plus r1 r2 => star_free r1 && star_free r2
    | Conc r1 r2 => star_free r1 && star_free r2
    end.

  Fixpoint words_of_star_free (r : regexp) : seq word :=
    match r with
    | Void => [::]
    | Eps => [:: [::]]
    | Atom a => [:: [:: a]]
    | Star _ => [::]
    | Plus r1 r2 => words_of_star_free r1 ++ words_of_star_free r2
    | Conc r1 r2 =>
        concat_word_lists (words_of_star_free r1) (words_of_star_free r2)
    end.

  Definition union_strings (ws : seq word) : regexp :=
    \big[@Plus char / @Void char]_(w <- ws)
      (String w).

  Lemma union_stringsP ws w :
    reflect (exists2 u, u \in ws & w = u) (w \in union_strings ws).
  Proof.
    rewrite /union_strings.
    apply: (iffP (big_plus_seqP _ _ _)) => [[u Hu]|[u Hu ->]].
    - by rewrite StringE inE => /eqP ->; exists u.
    - exists u => //.
      by rewrite StringE inE eq_refl.
  Qed.

  Lemma union_strings_correct ws w :
    (w \in union_strings ws) = (w \in ws).
  Proof.
    apply/idP/idP.
    - by case/union_stringsP=> u Hu ->.
    - move=> Hw. apply/union_stringsP. by exists w.
  Qed.

  Lemma words_of_star_free_correct r :
    star_free r ->
    forall w, (w \in r) = (w \in words_of_star_free r).
  Proof.
    elim: r => [| |a|r _|r1 IH1 r2 IH2|r1 IH1 r2 IH2] /=.
    - by move=> _ w; rewrite unfold_in /void.
    - by move=> _ [|x xs]; rewrite unfold_in /eps.
    - move=> _ w. rewrite unfold_in /atom.
      by case: w => [|x [|y ys]]; rewrite ?inE.
    - by case.
    - move/andP=> [Hr1 Hr2] w.
      by rewrite unfold_in /= !inE IH1 // IH2 // mem_cat.
    - move/andP=> [Hr1 Hr2] w.
      rewrite unfold_in /=.
      apply/idP/idP.
      + case/concP=> x [y [-> [Hx Hy]]].
        apply/concat_word_listsP.
        exists x, y; split=> //.
        * by rewrite -IH1.
        * by rewrite -IH2.
      + case/concat_word_listsP=> x [y [Hx Hy ->]].
        apply/concP; exists x; exists y; split=> //.
        split.
        * by rewrite IH1.
        * by rewrite IH2.
  Qed.

  Definition normalize_star_free (r : regexp) : regexp :=
    union_strings (words_of_star_free r).

  Lemma normalize_star_free_correct r :
    star_free r ->
    forall w, (w \in normalize_star_free r) = (w \in r).
  Proof.
    move=> Hr w.
    by rewrite /normalize_star_free union_strings_correct
      -words_of_star_free_correct.
  Qed.

  Definition finite_lang (L : dlang) :=
    exists ws : seq word, forall w, L w <-> w \in ws.

  Lemma star_free_finite (r : regexp) :
    star_free r -> finite_lang (regex_lang r).
  Proof.
    move=> Hr.
    exists (words_of_star_free r) => w.
    by rewrite /regex_lang inE words_of_star_free_correct.
  Qed.

  Lemma pumping_closure_monotone (L1 L2 : dlang) :
    {subset L1 <= L2} ->
    forall w,
      @pumping_closure char d0 L1 w ->
      @pumping_closure char d0 L2 w.
  Proof.
    move=> Hsub w Hclos.
    elim: Hclos => [u Hu | u v _ IH Hpump].
    - exact: pumping_closure_base (Hsub _ Hu).
    - exact: pumping_closure_step IH Hpump.
  Qed.

  Lemma pumping_closure_lift_singleton (L : dlang) (u w : word) :
    L u ->
    @pumping_closure char d0 (pred1 u) w ->
    @pumping_closure char d0 L w.
  Proof.
    move=> Hu Hclos.
    elim: Hclos => [v Hv | v v' _ IH Hpump].
    - move/eqP: Hv => ->. exact: pumping_closure_base Hu.
    - exact: pumping_closure_step IH Hpump.
  Qed.

  Lemma pumping_closure_lift_closure (L : dlang) (u w : word) :
    @pumping_closure char d0 L u ->
    @pumping_closure char d0 (pred1 u) w ->
    @pumping_closure char d0 L w.
  Proof.
    move=> Hu Hclos.
    elim: Hclos => [v Hv | v v' _ IH Hpump].
    - move/eqP: Hv => ->. exact: Hu.
    - exact: pumping_closure_step IH Hpump.
  Qed.

  Lemma regexp_power_in_star (r : regexp) n (w : word) :
    w \in regexp_power n r -> w \in Star r.
  Proof.
    elim: n w => [|n IH] w /=.
    - by move/eqP=> ->.
    - case/concP=> w1 [w2 [-> [Hw1 Hw2]]].
      exact: star_cat Hw1 (IH _ Hw2).
  Qed.

  Lemma bounded_star_basis_in_star (r : regexp) (w : word) :
    w \in bounded_star_basis r -> w \in Star r.
  Proof.
    case/bounded_star_basisP=> k Hk.
    exact: regexp_power_in_star Hk.
  Qed.

  Fixpoint word_symbols (u : word) : {set char} :=
    if u is a :: u' then [set a] :|: word_symbols u' else set0.

  Lemma word_symbols_cat (u v : word) :
    word_symbols (u ++ v) = word_symbols u :|: word_symbols v.
  Proof.
    elim: u => [|a u IH] /=.
    - by rewrite set0U.
    - by rewrite IH setUA.
  Qed.

  Lemma mem_word_symbols (u : word) c :
    c \in word_symbols u = (c \in u).
  Proof.
    elim: u => [|a u IH] /=.
    - by rewrite inE.
    - by rewrite !inE IH.
  Qed.

  Lemma subset_word_symbols_all (u v : word) :
    word_symbols u \subset word_symbols v ->
    all (fun c => c \in v) u.
  Proof.
    move=> Hsub.
    apply/allP=> c Hc.
    by rewrite -mem_word_symbols (subsetP Hsub) ?mem_word_symbols.
  Qed.

  Lemma pumping_insert_char_after_prefix (p s : word) c :
    c \in p ->
    @pumping char d0 (p ++ s) (p ++ c :: s).
  Proof.
    move=> Hc.
    have [i Hi Hnth] : exists2 i, i < size p & nth d0 p i = c.
    { exists (seq.index c p).
      - by rewrite index_mem.
      - by rewrite nth_index. }
    have Hp : 0 < size p := leq_ltn_trans (leq0n i) Hi.
    rewrite /pumping.
    apply/hasP; exists (size p).-1.
    - rewrite mem_iota add0n size_cat leq0n /=.
      by rewrite -{2}(prednK Hp) ltnS leq_addr.
    apply/andP; split.
    - rewrite size_cat.
      by rewrite -{2}(prednK Hp) ltnS leq_addr.
    apply/hasP; exists i.
    - by rewrite mem_iota add0n prednK.
    apply/andP; split.
    - by rewrite -ltnS prednK.
    apply/eqP.
    rewrite /pump_at prednK // take_size_cat // drop_size_cat //.
    by rewrite nth_cat Hi Hnth.
  Qed.

  Lemma all_mem_catl (p u : word) v :
    all (fun c => c \in p) v ->
    all (fun c => c \in p ++ u) v.
  Proof.
    move/allP=> Hall.
    apply/allP=> c Hcin.
    have Hc := Hall c Hcin.
    by rewrite mem_cat Hc.
  Qed.

  Lemma pumping_insert_block_after_prefix (p block s : word) :
    all (fun c => c \in p) block ->
    @pumping_closure char d0 (pred1 (p ++ s)) (p ++ block ++ s).
  Proof.
    elim: block p s => [|c block IH] p s /=.
    - move=> _.
      exact: (@pumping_closure_base char d0 (pred1 (p ++ s)) (p ++ s) (eq_refl _)).
    - move/andP=> [Hc Hall].
      have Hstep :
        @pumping char d0 (p ++ s) (p ++ c :: s) :=
        pumping_insert_char_after_prefix p s c Hc.
      have Hfirst :
        @pumping_closure char d0 (pred1 (p ++ s)) (p ++ c :: s) :=
        @pumping_closure_step char d0 (pred1 (p ++ s))
          (p ++ s) (p ++ c :: s)
          (@pumping_closure_base char d0 (pred1 (p ++ s)) (p ++ s) (eq_refl _))
          Hstep.
      have Hrest :
        @pumping_closure char d0 (pred1 (p ++ c :: s))
          (p ++ c :: block ++ s).
      { have := IH (p ++ [:: c]) s (all_mem_catl p [:: c] block Hall).
        by rewrite -!catA /=. }
      exact: pumping_closure_lift_closure Hfirst Hrest.
  Qed.

  Fixpoint factor_basis (p : word) (vv : seq word) : seq word :=
    if vv is v :: vs then
      if word_symbols v \subset word_symbols p then factor_basis p vs
      else v :: factor_basis (p ++ v) vs
    else [::].

  Lemma factor_basis_replay (p : word) (vv : seq word) :
    @pumping_closure char d0
      (pred1 (p ++ flatten (factor_basis p vv)))
      (p ++ flatten vv).
  Proof.
    elim: vv p => [|v vs IH] p /=.
    - exact: (@pumping_closure_base char d0
        (pred1 (p ++ [::])) (p ++ [::]) (eq_refl _)).
    - case Hsub: (word_symbols v \subset word_symbols p).
      + have Hrec := IH p.
        have Hall : all (fun c => c \in p) v :=
          subset_word_symbols_all v p Hsub.
        have Hins :
          @pumping_closure char d0 (pred1 (p ++ flatten vs))
            (p ++ v ++ flatten vs) :=
          pumping_insert_block_after_prefix p v (flatten vs) Hall.
        exact: pumping_closure_lift_closure Hrec Hins.
      + have Hrec := IH (p ++ v).
        by rewrite -!catA /= in Hrec.
  Qed.

  Lemma regexp_power_flatten (r : regexp) (vv : seq word) :
    all (fun v => v \in r) vv ->
    flatten vv \in regexp_power (size vv) r.
  Proof.
    elim: vv => [|v vs IH] //=.
    move/andP=> [Hv Hvs].
    apply/concP.
    exists v; exists (flatten vs); split=> //.
    by split=> //; exact: IH.
  Qed.

  Lemma factor_basis_all (r : regexp) p vv :
    all (fun v => v \in r) vv ->
    all (fun v => v \in r) (factor_basis p vv).
  Proof.
    elim: vv p => [|v vs IH] p //=.
    move/andP=> [Hv Hvs].
    case: ifP => _.
    - exact: IH _ Hvs.
    - by rewrite /= Hv (IH _ Hvs).
  Qed.

  Lemma factor_basis_size (p : word) (vv : seq word) :
    size (factor_basis p vv) + #|word_symbols p| <= #|char|.
  Proof.
    elim: vv p => [|v vs IH] p /=.
    - rewrite add0n. exact: max_card.
    - case Hsub: (word_symbols v \subset word_symbols p).
      + exact: IH.
      + have IH' := IH (p ++ v).
        rewrite word_symbols_cat in IH'.
        have Hproper :
          word_symbols p \proper word_symbols p :|: word_symbols v.
        { apply: properUl.
          by rewrite Hsub. }
        have Hlt : #|word_symbols p| < #|word_symbols p :|: word_symbols v| :=
          proper_card Hproper.
        apply: (leq_trans _ IH').
        by rewrite addSn -addnS leq_add2l.
  Qed.

  Lemma pumping_closure_bounded_star_basis_to_star (r : regexp) :
    forall w,
      @pumping_closure char d0 (regex_lang (bounded_star_basis r)) w ->
      @pumping_closure char d0 (regex_lang (Star r)) w.
  Proof.
    apply: pumping_closure_monotone => w.
    exact: bounded_star_basis_in_star.
  Qed.

  (* Keystone compression lemma for the finite-basis theorem:
     any word in r* can be obtained by pumping from a word made of at most
     #|char| many r-factors. *)
  Lemma star_has_bounded_pumping_basis (r : regexp) (w : word) :
    w \in Star r ->
    exists u,
      [/\ u \in bounded_star_basis r
        & @pumping_closure char d0 (pred1 u) w].
  Proof.
    case/starP=> vv Hall ->.
    pose bs := factor_basis [::] vv.
    exists (flatten bs); split.
    - apply/bounded_star_basisP.
      have Hsize : size bs < (#|char|).+1.
      { rewrite -ltnS.
        have := factor_basis_size [::] vv.
        by rewrite /bs /= cards0 addn0. }
      exists (Ordinal Hsize).
      have Hr : all (fun v => v \in r) vv.
      { apply/allP=> v Hv.
        move/allP: Hall => /(_ v Hv).
        by case/andP. }
      have Hbs : all (fun v => v \in r) bs :=
        factor_basis_all r [::] vv Hr.
      have Hpow : flatten bs \in regexp_power (size bs) r :=
        regexp_power_flatten r bs Hbs.
      exact: Hpow.
    - have Hreplay := factor_basis_replay [::] vv.
      by rewrite /bs in Hreplay.
  Qed.

  Lemma pumping_closure_star_to_bounded_star_basis (r : regexp) :
    forall w,
      @pumping_closure char d0 (regex_lang (Star r)) w ->
      @pumping_closure char d0 (regex_lang (bounded_star_basis r)) w.
  Proof.
    move=> w Hclos.
    elim: Hclos => [u Hu | u v _ IH Hpump].
    - case: (star_has_bounded_pumping_basis r u Hu) => x [Hx Hxu].
      exact: pumping_closure_lift_singleton Hx Hxu.
    - exact: pumping_closure_step IH Hpump.
  Qed.

  Theorem pumping_closure_star_finite_basis (r : regexp) :
    closure_equiv (Star r) (bounded_star_basis r).
  Proof.
    move=> w; split.
    - exact: pumping_closure_star_to_bounded_star_basis.
    - exact: pumping_closure_bounded_star_basis_to_star.
  Qed.

End PumpingClosureRegularity.
