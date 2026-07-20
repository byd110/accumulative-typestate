(* definition for protocol and its compliance at language level *)

Require Import RegLang.languages.
Require Import RegLang.nfa RegLang.dfa.
Require Import RegLang.regexp.

Require Import String List.
Require Import Coq.Logic.Classical.
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

  Inductive pump_semantic : {set char} -> word -> word -> Prop :=
  | pump_semantic_nil X :
      pump_semantic X [::] [::]
  | pump_semantic_cons X a s block out :
      all (fun c => c \in X :|: [set a]) block ->
      pump_semantic (X :|: [set a]) s out ->
      pump_semantic X (a :: s) (a :: block ++ out).

  Fixpoint pumping_singleton_re_from (X : {set char}) (w : word) : regexp :=
    if w is a :: s then
      Conc (Atom a)
        (Conc (Star (re_of_set (X :|: [set a])))
          (pumping_singleton_re_from (X :|: [set a]) s))
    else Eps.

  Definition pumping_singleton_re (w : word) : regexp :=
    pumping_singleton_re_from set0 w.

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
    - move=> H. by case: H.
    - move/andP=> [Hr1 Hr2] w.
      by rewrite unfold_in /= /plus /= IH1 // IH2 // mem_cat.
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

  Fixpoint eliminate_star (r : regexp) : regexp :=
    match r with
    | Void => Void
    | Eps => Eps
    | Atom a => Atom a
    | Star r1 => bounded_star_basis (eliminate_star r1)
    | Plus r1 r2 => Plus (eliminate_star r1) (eliminate_star r2)
    | Conc r1 r2 => Conc (eliminate_star r1) (eliminate_star r2)
    end.

  Lemma regexp_power_star_free n r :
    star_free r -> star_free (regexp_power n r).
  Proof.
    elim: n => [|n IH] //= Hr.
    by rewrite Hr IH.
  Qed.

  Lemma bounded_star_basis_star_free r :
    star_free r -> star_free (bounded_star_basis r).
  Proof.
    move=> Hr.
    rewrite /bounded_star_basis.
    elim: (index_enum ('I_(#|char|).+1)) => [|k ks IH].
    - by rewrite big_nil.
    - by rewrite big_cons /= regexp_power_star_free // IH.
  Qed.

  Lemma eliminate_star_star_free r :
    star_free (eliminate_star r).
  Proof.
    elim: r => [| |a|r IH|r1 IH1 r2 IH2|r1 IH1 r2 IH2] //=.
    - exact: bounded_star_basis_star_free.
    - by rewrite IH1 IH2.
    - by rewrite IH1 IH2.
  Qed.

  Definition pumping_normalize (r : regexp) : regexp :=
    normalize_star_free (eliminate_star r).

  Lemma pumping_normalize_is_union_strings r :
    pumping_normalize r = union_strings (words_of_star_free (eliminate_star r)).
  Proof. by []. Qed.

  Lemma closure_equiv_refl r :
    closure_equiv r r.
  Proof. by move=> w. Qed.

  Lemma closure_equiv_sym r s :
    closure_equiv r s -> closure_equiv s r.
  Proof.
    move=> H w. split; by move/(H w).
  Qed.

  Lemma closure_equiv_trans r s t :
    closure_equiv r s -> closure_equiv s t -> closure_equiv r t.
  Proof.
    move=> Hrs Hst w. split.
    - by move/(Hrs w)/(Hst w).
    - by move/(Hst w)/(Hrs w).
  Qed.

  Lemma regexp_language_regular (r : regexp) :
    RegLang.dfa.regular (fun w : word => is_true (w \in r)).
  Proof.
    case: (@regularP char (fun w : word => is_true (w \in r)))
      => _ Hregular.
    apply: Hregular.
    by exists r.
  Qed.

  Lemma pumping_normalize_regular r :
    RegLang.dfa.regular
      (fun w : word => is_true (w \in pumping_normalize r)).
  Proof. exact: regexp_language_regular. Qed.

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

  Lemma language_equiv_closure_equiv r s :
    (forall w, (w \in r) = (w \in s)) ->
    closure_equiv r s.
  Proof.
    move=> Hlang w; split.
    - apply: pumping_closure_monotone => u.
      by rewrite /regex_lang !inE Hlang.
    - apply: pumping_closure_monotone => u.
      by rewrite /regex_lang !inE Hlang.
  Qed.

  Lemma pumping_normalize_eliminate_star_equiv r :
    closure_equiv (eliminate_star r) (pumping_normalize r).
  Proof.
    apply: language_equiv_closure_equiv => w.
    by rewrite normalize_star_free_correct ?eliminate_star_star_free.
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

  Lemma pump_at_cat_suffix (u v : word) k i :
    k < size u ->
    i <= k ->
    @pump_at char d0 (u ++ v) k i = @pump_at char d0 u k i ++ v.
  Proof.
    move=> Hk Hi.
    have Hk' : k.+1 <= size u by exact: Hk.
    have Hi' : i < size u := leq_ltn_trans Hi Hk.
    rewrite /pump_at.
    rewrite takel_cat // nth_cat Hi'.
    case Hlt: (k.+1 < size u).
    - by rewrite drop_cat Hlt -catA.
    - have Heq : k.+1 = size u.
      { apply/eqP. by rewrite eqn_leq Hk' leqNgt Hlt. }
      by rewrite Heq drop_size_cat // take_size drop_size -catA.
  Qed.

  Lemma pumping_cat_suffix (u u' v : word) :
    @pumping char d0 u u' ->
    @pumping char d0 (u ++ v) (u' ++ v).
  Proof.
    rewrite /pumping.
    move/hasP=> [k Hk].
    move/andP=> [Hklt Hki].
    move/hasP: Hki=> [i Hi].
    move/andP=> [Hile /eqP ->].
    have Hkcat : k < size (u ++ v).
    { by rewrite size_cat; exact: leq_trans Hklt (leq_addr _ _). }
    apply/hasP; exists k.
    - by rewrite mem_iota add0n leq0n Hkcat.
    apply/andP; split.
    - exact: Hkcat.
    apply/hasP; exists i.
    - by rewrite mem_iota add0n leq0n ltnS Hile.
    apply/andP; split=> //.
    by rewrite pump_at_cat_suffix // eq_refl.
  Qed.

  Lemma pump_at_cat_prefix (p u : word) k i :
    k < size u ->
    i <= k ->
    @pump_at char d0 (p ++ u) (size p + k) (size p + i) =
      p ++ @pump_at char d0 u k i.
  Proof.
    move=> Hk Hi.
    have Hk' : k.+1 <= size u by exact: Hk.
    rewrite /pump_at.
    rewrite -addnS take_cat ltnNge leq_addr /=.
    rewrite -{2}[size p]addn0 subnDl subn0.
    rewrite drop_cat ltnNge leq_addr /=.
    rewrite -[X in _ - X]addn0 subnDl subn0.
    rewrite nth_cat ltnNge leq_addr /=.
    rewrite -[X in _ - X]addn0 subnDl subn0.
    by rewrite -!catA.
  Qed.

  Lemma pumping_cat_prefix (p u u' : word) :
    @pumping char d0 u u' ->
    @pumping char d0 (p ++ u) (p ++ u').
  Proof.
    rewrite /pumping.
    move/hasP=> [k Hk].
    move/andP=> [Hklt Hki].
    move/hasP: Hki=> [i Hi].
    move/andP=> [Hile /eqP ->].
    apply/hasP; exists (size p + k).
    - rewrite mem_iota add0n size_cat.
      by rewrite leq_addr ltn_add2l.
    apply/andP; split.
    - by rewrite size_cat ltn_add2l.
    apply/hasP; exists (size p + i).
    - rewrite mem_iota add0n.
      by rewrite leq_addr ltnS leq_add2l Hile.
    apply/andP; split.
    - by rewrite leq_add2l.
    by rewrite pump_at_cat_prefix // eq_refl.
  Qed.

  Lemma pumping_closure_cat_prefix
      (L1 L2 : dlang) (u v : word) :
    L1 u ->
    @pumping_closure char d0 L2 v ->
    @pumping_closure char d0 (RegLang.languages.conc L1 L2) (u ++ v).
  Proof.
    move=> Hu Hclos.
    elim: Hclos => [v0 Hv0 | v0 v1 _ IH Hpump].
    - apply: pumping_closure_base.
      exact: conc_cat Hu Hv0.
    - apply: (@pumping_closure_step char d0 (RegLang.languages.conc L1 L2)
                (u ++ v0) (u ++ v1) IH).
      exact: pumping_cat_prefix.
  Qed.

  Lemma pumping_closure_cat
      (L1 L2 : dlang) (u v : word) :
    @pumping_closure char d0 L1 u ->
    @pumping_closure char d0 L2 v ->
    @pumping_closure char d0 (RegLang.languages.conc L1 L2) (u ++ v).
  Proof.
    move=> Hu Hv.
    elim: Hu => [u0 Hu0 | u0 u1 _ IH Hpump].
    - exact: pumping_closure_cat_prefix Hu0 Hv.
    - apply: (@pumping_closure_step char d0 (RegLang.languages.conc L1 L2)
                (u0 ++ v) (u1 ++ v) IH).
      exact: pumping_cat_suffix.
  Qed.

  Lemma pumping_closure_base_lift (L1 L2 : dlang) :
    (forall u, L1 u -> @pumping_closure char d0 L2 u) ->
    forall w,
      @pumping_closure char d0 L1 w ->
      @pumping_closure char d0 L2 w.
  Proof.
    move=> Hbase w Hclos.
    elim: Hclos => [u Hu | u v _ IH Hpump].
    - exact: Hbase.
    - exact: pumping_closure_step IH Hpump.
  Qed.

  Lemma pumping_closure_plusl (r s : regexp) w :
    @pumping_closure char d0 (regex_lang r) w ->
    @pumping_closure char d0 (regex_lang (Plus r s)) w.
  Proof.
    apply: pumping_closure_monotone => u Hu.
    by apply/plusP; left.
  Qed.

  Lemma pumping_closure_plusr (r s : regexp) w :
    @pumping_closure char d0 (regex_lang s) w ->
    @pumping_closure char d0 (regex_lang (Plus r s)) w.
  Proof.
    apply: pumping_closure_monotone => u Hu.
    by apply/plusP; right.
  Qed.

  Lemma pumping_closure_conc_regex (r s : regexp) u v :
    @pumping_closure char d0 (regex_lang r) u ->
    @pumping_closure char d0 (regex_lang s) v ->
    @pumping_closure char d0 (regex_lang (Conc r s)) (u ++ v).
  Proof.
    exact: pumping_closure_cat.
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

  Lemma re_of_setP (X : {set char}) (w : word) :
    reflect (exists2 c, c \in X & w = [:: c]) (w \in re_of_set X).
  Proof.
    rewrite /re_of_set.
    apply: (iffP (big_plusP _ _ _)) => [[c Hc Hw] | [c Hc ->]].
    - move: Hw. rewrite unfold_in /atom.
      by case: w => [|x [|y ys]] //= /eqP ->; exists c.
    - exists c => //.
      change ([:: c] \in atom c).
      by rewrite /atom inE.
  Qed.

  Lemma star_re_of_set_all (X : {set char}) (w : word) :
    w \in Star (re_of_set X) ->
    all (fun c => c \in X) w.
  Proof.
    case/starP=> vv Hall ->.
    elim: vv Hall => [|v vs IH] //= /andP [Hv Hvs].
    move: Hv; rewrite inE => /andP [_ Hv].
    have [c Hc Hatom] : exists2 c, c \in X & v \in Atom c.
    { rewrite /re_of_set in Hv.
      pose R := @big_plusP char char (fun c => c \in X) v
        (fun c => Atom c).
      exact ((@elimT _ _ R) Hv). }
    move: Hatom. rewrite unfold_in /atom => /eqP ->.
    by rewrite /= Hc (IH Hvs).
  Qed.

  Lemma all_star_re_of_set (X : {set char}) (w : word) :
    all (fun c => c \in X) w ->
    w \in Star (re_of_set X).
  Proof.
    elim: w => [|a w IH] /=.
    - by rewrite unfold_in /eps.
    - case Ha: (a \in X) => //= Hw.
      have Hhead : [:: a] \in re_of_set X.
      { apply/re_of_setP. by exists a. }
      exact: star_cat Hhead (IH Hw).
  Qed.

  Lemma pump_semanticP X s out :
    pump_semantic X s out <-> out \in pumping_singleton_re_from X s.
  Proof.
    split.
    - elim=> [Y|Y a rest block out' Hblock _ IH] /=.
      + by rewrite unfold_in /eps.
      + apply/concP; exists [:: a]; exists (block ++ out'); split=> //.
        split.
        * change ([:: a] \in atom a). by rewrite /atom inE.
        * apply/concP; exists block; exists out'; split=> //.
          split.
          -- exact: all_star_re_of_set.
          -- exact: IH.
    - elim: s X out => [|a rest IH] X out /=.
      + move=> Hout.
        move: Hout; rewrite unfold_in /eps => /eqP ->.
        exact: pump_semantic_nil.
      + case/concP=> h [tail [-> [Hh Htail]]].
        move: Hh; rewrite unfold_in /atom => /eqP ->.
        case/concP: Htail => block [out' [-> [Hblock Hout']]].
        apply: pump_semantic_cons.
        * exact: star_re_of_set_all.
        * exact: IH.
  Qed.

  Lemma pump_semantic_base X s :
    pump_semantic X s s.
  Proof.
    elim: s X => [|a s IH] X /=.
    - exact: pump_semantic_nil.
    - exact: pump_semantic_cons (isT : all _ [::]) (IH (X :|: [set a])).
  Qed.

  Definition insert_after (w : word) k c : word :=
    take k.+1 w ++ c :: drop k.+1 w.

  Lemma all_take P (w : word) n :
    all P w -> all P (take n w).
  Proof.
    move/allP=> Hall.
    apply/allP=> c Hc.
    exact: Hall c (mem_take Hc).
  Qed.

  Lemma all_drop P (w : word) n :
    all P w -> all P (drop n w).
  Proof.
    move/allP=> Hall.
    apply/allP=> c Hc.
    exact: Hall c (mem_drop Hc).
  Qed.

  Lemma all_insert_after P (w : word) k c :
    all P w -> P c -> all P (insert_after w k c).
  Proof.
    move=> Hw Hc.
    rewrite /insert_after all_cat /= Hc.
    by rewrite all_take // all_drop.
  Qed.

  Lemma cat_cons_cat (x : char) (u v w : word) :
    u ++ x :: v ++ w = (u ++ x :: v) ++ w.
  Proof. by elim: u => [|a u IH] //=; rewrite IH. Qed.

  Lemma cons_cat_snoc (a c : char) (block out : word) :
    a :: block ++ c :: out = a :: (block ++ [:: c]) ++ out.
  Proof. by elim: block a => [|b block IH] a //=; rewrite IH. Qed.

  Lemma insert_after_cat_prefix (p u : word) k c :
    insert_after (p ++ u) (size p + k) c =
      p ++ insert_after u k c.
  Proof.
    rewrite /insert_after -addnS.
    rewrite take_cat ltnNge leq_addr /=.
    rewrite -{2}[size p]addn0 subnDl subn0.
    rewrite drop_cat ltnNge leq_addr /=.
    rewrite -[X in _ - X]addn0 subnDl subn0.
    by rewrite -!catA.
  Qed.

  Lemma mem_head_segment_allowed (X : {set char}) (a : char) (block : word) (c : char) :
    c \in a :: block ->
    all (fun x => x \in X :|: [set a]) block ->
    c \in X :|: [set a].
  Proof.
    rewrite in_cons.
    case/orP=> [/eqP -> | Hc] Hblock.
    - exact: set1Ur.
    - exact: (allP Hblock c Hc).
  Qed.

  Lemma pump_semantic_insert_at X s out k c :
    pump_semantic X s out ->
    k < size out ->
    (c \in X) || (c \in take k.+1 out) ->
    pump_semantic X s (insert_after out k c).
  Proof.
    move=> Hsem.
    elim: Hsem k c => [Y|Y a rest block out' Hblock Hout IH] k c Hk Hc /=.
    - by rewrite ltn0 in Hk.
    - set head := a :: block.
      case Hhead: (k < size head).
      + have Hc_allowed : c \in Y :|: [set a].
        { move/orP: Hc => [HcY | Hctake].
          - by rewrite inE HcY.
          - have Htake_head :
              take k.+1 (head ++ out') = take k.+1 head.
            { exact: takel_cat. }
            rewrite /head in Htake_head.
            have Hcin_take_head : c \in take k.+1 head.
            { by move: Hctake; rewrite Htake_head. }
            have Hcin_head : c \in head.
            { exact: mem_take Hcin_take_head. }
            exact: mem_head_segment_allowed Hcin_head Hblock. }
        have Hhead_nonempty : head = a :: block by [].
        rewrite /insert_after.
        case: k Hhead Hk Hc Hc_allowed => [|k] Hhead Hk Hc Hc_allowed.
        * rewrite /= take0 drop0.
          apply: (@pump_semantic_cons Y a rest (c :: block) out').
          -- by rewrite /= Hc_allowed Hblock.
          -- exact: Hout.
        * rewrite /=.
          have Hkblock : k < size block by move: Hhead; rewrite /head /= ltnS.
          case Hlt: (k.+1 < size block).
          -- rewrite (take_cat k.+1 block out') Hlt.
             rewrite (drop_cat k.+1 block out') Hlt.
             rewrite cat_cons_cat.
             apply: (@pump_semantic_cons Y a rest
               (take k.+1 block ++ c :: drop k.+1 block) out').
             ++ exact: (all_insert_after
                  (fun x => x \in Y :|: [set a]) block k c Hblock Hc_allowed).
             ++ exact: Hout.
          -- have Hle : k.+1 <= size block by exact: Hkblock.
             have Heq : k.+1 = size block.
             { apply/eqP. by rewrite eqn_leq Hle leqNgt Hlt. }
             rewrite Heq take_size_cat // drop_size_cat //.
             replace (a :: block ++ c :: out')
                with (a :: (block ++ [:: c]) ++ out').
             2: symmetry; exact: (cons_cat_snoc a c block out').
             apply: (@pump_semantic_cons Y a rest (block ++ [:: c]) out').
             ++ by rewrite all_cat Hblock /= Hc_allowed.
             ++ exact: Hout.
      + have Hhead_le : size head <= k by rewrite leqNgt Hhead.
        pose kt := k - size head.
        have HkE : k = size head + kt by rewrite /kt subnKC.
        have Hkt : kt < size out'.
        { have Hsize : size (a :: block ++ out') = size head + size out'.
          { by rewrite /head /= size_cat. }
          move: Hk. rewrite HkE Hsize ltn_add2l. by []. }
        have Hc_tail :
          (c \in Y :|: [set a]) || (c \in take kt.+1 out').
        { move/orP: Hc => [HcY | Hctake].
          - apply/orP; left. by rewrite inE HcY.
          - have Htake_tail :
              take k.+1 (a :: block ++ out') = head ++ take kt.+1 out'.
            { change (take k.+1 (head ++ out') = head ++ take kt.+1 out').
              rewrite HkE -addnS.
              rewrite take_cat ltnNge leq_addr /=.
              by rewrite -[X in _ - X]addn0 subnDl subn0. }
            rewrite Htake_tail in Hctake.
            move: Hctake; rewrite mem_cat.
            case/orP=> [Hcin_head | Hctail].
            + apply/orP; left.
              exact: mem_head_segment_allowed Hcin_head Hblock.
            + by apply/orP; right. }
        have Htail := IH kt c Hkt Hc_tail.
        have Hins_tail :
          insert_after (a :: block ++ out') k c =
            head ++ insert_after out' kt c.
        { rewrite HkE.
          change (insert_after (head ++ out') (size head + kt) c =
            head ++ insert_after out' kt c).
          exact: insert_after_cat_prefix. }
        rewrite Hins_tail /head.
        exact: pump_semantic_cons Hblock Htail.
  Qed.

  Lemma nth_mem_take_prefix (out : word) k i :
    i <= k ->
    k < size out ->
    nth d0 out i \in take k.+1 out.
  Proof.
    move=> Hik Hk.
    have Hi_take : i < size (take k.+1 out).
    { have Hle : k.+1 <= size out by exact: Hk.
      have Hsize : size (take k.+1 out) = k.+1.
      { rewrite size_take. by case: (minn_idPl Hle). }
      by rewrite Hsize ltnS. }
    have Hik' : i < k.+1 by rewrite ltnS.
    rewrite -(@nth_take k.+1 char d0 i Hik' out).
    exact: mem_nth Hi_take.
  Qed.

  Lemma pump_semantic_closed X s out out' :
    pump_semantic X s out ->
    @pumping char d0 out out' ->
    pump_semantic X s out'.
  Proof.
    move=> Hsem.
    rewrite /pumping.
    move/hasP=> [k Hkmem].
    move/andP=> [Hk Hhas].
    move/hasP: Hhas=> [i Himem].
    move/andP=> [Hik /eqP ->].
    rewrite /pump_at.
    change (pump_semantic X s (insert_after out k (nth d0 out i))).
    apply: (@pump_semantic_insert_at X s out k (nth d0 out i) Hsem Hk).
    apply/orP; right.
    exact: nth_mem_take_prefix.
  Qed.

  Lemma pumping_closure_singleton_to_semantic w out :
    @pumping_closure char d0 (pred1 w) out ->
    pump_semantic set0 w out.
  Proof.
    move=> Hclos.
    elim: Hclos => [u Hu | u v _ IH Hpump].
    - move/eqP: Hu => ->. exact: pump_semantic_base.
    - exact: pump_semantic_closed IH Hpump.
  Qed.

  Lemma pumping_closure_singleton_to_re w out :
    @pumping_closure char d0 (pred1 w) out ->
    out \in pumping_singleton_re w.
  Proof.
    move=> Hclos.
    exact ((proj1 (pump_semanticP set0 w out))
      (pumping_closure_singleton_to_semantic w out Hclos)).
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

  Lemma all_word_symbols_mem (p block : word) :
    all (fun c => c \in word_symbols p) block ->
    all (fun c => c \in p) block.
  Proof.
    move/allP=> Hall.
    apply/allP=> c Hc.
    by rewrite -mem_word_symbols; exact: Hall.
  Qed.

  Lemma pump_semantic_to_closure_from p s out :
    pump_semantic (word_symbols p) s out ->
    @pumping_closure char d0 (pred1 (p ++ s)) (p ++ out).
  Proof.
    move E: (word_symbols p) => X Hsem.
    elim: Hsem p E => [Y|Y a rest block out' Hblock _ IH] p E /=.
    - exact: (@pumping_closure_base char d0 (pred1 (p ++ [::]))
        (p ++ [::]) (eq_refl _)).
    - have Epa : word_symbols (p ++ [:: a]) = word_symbols p :|: [set a].
      { by rewrite word_symbols_cat /= setU0. }
      have EpaY : word_symbols (p ++ [:: a]) = Y :|: [set a].
      { by rewrite Epa E. }
      have Htail :
        @pumping_closure char d0 (pred1 ((p ++ [:: a]) ++ rest))
          ((p ++ [:: a]) ++ out') :=
        IH (p ++ [:: a]) EpaY.
      rewrite -!catA /= in Htail.
      have Hblock' : all (fun c => c \in p ++ [:: a]) block.
      { apply: all_word_symbols_mem.
        by rewrite Epa E. }
      have Hins :
        @pumping_closure char d0 (pred1 (p ++ a :: out'))
          (p ++ a :: block ++ out').
      { have := pumping_insert_block_after_prefix (p ++ [:: a]) block out' Hblock'.
        by rewrite -!catA /=. }
      exact: pumping_closure_lift_closure Htail Hins.
  Qed.

  Lemma pump_semantic_to_closure w out :
    pump_semantic set0 w out ->
    @pumping_closure char d0 (pred1 w) out.
  Proof.
    move=> Hsem.
    have := pump_semantic_to_closure_from [::] w out Hsem.
    by rewrite /=.
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

  Lemma pumping_closure_star_factors (r : regexp) (vv : seq word) :
    (forall v, v \in vv ->
      @pumping_closure char d0 (regex_lang r) v) ->
    @pumping_closure char d0 (regex_lang (Star r)) (flatten vv).
  Proof.
    elim: vv => [|v vs IH] Hfac /=.
    - apply: pumping_closure_base.
      by rewrite /regex_lang inE.
    - have Hv : @pumping_closure char d0 (regex_lang r) v.
      { exact: Hfac v (mem_head _ _). }
      have Hvs : @pumping_closure char d0 (regex_lang (Star r)) (flatten vs).
      { apply: IH => u Hu. apply: Hfac. by rewrite in_cons Hu orbT. }
      have Hcat :=
        @pumping_closure_conc_regex r (Star r) v (flatten vs) Hv Hvs.
      apply: (pumping_closure_monotone _ _ _ _ Hcat) => u.
      case/concP=> u1 [u2 [-> [Hu1 Hu2]]].
      exact: star_cat Hu1 Hu2.
  Qed.

  Lemma eliminate_star_base_closure r :
    [/\ (forall w,
          w \in r ->
          @pumping_closure char d0 (regex_lang (eliminate_star r)) w)
      & (forall w,
          w \in eliminate_star r ->
          @pumping_closure char d0 (regex_lang r) w)].
  Proof.
    elim: r => [| |a|r [IHto IHfrom]|r1 [IHto1 IHfrom1] r2 [IHto2 IHfrom2]
                |r1 [IHto1 IHfrom1] r2 [IHto2 IHfrom2]] /=.
    - split; move=> w; by rewrite /regex_lang inE.
    - split; move=> w Hw; exact: pumping_closure_base Hw.
    - split; move=> w Hw; exact: pumping_closure_base Hw.
    - split.
      + move=> w Hw.
        case/starP: Hw => vv Hall ->.
        have Hstar :
          @pumping_closure char d0 (regex_lang (Star (eliminate_star r)))
            (flatten vv).
        { apply: pumping_closure_star_factors => v Hv.
          have Hrv : v \in r.
          { move: ((allP Hall) v Hv). by rewrite inE => /andP []. }
          exact: (IHto v Hrv). }
        exact: pumping_closure_star_to_bounded_star_basis Hstar.
      + move=> w Hw.
        have Hstar_elim :
          @pumping_closure char d0 (regex_lang (Star (eliminate_star r))) w :=
          pumping_closure_bounded_star_basis_to_star (eliminate_star r) w
            (@pumping_closure_base char d0
              (regex_lang (bounded_star_basis (eliminate_star r))) w Hw).
        apply: (@pumping_closure_base_lift
          (regex_lang (Star (eliminate_star r))) (regex_lang (Star r))).
        * move=> u Hu.
          case/starP: Hu => vv Hall ->.
          apply: pumping_closure_star_factors => v Hv.
          have Hrv : v \in eliminate_star r.
          { move: ((allP Hall) v Hv). by rewrite inE => /andP []. }
          exact: (IHfrom v Hrv).
        * exact: Hstar_elim.
    - split.
      + move=> w.
        case/plusP=> [Hw | Hw].
        * exact: pumping_closure_plusl (IHto1 w Hw).
        * exact: pumping_closure_plusr (IHto2 w Hw).
      + move=> w.
        case/plusP=> [Hw | Hw].
        * exact: pumping_closure_plusl (IHfrom1 w Hw).
        * exact: pumping_closure_plusr (IHfrom2 w Hw).
    - split.
      + move=> w.
        case/concP=> u [v [-> [Hu Hv]]].
        exact: pumping_closure_conc_regex (IHto1 u Hu) (IHto2 v Hv).
      + move=> w.
        case/concP=> u [v [-> [Hu Hv]]].
        exact: pumping_closure_conc_regex (IHfrom1 u Hu) (IHfrom2 v Hv).
  Qed.

  Theorem eliminate_star_correct r :
    closure_equiv r (eliminate_star r).
  Proof.
    have [Hto Hfrom] := eliminate_star_base_closure r.
    move=> w; split.
    - move=> Hclos.
      exact: (@pumping_closure_base_lift
        (regex_lang r) (regex_lang (eliminate_star r)) Hto w Hclos).
    - move=> Hclos.
      exact: (@pumping_closure_base_lift
        (regex_lang (eliminate_star r)) (regex_lang r) Hfrom w Hclos).
  Qed.

  Theorem pumping_normalize_correct r :
    closure_equiv r (pumping_normalize r).
  Proof.
    exact: closure_equiv_trans (eliminate_star_correct r)
             (pumping_normalize_eliminate_star_equiv r).
  Qed.

  Lemma pumping_closure_singleton_correct w out :
    @pumping_closure char d0 (pred1 w) out <->
    out \in pumping_singleton_re w.
  Proof.
    split.
    - exact: pumping_closure_singleton_to_re.
    - move=> Hre.
      apply: pump_semantic_to_closure.
      exact: (proj2 (pump_semanticP set0 w out) Hre).
  Qed.

  Lemma pumping_closure_singleton_regular w :
    RegLang.dfa.regular
      (fun out : word => @pumping_closure char d0 (pred1 w) out).
  Proof.
    apply: (RegLang.dfa.regular_ext
      (L2 := fun out : word => is_true (out \in pumping_singleton_re w))).
    - exact: regexp_language_regular.
    - move=> out. exact: pumping_closure_singleton_correct.
  Qed.

  Lemma pumping_closure_union_stringsP ws out :
    @pumping_closure char d0 (regex_lang (union_strings ws)) out <->
    exists2 w, w \in ws & @pumping_closure char d0 (pred1 w) out.
  Proof.
    split.
    - move=> Hclos.
      elim: Hclos => [u Hu | u v _ [w Hw Hwu] Hpump].
      + move: Hu. rewrite /regex_lang inE union_strings_correct => Hu.
        exists u => //.
        exact: (@pumping_closure_base char d0 (pred1 u) u (eq_refl _)).
      + exists w => //.
        exact: pumping_closure_step Hwu Hpump.
    - move=> [w Hw Hclos].
      apply: (@pumping_closure_lift_singleton
        (regex_lang (union_strings ws)) w out).
      + by rewrite /regex_lang inE union_strings_correct.
      + exact: Hclos.
  Qed.

  Lemma pumping_closure_union_strings_regular ws :
    RegLang.dfa.regular
      (fun out : word =>
        @pumping_closure char d0 (regex_lang (union_strings ws)) out).
  Proof.
    apply: (RegLang.dfa.regular_ext
      (L2 := fun out : word =>
        exists2 w, w \in ws & @pumping_closure char d0 (pred1 w) out)).
    - apply: RegLang.dfa.regular_bigU => w _.
      exact: pumping_closure_singleton_regular.
    - move=> out. exact: pumping_closure_union_stringsP.
  Qed.

  Lemma pumping_closure_normalized_regular r :
    RegLang.dfa.regular
      (fun out : word =>
        @pumping_closure char d0 (regex_lang (pumping_normalize r)) out).
  Proof.
    rewrite pumping_normalize_is_union_strings.
    exact: pumping_closure_union_strings_regular.
  Qed.

  Theorem pumping_closure_regular_regex r :
    RegLang.dfa.regular
      (fun out : word =>
        @pumping_closure char d0 (regex_lang r) out).
  Proof.
    apply: (RegLang.dfa.regular_ext
      (L2 := fun out : word =>
        @pumping_closure char d0 (regex_lang (pumping_normalize r)) out)).
    - exact: pumping_closure_normalized_regular.
    - move=> out.
      case: (pumping_normalize_correct r out) => Hto Hfrom.
      split; [exact: Hto | exact: Hfrom].
  Qed.

End PumpingClosureRegularity.

Section InterleavingClosedness.
  Variable char : finType.
  Notation word := (RegLang.languages.word char).
  Notation lang := (RegLang.languages.lang char).
  Notation dlang := (RegLang.languages.dlang char).

  Notation regexp := (RegLang.regexp.regexp char).
  Variable d0 : char.
  Definition pumping_closure_lang (L:dlang) := fun w => @pumping_closure char d0 L w.

  Inductive interleaving : word -> word -> word -> Prop :=
  | interleaving_nil_l v :
      interleaving [::] v v
  | interleaving_nil_r u :
      interleaving u [::] u
  | interleaving_left a u v w :
      interleaving u v w ->
      interleaving (a :: u) v (a :: w)
  | interleaving_right b u v w :
      interleaving u v w ->
      interleaving u (b :: v) (b :: w).

  Definition shuffle_closed (L : lang) :=
    forall u v w, L u -> L v -> interleaving u v w -> L w.

  Definition seed_covers (seed w : word) :=
    @pumping_closure char d0 (pred1 seed) w.

  Definition covered_by (S : lang) : lang :=
    fun w => exists2 seed, S seed & seed_covers seed w.

  Definition seed_corpus (K : lang) (S : lang) :=
    forall w, K w <-> covered_by S w.

  Definition shuffle_lang (L1 L2 : lang) : lang :=
    fun w => exists u v, [/\ L1 u, L2 v & interleaving u v w].

  Lemma pumping_closure_seed_corpus (L : dlang) :
    seed_corpus (pumping_closure_lang L) L.
  Proof.
    move=> w; split.
    - move=> Hclos.
      elim: Hclos => [u Hu | u v _ [seed Hseed Hseedu] Hpump].
      + exists u => //.
        exact: (@pumping_closure_base char d0 (pred1 u) u (eq_refl _)).
      + exists seed => //.
        exact: pumping_closure_step Hseedu Hpump.
    - move=> [seed Hseed Hseedout].
      exact: (@pumping_closure_lift_singleton char d0 L seed w Hseed Hseedout).
  Qed.

  Theorem same_seed_corpus_shuffle_closed (L : dlang) (S : lang) :
    seed_corpus (pumping_closure_lang L) S ->
    seed_corpus (shuffle_lang (covered_by S) (covered_by S)) S ->
    shuffle_closed (pumping_closure_lang L).
  Proof.
    move=> Hcorpus Hshuffle u v w Hu Hv Hint.
    have HuS : covered_by S u := (proj1 (Hcorpus u)) Hu.
    have HvS : covered_by S v := (proj1 (Hcorpus v)) Hv.
    have Hshuf : shuffle_lang (covered_by S) (covered_by S) w.
    { exists u, v. by split. }
    have HoutS : covered_by S w := (proj1 (Hshuffle w)) Hshuf.
    exact: (proj2 (Hcorpus w)) HoutS.
  Qed.

  Lemma seed_covers_trans s t w :
    seed_covers s t -> seed_covers t w -> seed_covers s w.
  Proof.
    move=> Hst Htw.
    exact: (@pumping_closure_lift_closure char d0 (pred1 s) t w Hst Htw).
  Qed.

  Lemma seed_covers_refl s :
    seed_covers s s.
  Proof.
    exact: (@pumping_closure_base char d0 (pred1 s) s (eq_refl _)).
  Qed.

  Lemma seed_covers_size_ge s w :
    seed_covers s w -> size s <= size w.
  Proof.
    move=> Hclos.
    elim: Hclos => [u Hu | u v _ IH Hpump].
    - by move/eqP: Hu => ->.
    - have Hsize : size v = size u + 1 := @pumping_size char d0 u v Hpump.
      rewrite Hsize.
      exact: leq_trans IH (leq_addr _ _).
  Qed.

  Lemma seed_covers_same_size s w :
    seed_covers s w -> size s = size w -> s = w.
  Proof.
    move=> Hclos Hsize.
    elim: Hclos Hsize => [u Hu | u v Hprev _ Hpump] Hsize.
    - by move/eqP: Hu.
    - have Hle : size s <= size u := seed_covers_size_ge s u Hprev.
      have Hlt : size u < size s.
      { rewrite Hsize (@pumping_size char d0 u v Hpump).
        by rewrite addn1 ltnSn. }
      by move: Hle; rewrite leqNgt Hlt.
  Qed.

  Lemma seed_covers_antisym s t :
    seed_covers s t -> seed_covers t s -> s = t.
  Proof.
    move=> Hst Hts.
    have Hst_size : size s <= size t := seed_covers_size_ge s t Hst.
    have Hts_size : size t <= size s := seed_covers_size_ge t s Hts.
    have Hsize : size s = size t.
    { apply/eqP. by rewrite eqn_leq Hst_size Hts_size. }
    exact: seed_covers_same_size Hst Hsize.
  Qed.

  Lemma strict_seed_covers_size_lt s t :
    seed_covers s t ->
    ~ seed_covers t s ->
    size s < size t.
  Proof.
    move=> Hst Hnot.
    have Hle : size s <= size t := seed_covers_size_ge s t Hst.
    rewrite leq_eqVlt in Hle.
    case/orP: Hle => [/eqP Hsize | Hlt]; last exact: Hlt.
    have Heq : s = t := seed_covers_same_size s t Hst Hsize.
    move: Hnot; rewrite Heq => Hnot.
    exfalso. exact: Hnot (seed_covers_refl t).
  Qed.

  Lemma distinct_seed_covers_size_lt s t :
    seed_covers s t ->
    s <> t ->
    size s < size t.
  Proof.
    move=> Hst Hneq.
    have Hle : size s <= size t := seed_covers_size_ge s t Hst.
    rewrite leq_eqVlt in Hle.
    case/orP: Hle => [/eqP Hsize | Hlt]; last exact: Hlt.
    have Heq : s = t := seed_covers_same_size s t Hst Hsize.
    by case: Hneq.
  Qed.

  Definition cover_le (s t : word) :=
    forall w, seed_covers t w -> seed_covers s w.

  Lemma cover_leP s t :
    cover_le s t <-> seed_covers s t.
  Proof.
    split.
    - move=> Hle. exact: (Hle t (seed_covers_refl t)).
    - move=> Hst w Htw. exact: seed_covers_trans Hst Htw.
  Qed.

  Lemma cover_le_refl s :
    cover_le s s.
  Proof. by []. Qed.

  Lemma cover_le_trans s t u :
    cover_le s t -> cover_le t u -> cover_le s u.
  Proof.
    move=> Hst Htu w Huw.
    exact: Hst (Htu w Huw).
  Qed.

  Lemma cover_le_antisym s t :
    cover_le s t -> cover_le t s -> s = t.
  Proof.
    move/cover_leP=> Hst.
    move/cover_leP=> Hts.
    exact: seed_covers_antisym Hst Hts.
  Qed.

  Definition minimal_seed_corpus (L : lang) : lang :=
    fun seed =>
      L seed /\
      forall seed',
        L seed' -> cover_le seed' seed -> seed' = seed.

  Lemma minimal_seed_corpus_sub (L : lang) seed :
    minimal_seed_corpus L seed -> L seed.
  Proof. by case. Qed.

  Lemma minimal_seed_representative (L : lang) seed :
    L seed ->
    exists2 min_seed,
      minimal_seed_corpus L min_seed & seed_covers min_seed seed.
  Proof.
    move=> Hseed.
    pose P n :=
      forall cur, size cur <= n -> L cur ->
        exists2 min_seed,
          minimal_seed_corpus L min_seed & seed_covers min_seed cur.
    have HP : forall n, P n.
    { elim=> [|n IH] cur Hsize Hcur.
      - have Hempty : size cur = 0 by apply/eqP; rewrite eqn_leq Hsize.
        case: (classic
          (exists seed',
            L seed' /\ seed_covers seed' cur /\ seed' <> cur)).
        + move=> [seed' [_ [Hcover Hneq]]].
          have Hlt := distinct_seed_covers_size_lt seed' cur Hcover Hneq.
          move: Hlt. by rewrite Hempty.
        + move=> Hnone.
          exists cur.
          * split=> // seed' Hseed' Hle.
            move/cover_leP: Hle=> Hcover.
            case: (classic (seed' = cur)) => // Hneq.
            by case: Hnone; exists seed'.
          * exact: seed_covers_refl.
      - case: (classic
          (exists seed',
            L seed' /\ seed_covers seed' cur /\ seed' <> cur)).
        + move=> [seed' [Hseed' [Hcover Hneq]]].
          have Hlt := distinct_seed_covers_size_lt seed' cur Hcover Hneq.
          have Hseed'_size : size seed' <= n.
          { have : size seed' < n.+1 := leq_trans Hlt Hsize.
            by rewrite ltnS. }
          have [min_seed Hmin Hmin_seed'] := IH seed' Hseed'_size Hseed'.
          exists min_seed => //.
          exact: seed_covers_trans Hmin_seed' Hcover.
        + move=> Hnone.
          exists cur.
          * split=> // seed' Hseed' Hle.
            move/cover_leP: Hle=> Hcover.
            case: (classic (seed' = cur)) => // Hneq.
            by case: Hnone; exists seed'.
          * exact: seed_covers_refl. }
    exact: (HP (size seed) seed (leqnn _) Hseed).
  Qed.

  Lemma minimal_seed_corpus_seed_corpus (L : dlang) :
    seed_corpus (pumping_closure_lang L) (minimal_seed_corpus L).
  Proof.
    move=> w; split.
    - move/(proj1 (pumping_closure_seed_corpus L w))=> [seed Hseed Hseedw].
      have [min_seed Hmin Hminseed] :=
        minimal_seed_representative L seed Hseed.
      exists min_seed => //.
      exact: seed_covers_trans Hminseed Hseedw.
    - move=> [seed Hmin Hseedw].
      exact: (@pumping_closure_lift_singleton char d0 L seed w
        (minimal_seed_corpus_sub L seed Hmin) Hseedw).
  Qed.

  Theorem minimal_seed_corpus_closedness (L : dlang) :
    seed_corpus (pumping_closure_lang L) (minimal_seed_corpus L) ->
    seed_corpus
      (shuffle_lang
        (covered_by (minimal_seed_corpus L))
        (covered_by (minimal_seed_corpus L)))
      (minimal_seed_corpus L) ->
    shuffle_closed (pumping_closure_lang L).
  Proof.
    exact: same_seed_corpus_shuffle_closed.
  Qed.

  Fixpoint canonical_seed_from (seen : word) (w : word) : word :=
    if w is a :: rest then
      if a \in seen then canonical_seed_from seen rest
      else a :: canonical_seed_from (seen ++ [:: a]) rest
    else [::].

  Definition canonical_seed (w : word) : word :=
    canonical_seed_from [::] w.

  Definition canonical_corpus (K : lang) : lang :=
    fun seed => exists2 w, K w & canonical_seed w = seed.

  Definition canonical_shuffle_stable (S : lang) :=
    forall u v w,
      S u ->
      S v ->
      interleaving u v w ->
      S (canonical_seed w).

  Lemma cat_singler_cons (p rest : word) a0 :
    (p ++ [:: a0]) ++ rest = p ++ a0 :: rest.
  Proof. by elim: p => [|x p IH] //=; rewrite IH. Qed.

  Lemma canonical_seed_from_cat seen u v :
    canonical_seed_from seen (u ++ v) =
      canonical_seed_from seen u ++
        canonical_seed_from (seen ++ canonical_seed_from seen u) v.
  Proof.
    elim: u seen => [|a0 rest IH] seen /=.
    - by rewrite cats0.
    - case Ha: (a0 \in seen).
      + by rewrite IH.
      + rewrite IH /=.
        by rewrite cat_singler_cons.
  Qed.

  Lemma canonical_seed_from_all_mem seen w :
    all (fun c => c \in seen ++ canonical_seed_from seen w) w.
  Proof.
    elim: w seen => [|a0 rest IH] seen //=.
    case Ha: (a0 \in seen).
    - apply/andP; split.
      + by rewrite mem_cat Ha.
      + apply/allP=> c Hc.
        have Hall := IH seen.
        exact: (allP Hall c Hc).
    - apply/andP; split.
      + rewrite mem_cat.
        apply/orP; right.
        by rewrite in_cons eq_refl.
      + apply/allP=> c Hc.
        have Hall := IH (seen ++ [:: a0]).
        have Hc' := allP Hall c Hc.
        move: Hc'.
        by rewrite -catA /=.
  Qed.

  Lemma canonical_seed_from_all_seen seen w :
    all (fun c => c \in seen) w ->
    canonical_seed_from seen w = [::].
  Proof.
    elim: w seen => [|a0 rest IH] seen //=.
    move/andP=> [Ha Hall].
    by rewrite Ha IH.
  Qed.

  Lemma canonical_seed_cat_self w :
    canonical_seed (w ++ w) = canonical_seed w.
  Proof.
    rewrite /canonical_seed canonical_seed_from_cat /=.
    have Hall := canonical_seed_from_all_mem [::] w.
    have Hnil :
      canonical_seed_from (canonical_seed_from [::] w) w = [::].
    { apply: canonical_seed_from_all_seen.
      move: Hall. by rewrite /=. }
    by rewrite Hnil cats0.
  Qed.

  Lemma canonical_seed_from_seen_mem seen p c :
    c \in seen ++ p ->
    c \in seen ++ canonical_seed_from seen p.
  Proof.
    rewrite !mem_cat.
    case/orP=> [Hseen | Hp].
    - by rewrite Hseen.
    - have Hall := canonical_seed_from_all_mem seen p.
      move: (allP Hall c Hp).
      by rewrite mem_cat.
  Qed.

  Lemma canonical_seed_from_insert_seen seen p s c :
    c \in seen ++ p ->
    canonical_seed_from seen (p ++ c :: s) =
      canonical_seed_from seen (p ++ s).
  Proof.
    move=> Hc.
    rewrite !canonical_seed_from_cat.
    have Hseen : c \in seen ++ canonical_seed_from seen p :=
      canonical_seed_from_seen_mem seen p c Hc.
    by rewrite /= Hseen.
  Qed.

  Lemma pumping_canonical_seed u v :
    @pumping char d0 u v ->
    canonical_seed v = canonical_seed u.
  Proof.
    rewrite /pumping.
    move/hasP=> [k Hk].
    move/andP=> [Hklt Hhas].
    move/hasP: Hhas=> [i Hi].
    move/andP=> [Hile /eqP ->].
    rewrite /pump_at /canonical_seed.
    rewrite -[u in RHS](cat_take_drop k.+1 u).
    apply: canonical_seed_from_insert_seen.
    rewrite /=.
    have Hi_take : nth d0 u i \in take k.+1 u.
    { exact: (@nth_mem_take_prefix char d0 u k i Hile Hklt). }
    exact: Hi_take.
  Qed.

  Lemma seed_covers_canonical_seed s w :
    seed_covers s w ->
    canonical_seed w = canonical_seed s.
  Proof.
    move=> Hclos.
    elim: Hclos => [u Hu | u v _ IH Hpump].
    - by move/eqP: Hu => ->.
    - by rewrite (pumping_canonical_seed u v Hpump).
  Qed.

  Lemma interleaving_cat u v :
    interleaving u v (u ++ v).
  Proof.
    elim: u => [|a0 u IH] /=.
    - exact: interleaving_nil_l.
    - exact: interleaving_left IH.
  Qed.

  Lemma canonical_seed_from_closure seen w :
    pumping_closure_lang (pred1 (seen ++ canonical_seed_from seen w)) (seen ++ w).
  Proof.
    elim: w seen => [|a0 rest IH] seen /=.
    - exact: (@pumping_closure_base char d0
        (pred1 (seen ++ [::])) (seen ++ [::]) (eq_refl _)).
    - case Ha: (a0 \in seen).
      + have Htail := IH seen.
        have Hinsert :
          @pumping_closure char d0 (pred1 (seen ++ rest))
            (seen ++ a0 :: rest).
        { have Hall : all (fun c => c \in seen) [:: a0] by rewrite /= Ha.
          have := @pumping_insert_block_after_prefix char d0 seen [:: a0] rest Hall.
          by []. }
        exact: (@pumping_closure_lift_closure char d0
          (pred1 (seen ++ canonical_seed_from seen rest))
          (seen ++ rest) (seen ++ a0 :: rest) Htail Hinsert).
      + have Htail := IH (seen ++ [:: a0]).
        rewrite -(cat_singler_cons seen
          (canonical_seed_from (seen ++ [:: a0]) rest) a0).
        rewrite -(cat_singler_cons seen rest a0).
        exact: Htail.
  Qed.

  Lemma canonical_seed_covers w :
    seed_covers (canonical_seed w) w.
  Proof.
    have := canonical_seed_from_closure [::] w.
    by rewrite /seed_covers /canonical_seed /=.
  Qed.

  Lemma stable_minimal_seed_canonical (L : dlang) :
    canonical_shuffle_stable (minimal_seed_corpus L) ->
    forall seed,
      minimal_seed_corpus L seed ->
      canonical_seed seed = seed.
  Proof.
    move=> Hstable seed Hmin.
    have Hcan_min : minimal_seed_corpus L (canonical_seed seed).
    { have Hshuffle : interleaving seed seed (seed ++ seed) := interleaving_cat seed seed.
      have := Hstable seed seed (seed ++ seed) Hmin Hmin Hshuffle.
      by rewrite canonical_seed_cat_self. }
    have Hcan_seed : seed_covers (canonical_seed seed) seed :=
      canonical_seed_covers seed.
    case: Hmin => _ Hmin'.
    apply: Hmin'.
    - exact: minimal_seed_corpus_sub Hcan_min.
    - by apply/cover_leP.
  Qed.

  Lemma all_mem_cat_r (seen extra xs : word) :
    all (fun c => c \in seen) xs ->
    all (fun c => c \in seen ++ extra) xs.
  Proof.
    move=> Hall.
    apply/allP=> c Hc.
    have := allP Hall c Hc.
    by rewrite mem_cat => ->.
  Qed.

  Lemma all_mem_rcons_seen (seen xs : word) (a0 : char) :
    all (fun c => c \in seen) xs ->
    a0 \in seen ->
    all (fun c => c \in seen) (xs ++ [:: a0]).
  Proof.
    move=> Hall Ha.
    by rewrite all_cat Hall /= Ha.
  Qed.

  Lemma all_mem_rcons_cat (seen xs : word) (a0 : char) :
    all (fun c => c \in seen) xs ->
    all (fun c => c \in seen ++ [:: a0]) (xs ++ [:: a0]).
  Proof.
    move=> Hall.
    rewrite all_cat /=.
    apply/andP; split.
    - exact: all_mem_cat_r.
    - by rewrite mem_cat mem_seq1 eq_refl orbT.
  Qed.

  Lemma canonical_seed_from_absorb (small big w : word) :
    all (fun c => c \in big) small ->
    canonical_seed_from big (canonical_seed_from small w) =
      canonical_seed_from big w.
  Proof.
    elim: w small big => [|a0 rest IH] small big Hsub //=.
    case Ha_small: (a0 \in small).
    - have Ha_big : a0 \in big := allP Hsub a0 Ha_small.
      by rewrite Ha_big (IH small big Hsub).
    - case Ha_big: (a0 \in big).
      + have Hsub' : all (fun c => c \in big) (small ++ [:: a0]) :=
          all_mem_rcons_seen big small a0 Hsub Ha_big.
        by rewrite /= Ha_big (IH (small ++ [:: a0]) big Hsub').
      + have Hsub' :
          all (fun c => c \in big ++ [:: a0]) (small ++ [:: a0]) :=
          all_mem_rcons_cat big small a0 Hsub.
        by rewrite /= Ha_big (IH (small ++ [:: a0]) (big ++ [:: a0]) Hsub').
  Qed.

  Lemma canonical_interleaving_factor_from
      (seenL seenR seenG u v w : word) :
    all (fun c => c \in seenG) seenL ->
    all (fun c => c \in seenG) seenR ->
    interleaving u v w ->
    exists z,
      interleaving
        (canonical_seed_from seenL u)
        (canonical_seed_from seenR v)
        z /\
      canonical_seed_from seenG z = canonical_seed_from seenG w.
  Proof.
    move=> HLG HRG Hint.
    elim: Hint seenL seenR seenG HLG HRG
      => [v0|u0|a0 u0 v0 w0 _ IH|b0 u0 v0 w0 _ IH]
         seenL seenR seenG HLG HRG /=.
    - exists (canonical_seed_from seenR v0); split.
      + exact: interleaving_nil_l.
      + exact: canonical_seed_from_absorb HRG.
    - exists (canonical_seed_from seenL u0); split.
      + exact: interleaving_nil_r.
      + exact: canonical_seed_from_absorb HLG.
    - case HaL: (a0 \in seenL).
      + have HaG : a0 \in seenG := allP HLG a0 HaL.
        have [z [Hz Hcan]] := IH seenL seenR seenG HLG HRG.
        exists z; split=> //.
        by rewrite /= HaG Hcan.
      + case HaG: (a0 \in seenG).
        * have HLG' :
            all (fun c => c \in seenG) (seenL ++ [:: a0]) :=
            all_mem_rcons_seen seenG seenL a0 HLG HaG.
          have [z [Hz Hcan]] := IH (seenL ++ [:: a0]) seenR seenG HLG' HRG.
          exists (a0 :: z); split.
          -- exact: interleaving_left Hz.
          -- by rewrite /= HaG Hcan.
        * have HLG' :
            all (fun c => c \in seenG ++ [:: a0]) (seenL ++ [:: a0]) :=
            all_mem_rcons_cat seenG seenL a0 HLG.
          have HRG' :
            all (fun c => c \in seenG ++ [:: a0]) seenR :=
            all_mem_cat_r seenG [:: a0] seenR HRG.
          have [z [Hz Hcan]] :=
            IH (seenL ++ [:: a0]) seenR (seenG ++ [:: a0]) HLG' HRG'.
          exists (a0 :: z); split.
          -- exact: interleaving_left Hz.
          -- by rewrite /= HaG Hcan.
    - case HbR: (b0 \in seenR).
      + have HbG : b0 \in seenG := allP HRG b0 HbR.
        have [z [Hz Hcan]] := IH seenL seenR seenG HLG HRG.
        exists z; split=> //.
        by rewrite /= HbG Hcan.
      + case HbG: (b0 \in seenG).
        * have HRG' :
            all (fun c => c \in seenG) (seenR ++ [:: b0]) :=
            all_mem_rcons_seen seenG seenR b0 HRG HbG.
          have [z [Hz Hcan]] := IH seenL (seenR ++ [:: b0]) seenG HLG HRG'.
          exists (b0 :: z); split.
          -- exact: interleaving_right Hz.
          -- by rewrite /= HbG Hcan.
        * have HRG' :
            all (fun c => c \in seenG ++ [:: b0]) (seenR ++ [:: b0]) :=
            all_mem_rcons_cat seenG seenR b0 HRG.
          have HLG' :
            all (fun c => c \in seenG ++ [:: b0]) seenL :=
            all_mem_cat_r seenG [:: b0] seenL HLG.
          have [z [Hz Hcan]] :=
            IH seenL (seenR ++ [:: b0]) (seenG ++ [:: b0]) HLG' HRG'.
          exists (b0 :: z); split.
          -- exact: interleaving_right Hz.
          -- by rewrite /= HbG Hcan.
  Qed.

  Lemma canonical_interleaving_factor u v w :
    interleaving u v w ->
    exists z,
      interleaving (canonical_seed u) (canonical_seed v) z /\
      canonical_seed z = canonical_seed w.
  Proof.
    move=> Hint.
    have [z [Hz Hcan]] :=
      canonical_interleaving_factor_from [::] [::] [::] u v w
        (isT : all (fun c => c \in [::]) [::])
        (isT : all (fun c => c \in [::]) [::])
        Hint.
    exists z; split=> //.
  Qed.

  Theorem closedness (L : dlang) :
    canonical_shuffle_stable (minimal_seed_corpus L) ->
    shuffle_closed (pumping_closure_lang L).
  Proof.
    move=> Hstable u v w Hu Hv Hint.
    pose S := minimal_seed_corpus L.
    have Hcorpus : seed_corpus (pumping_closure_lang L) S :=
      minimal_seed_corpus_seed_corpus L.
    have HuS : covered_by S u := (proj1 (Hcorpus u)) Hu.
    have HvS : covered_by S v := (proj1 (Hcorpus v)) Hv.
    case: HuS => su Hsu Hsuu.
    case: HvS => sv Hsv Hsvv.
    have Hcu_su : canonical_seed u = su.
    { rewrite (seed_covers_canonical_seed su u Hsuu).
      exact: (stable_minimal_seed_canonical L Hstable su Hsu). }
    have Hcv_sv : canonical_seed v = sv.
    { rewrite (seed_covers_canonical_seed sv v Hsvv).
      exact: (stable_minimal_seed_canonical L Hstable sv Hsv). }
    have [z [Hz Hcz]] := canonical_interleaving_factor u v w Hint.
    have Hz' : interleaving su sv z.
    { move: Hz.
      by rewrite Hcu_su Hcv_sv. }
    have Hseed : S (canonical_seed w).
    { have := Hstable su sv z Hsu Hsv Hz'.
      by rewrite Hcz. }
    have Hcovered : covered_by S w.
    { exists (canonical_seed w) => //.
      exact: canonical_seed_covers w. }
    exact: (proj2 (Hcorpus w)) Hcovered.
  Qed.

  Lemma covered_by_canonical_corpus (K : lang) w :
    K w ->
    covered_by (canonical_corpus K) w.
  Proof.
    move=> Hout.
    exists (canonical_seed w).
    - by exists w.
    - exact: canonical_seed_covers.
  Qed.

  (*
  This tempting theorem is false as stated.  The canonical corpus forgets
  repeated milestone obligations in base words, so stability of canonical seeds
  alone is not enough to imply shuffle closedness of the pumping closure.

  Theorem closedness L :
    canonical_shuffle_stable (canonical_corpus L) ->
    shuffle_closed (pumping_closure_lang L).
  *)

  Variables a b x y : char.

  Example interleaving_ab_xy_axby :
    interleaving [:: a; b] [:: x; y] [:: a; x; b; y].
  Proof.
    apply: interleaving_left.
    apply: interleaving_right.
    apply: interleaving_left.
    apply: interleaving_right.
    exact: interleaving_nil_l.
  Qed.

  Example interleaving_ab_xy_xaby :
    interleaving [:: a; b] [:: x; y] [:: x; a; b; y].
  Proof.
    apply: interleaving_right.
    apply: interleaving_left.
    apply: interleaving_left.
    apply: interleaving_right.
    exact: interleaving_nil_l.
  Qed.

  Example interleaving_left_empty :
    interleaving [::] [:: x; y] [:: x; y].
  Proof. exact: interleaving_nil_l. Qed.

  Example interleaving_right_empty :
    interleaving [:: a; b] [::] [:: a; b].
  Proof. exact: interleaving_nil_r. Qed.

End InterleavingClosedness.

(*
Section InterleavingSpecificAttempts.
  Variable char : finType.
  Notation word := (RegLang.languages.word char).
  Notation lang := (RegLang.languages.lang char).
  Notation dlang := (RegLang.languages.dlang char).

  Variable d0 : char.

  Definition shuffle_closed (L : lang) :=
    forall u v w,
      L u -> L v -> @interleaving char u v w -> L w.

  Definition prefix_of (p s : word) :=
    exists t, s = p ++ t.

  Definition prefix_include (L : dlang) :=
    exists2 s, L s & forall u, L u -> prefix_of u s.

  Definition singleton_reseeding_complete (L : dlang) :=
    forall seed1 seed2 out1 out2 out,
      L seed1 ->
      L seed2 ->
      @pumping_closure char d0 (pred1 seed1) out1 ->
      @pumping_closure char d0 (pred1 seed2) out2 ->
      @interleaving char out1 out2 out ->
      exists2 seed, L seed & @pumping_closure char d0 (pred1 seed) out.

  Definition comparable_reseeding_complete (L : dlang) :=
    forall seed1 seed2 out1 out2 out,
      L seed1 ->
      L seed2 ->
      prefix_of seed1 seed2 \/ prefix_of seed2 seed1 ->
      @pumping_closure char d0 (pred1 seed1) out1 ->
      @pumping_closure char d0 (pred1 seed2) out2 ->
      @interleaving char out1 out2 out ->
      exists2 seed, L seed & @pumping_closure char d0 (pred1 seed) out.

  Lemma pumping_closure_origin (L : dlang) out :
    @pumping_closure char d0 L out ->
    exists2 seed, L seed & @pumping_closure char d0 (pred1 seed) out.
  Proof.
    move=> Hclos.
    elim: Hclos => [u Hu | u v _ [seed Hseed Hseedu] Hpump].
    - exists u => //.
      exact: (@pumping_closure_base char d0 (pred1 u) u (eq_refl _)).
    - exists seed => //.
      exact: pumping_closure_step Hseedu Hpump.
  Qed.

  Theorem reseeding_complete_pumping_closure_shuffle_closed (L : dlang) :
    singleton_reseeding_complete L ->
    shuffle_closed (fun out => @pumping_closure char d0 L out).
  Proof.
    move=> Hreseed out1 out2 out Hout1 Hout2 Hint.
    case: (pumping_closure_origin L out1 Hout1) => seed1 Hseed1 Hseed1out.
    case: (pumping_closure_origin L out2 Hout2) => seed2 Hseed2 Hseed2out.
    case: (Hreseed seed1 seed2 out1 out2 out
             Hseed1 Hseed2 Hseed1out Hseed2out Hint)
      => seed Hseed Hseedout.
    exact: (@pumping_closure_lift_singleton char d0 L seed out Hseed Hseedout).
  Qed.

  Lemma prefix_of_take p s :
    prefix_of p s -> p = take (size p) s.
  Proof.
    move=> [t ->].
    by rewrite take_size_cat.
  Qed.

  Lemma prefix_of_comparable_by_size p q s :
    prefix_of p s ->
    prefix_of q s ->
    size p <= size q ->
    prefix_of p q.
  Proof.
    move=> [prest ->] [qrest Hq] Hsize.
    exists (drop (size p) q).
    rewrite -{1}(cat_take_drop (size p) q).
    have Htake : p = take (size p) q.
    { have Heq := congr1 (take (size p)) Hq.
      move: Heq.
      rewrite take_size_cat //.
      rewrite (@takel_cat (size p) char q qrest Hsize).
      by []. }
    by rewrite -Htake.
  Qed.

  Lemma prefix_include_seeds_comparable (L : dlang) seed1 seed2 :
    prefix_include L ->
    L seed1 ->
    L seed2 ->
    prefix_of seed1 seed2 \/ prefix_of seed2 seed1.
  Proof.
    move=> [top Htop Hall] Hseed1 Hseed2.
    have Hpref1 : prefix_of seed1 top := Hall seed1 Hseed1.
    have Hpref2 : prefix_of seed2 top := Hall seed2 Hseed2.
    case Hle: (size seed1 <= size seed2).
    - left. exact: (prefix_of_comparable_by_size seed1 seed2 top Hpref1 Hpref2 Hle).
    - right.
      have Hlt : size seed2 < size seed1 by rewrite ltnNge Hle.
      have Hle' : size seed2 <= size seed1 := ltnW Hlt.
      exact: (prefix_of_comparable_by_size seed2 seed1 top Hpref2 Hpref1 Hle').
  Qed.

  Theorem prefix_include_pumping_closure_shuffle_closed_from_comparable_reseeding
      (L : dlang) :
    prefix_include L ->
    comparable_reseeding_complete L ->
    shuffle_closed (fun out => @pumping_closure char d0 L out).
  Proof.
    move=> Hprefix Hreseed.
    apply: reseeding_complete_pumping_closure_shuffle_closed.
    move=> seed1 seed2 out1 out2 out Hseed1 Hseed2 Hout1 Hout2 Hint.
    apply: Hreseed Hout1 Hout2 Hint.
    - exact: Hseed1.
    - exact: Hseed2.
    - exact: prefix_include_seeds_comparable Hprefix Hseed1 Hseed2.
  Qed.

  Definition perm_word (s u : word) :=
    perm_eq s u.

  Definition permall_seed (s u : word) :=
    exists2 p, prefix_of p s & perm_word p u.

  Definition perm_suffix_seed (s t u : word) :=
    exists2 p, perm_word s p & u = p ++ t.

  Definition permutation_extended (L : dlang) (s t : word) :=
    forall u, L u <-> permall_seed s u \/ perm_suffix_seed s t u.

  Lemma interleaving_size u v w :
    @interleaving char u v w -> size w = size u + size v.
  Proof.
    elim=> [v0|u0|a0 u0 v0 w0 _ IH|b0 u0 v0 w0 _ IH] /=;
      by rewrite ?add0n ?addn0 ?IH ?addnS.
  Qed.

  Lemma interleaving_count_mem c u v w :
    @interleaving char u v w ->
    count_mem c w = count_mem c u + count_mem c v.
  Proof.
    elim=> [v0|u0|a0 u0 v0 w0 _ IH|b0 u0 v0 w0 _ IH] /=.
    - by [].
    - by rewrite addn0.
    - by rewrite IH addnA.
    - by rewrite IH addnCA.
  Qed.

  Lemma perm_word_count s u c :
    perm_word s u -> count_mem c s = count_mem c u.
  Proof.
    move/permP=> Hperm.
    exact: Hperm.
  Qed.

  Lemma permall_seed_count_le s u c :
    permall_seed s u ->
    count_mem c u <= count_mem c s.
  Proof.
    move=> [p [rest ->] Hperm].
    rewrite -(perm_word_count p u c Hperm).
    by rewrite count_cat leq_addr.
  Qed.

  Lemma pump_semantic_count_ge X s out c :
    @pump_semantic char X s out ->
    count_mem c s <= count_mem c out.
  Proof.
    elim=> [Y|Y a0 rest block out0 _ _ IH] //=.
    rewrite count_cat /= leq_add2l.
    apply: leq_trans IH _.
    by rewrite addnC leq_addr.
  Qed.

  Lemma pumping_closure_singleton_count_ge s out c :
    @pumping_closure char d0 (pred1 s) out ->
    count_mem c s <= count_mem c out.
  Proof.
    move=> Hclos.
    apply: pump_semantic_count_ge.
    exact: (@pumping_closure_singleton_to_semantic char d0 s out Hclos).
  Qed.
End InterleavingSpecificAttempts.
*)
