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

  (* Finite set of letters available up to prefix length j+1 (capped at |w0|) *)
  Definition sigma (w0 : word) (j : nat) : {set char} :=
    [set x
     | x \in [seq nth d0 w0 k
              | k <- iota 0 (minn j.+1 (size w0))] ].

  Notation collection := {set {set char}}.

  Definition union_of (S : collection) : {set char} :=
    \big[@setU char / set0]_(A in S) A.

  Definition collection_product (C D : collection) : collection :=
    [set (A :|: B) | A in C, B in D].

  Definition collection_star (C : collection) : collection :=
    [set union_of S | S in [set S : collection | S \subset C]].

  Lemma collection_starP (C : collection) (A : {set char}) :
    reflect (exists2 S : collection, S \subset C & A = union_of S)
      (A \in collection_star C).
  Proof.
    apply: (iffP imsetP) => [[S HS ->] | [S HS ->]].
    - by exists S; rewrite inE in HS.
    - by exists S; rewrite ?inE.
  Qed.
  
  (* Symbol Collection: the set of?> mmmm symbol collections possibly available for given regex *)
  Fixpoint symbol_collections (r : regexp) : collection :=
    match r with
    | Void => set0
    | Eps => set0
    | Atom c => [set [set c]]
    | Plus r1 r2 => symbol_collections r1 :|: symbol_collections r2
    | Conc r1 r2 => collection_product (symbol_collections r1) (symbol_collections r2)
    | Star r => collection_star (symbol_collections r)
    end.

  Lemma symbol_collections_starP (r : regexp) (A : {set char}) :
    reflect
      (exists2 S : collection, S \subset symbol_collections r & A = union_of S)
      (A \in symbol_collections (Star r)).
  Proof. exact: collection_starP. Qed.

  (* Union of sigleton symbols from the alphabet `X` *)
  Definition re_of_set (X : {set char}) : regexp :=
    \big[@Plus char / @Void char]_(c in X)
      (Atom c).
  
  (* Exact-branch semantics: start with exactly `A`, end with exactly `B`. *)
  Definition atom_branch_out (c : char) (A : {set char}) : regexp :=
    Conc (Atom c) (Star (re_of_set (A :|: [set c]))).

  Inductive pump_branch : regexp -> {set char} -> {set char} -> regexp -> Prop :=
  | pb_eps A :
      pump_branch Eps A A Eps
  | pb_atom A c :
      pump_branch (Atom c) A (A :|: [set c]) (atom_branch_out c A)
  | pb_plus_l r1 r2 A B out :
      pump_branch r1 A B out ->
      pump_branch (Plus r1 r2) A B out
  | pb_plus_r r1 r2 A B out :
      pump_branch r2 A B out ->
      pump_branch (Plus r1 r2) A B out
  | pb_conc r1 r2 A B C out1 out2 :
      pump_branch r1 A B out1 ->
      pump_branch r2 B C out2 ->
      pump_branch (Conc r1 r2) A C (Conc out1 out2)
  | pb_star0 r A :
      pump_branch (Star r) A A Eps
  | pb_starS r A B C out1 out2 :
      pump_branch r A B out1 ->
      pump_branch (Star r) B C out2 ->
      pump_branch (Star r) A C (Conc out1 out2).

  (* Collection-level semantics: finite unions of exact correlated branches. *)
  Inductive pump_semantic : regexp -> collection -> collection -> regexp -> Prop :=
  | pt_branch r (o : collection) A B out:
      A \in o ->
      pump_branch r A B out ->
      pump_semantic r o [set B] out
  | pt_union r (o o1 o2 : collection) out1 out2:
      pump_semantic r o o1 out1 ->
      pump_semantic r o o2 out2 ->
      pump_semantic r o (o1 :|: o2) (Plus out1 out2).

  Fixpoint word_symbols (u : word) : {set char} :=
    if u is a :: u' then [set a] :|: word_symbols u' else set0.

  Inductive staged_expansion : {set char} -> word -> word -> Prop :=
  | staged_nil A :
      staged_expansion A [::] [::]
  | staged_cons A a u extras w :
      all (fun c => c \in A :|: [set a]) extras ->
      staged_expansion (A :|: [set a]) u w ->
      staged_expansion A (a :: u) (a :: (extras ++ w)).

  Definition branch_invariant
      (r : regexp) (A B : {set char}) (w : word) :=
    exists u,
      [/\ u \in r, B = A :|: word_symbols u
        & staged_expansion A u w].

  Definition universal_invariant
      (r : regexp) (o o' : collection) (w : word) :=
    exists A u,
      [/\ A \in o, A :|: word_symbols u \in o', u \in r
        & staged_expansion A u w].

  Lemma pump_branch_regular (r : regexp) A B out :
    pump_branch r A B out ->
    RegLang.dfa.regular (fun w : word => is_true (w \in out)).
  Proof.
    move=> _.
    case: (@regularP char (fun w : word => is_true (w \in out)))
      => _ Hregular.
    apply: Hregular.
    by exists out.
  Qed.

  Lemma pump_semantic_regular (r : regexp) o o' out :
    pump_semantic r o o' out ->
    RegLang.dfa.regular (fun w : word => is_true (w \in out)).
  Proof.
    move=> _.
    case: (@regularP char (fun w : word => is_true (w \in out)))
      => _ Hregular.
    apply: Hregular.
    by exists out.
  Qed.

  Lemma string_pump_branch_exists (w0 : word) A :
    { Bo : {set char} * regexp |
      pump_branch (String w0) A Bo.1 Bo.2 }.
  Proof.
    elim: w0 A => [|a w0 IHw] A /=.
    - exists (A, Eps). exact: pb_eps.
    - case: (IHw (A :|: [set a])) => [[B out] Hout].
      exists (B, Conc (atom_branch_out a A) out).
      apply: pb_conc.
      + exact: pb_atom.
      + exact: Hout.
  Qed.

  Lemma singleton_pump_semantic_exists (w0 : word) :
    { oo : collection * regexp |
      pump_semantic (String w0) [set set0] oo.1 oo.2 }.
  Proof.
    case: (string_pump_branch_exists w0 set0) => [[B out] Hout].
    exists ([set B], out).
    apply: pt_branch.
    - by rewrite inE.
    - exact: Hout.
  Qed.

  Theorem singleton_pump_semantic_regular (w0 : word) :
    { oo : collection * regexp &
      pump_semantic (String w0) [set set0] oo.1 oo.2 *
      RegLang.dfa.regular (fun w : word => is_true (w \in oo.2)) }%type.
  Proof.
    case: (singleton_pump_semantic_exists w0) => [[o out] Hout].
    exists (o, out); split=> //.
    exact: pump_semantic_regular Hout.
  Qed.
    
  (* S0* · w0[0] · S1* · w0[1] · ... · S_{n-1}* · w0[n-1] · Sn*  *)
  Definition pumping_re (w0 : word) : RegLang.regexp.regexp char :=
    let n := size w0 in
    let fix build (j : nat) :=
      match j with
      | 0 =>
          RegLang.regexp.Star (re_of_set (sigma w0 0))
      | j'.+1 =>
          RegLang.regexp.Conc
            (build j')
            (RegLang.regexp.Conc
               (RegLang.regexp.Atom (nth d0 w0 j'))
               (RegLang.regexp.Star (re_of_set (sigma w0 j'.+1))))
      end
    in build n.

  (* This is the main semantic lemma you need to prove (by an invariant / induction on j). *)
  Lemma pumping_re_correct (w0 w : word) :
    @pumping_closure_singleton_dlang char d0 w0 w <-> (w \in pumping_re w0).
  Proof.
    (* TODO:
       Prove “reachable (|w|-|w0|) w0 w” iff w matches the staged decomposition:
         - before seeing w0[0], only Sj 0 letters can appear (actually Sj 0 is {w0[0]})
         - between w0[j] and w0[j+1], only Sj j letters can be inserted
         - after finishing w0, only Sj n letters can be inserted
       This is exactly what pumping_re encodes. *)
  Admitted.

  (* Regularity of the decidable singleton closure language *)
  Theorem pumping_closure_singleton_regular (w0 : word) :
    RegLang.dfa.regular (fun w => @pumping_closure_singleton_dlang char d0 w0 w).
  Proof.

    case: (@regularP char
      (fun w : word => is_true (@pumping_closure_singleton_dlang char d0 w0 w)))
      => _ Hregular.
    apply: Hregular.
    exists (pumping_re w0) => w.
    exact: pumping_re_correct.
  Qed.

  (* Regularity of the inductive (Prop) pumping_closure, via regular_ext + singleton_eq *)
  Theorem pumping_closure_regular (w0 : word) :
    RegLang.dfa.regular (fun w => @pumping_closure char d0 (pred1 w0) w).
  Proof.
    apply: (RegLang.dfa.regular_ext (L2 := fun w =>
      @pumping_closure_singleton_dlang char d0 w0 w)
      (pumping_closure_singleton_regular w0)).
    move=> w; exact: (@pumping_closure_singleton_eq char d0 w0 w).
  Qed.

End PumpingClosureRegularity.
