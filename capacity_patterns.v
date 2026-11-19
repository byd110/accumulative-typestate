(* Reusable capacity for a finite set of resource identities.  None adds one
   slot; Some i occupies a slot only on its first occurrence. *)
From Coq Require Import List Bool Lia.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import languages dfa.
From Accumulation Require Import pumping trace_languages protocols copying_typestate
  accumulation_bridge syntax semantics typestate soundness.
Set Implicit Arguments.
Unset Strict Implicit.

Section Capacity.
Variable I : finType.
Local Notation E := (Finite.clone (option I) _).

Fixpoint capacity_adds (w : seq E) : nat :=
  if w is a :: v then (if a is None then 1 else 0) + capacity_adds v else 0.
Fixpoint capacity_used (w : seq E) : {set I} :=
  if w is a :: v then
    if a is Some i then i |: capacity_used v else capacity_used v
  else set0.
Fixpoint capacity_check (c : nat) (U : {set I}) (w : seq E) : bool :=
  (#|U| <= c) &&
  if w is a :: v then
    if a is Some i then capacity_check c (i |: U) v
    else capacity_check c.+1 U v
  else true.
Definition capacity_safe (w : seq E) := capacity_check 0 set0 w.
Definition capacity_complete (w : seq E) :=
  capacity_safe w && (capacity_used w != set0).

Lemma capacity_adds_cat u v : capacity_adds (u ++ v) = capacity_adds u + capacity_adds v.
Proof. by elim: u => [|[i|] u IH] /=; rewrite ?add0n ?addnA ?IH. Qed.
Lemma capacity_used_cat u v : capacity_used (u ++ v) = capacity_used u :|: capacity_used v.
Proof. by elim: u => [|[i|] u IH] /=; rewrite ?set0U ?IH ?setUA. Qed.
Lemma capacity_used_mem i w : (i \in capacity_used w) = (Some i \in w).
Proof.
  elim: w => [|[j|] w IH] /=; rewrite ?inE ?IH //.
Qed.
Lemma capacity_check_budget c U w : capacity_check c U w -> #|U| <= c.
Proof. by case: w => [|a w] /= /andP []. Qed.
Lemma capacity_setU1 i (U : {set I}) : i \in U -> i |: U = U.
Proof. by move=> Hi; apply/setUidPr; rewrite sub1set. Qed.

Lemma capacity_check_more c d U w : c <= d ->
  capacity_check c U w -> capacity_check d U w.
Proof.
  elim: w c d U => [|[i|] w IH] c d U Hcd /= /andP [HU Hw];
    apply/andP; split; try exact: (leq_trans HU Hcd); try done.
  - exact (IH c d (i |: U) Hcd Hw).
  - exact (IH c.+1 d.+1 U Hcd Hw).
Qed.

Lemma capacity_check_cat c U p q :
  capacity_check c U (p ++ q) =
  capacity_check c U p && capacity_check (c + capacity_adds p) (U :|: capacity_used p) q.
Proof.
  elim: p c U => [|[i|] p IH] c U /=.
  - rewrite addn0 setU0 andbT.
    case H: (capacity_check c U q); last by rewrite andbF.
    by rewrite (capacity_check_budget H).
  - rewrite IH add0n (setUCA U [set i]) setUA.
    by rewrite andbA.
  - rewrite IH add1n addnS addSn.
    by rewrite andbA.
Qed.

Lemma capacity_check_final c U w : capacity_check c U w ->
  #|U :|: capacity_used w| <= c + capacity_adds w.
Proof.
  move=> H; have := H.
  rewrite -[w]cats0 capacity_check_cat => /andP [_].
  by rewrite cats0 /= andbT.
Qed.

Lemma capacity_safeP w : reflect
  (forall p q, w = p ++ q -> #|capacity_used p| <= capacity_adds p)
  (capacity_safe w).
Proof.
  apply: (iffP idP).
  - move=> H p q Heq; move: H.
    rewrite Heq /capacity_safe capacity_check_cat => /andP [Hp _].
    by move: (capacity_check_final Hp); rewrite set0U add0n.
  - move=> H; rewrite /capacity_safe.
    suff Hgen : forall p q, w = p ++ q ->
      capacity_check (capacity_adds p) (capacity_used p) q.
      by apply: (Hgen [::] w).
    move=> p q; elim: q p => [|[i|] q IH] p Heq /=.
    + by rewrite (H p [::] Heq).
    + apply/andP; split; first exact: H p (Some i :: q) Heq.
      have Heq' : w = (p ++ [::Some i]) ++ q by rewrite -catA.
      have := IH (p ++ [::Some i]) Heq'.
      by rewrite capacity_adds_cat capacity_used_cat /= !addn0 setU0 setUC.
    + apply/andP; split; first exact: H p (None :: q) Heq.
      have Heq' : w = (p ++ [::None]) ++ q by rewrite -catA.
      have := IH (p ++ [::None]) Heq'.
      by rewrite capacity_adds_cat capacity_used_cat /= addn1 setU0.
Qed.

Lemma capacity_union_budget c d (U V : {set I}) : #|U| <= c -> #|V| <= d -> #|U :|: V| <= c + d.
Proof.
  move=> HU HV; rewrite cardsU.
  exact: leq_trans (leq_subr _ _) (leq_add HU HV).
Qed.

Lemma capacity_check_shuffle u v w : trace_languages.shuffle u v w ->
  forall c U d V, capacity_check c U u -> capacity_check d V v ->
  capacity_check (c + d) (U :|: V) w.
Proof.
  move=> Hsh; elim: Hsh => [|a u0 v0 w0 Hsh IH|a u0 v0 w0 Hsh IH] c U d V Hu Hv.
  - by rewrite /= (capacity_union_budget (capacity_check_budget Hu) (capacity_check_budget Hv)).
  - have Hb := capacity_union_budget (capacity_check_budget Hu) (capacity_check_budget Hv).
    case: a Hu => [i|] /= /andP [_ Hu]; rewrite /= Hb /=.
    + rewrite setUA. exact: IH Hu Hv.
    + rewrite -addSn. exact: IH Hu Hv.
  - have Hb := capacity_union_budget (capacity_check_budget Hu) (capacity_check_budget Hv).
    case: a Hv => [i|] /= /andP [_ Hv]; rewrite /= Hb /=.
    + rewrite -setUCA. exact: IH Hu Hv.
    + rewrite -addnS. exact: IH Hu Hv.
Qed.

Lemma capacity_used_shuffle u v w : trace_languages.shuffle u v w ->
  capacity_used w = capacity_used u :|: capacity_used v.
Proof.
  move=> Hsh; elim: Hsh => [|[i|] u0 v0 w0 Hsh IH|[i|] u0 v0 w0 Hsh IH] /=;
    rewrite ?setU0 ?IH ?setUA //.
  by rewrite (setUC [set i]).
Qed.

Theorem capacity_shuffle_closed :
  trace_languages.shuffle_closed (fun w => capacity_complete w = true).
Proof.
  move=> u v w /andP [Hu Hune] /andP [Hv Hvne] Hsh; apply/andP; split.
  - have H := capacity_check_shuffle Hsh Hu Hv.
    by move: H; rewrite add0n setU0.
  - rewrite (capacity_used_shuffle Hsh) setU_eq0.
    by rewrite (negbTE Hune).
Qed.

Lemma capacity_check_insert c U p a q : a \in p ->
  capacity_check c U (p ++ q) -> capacity_check c U (p ++ a :: q).
Proof.
  rewrite !capacity_check_cat; move=> Ha /andP [Hp Hq]; rewrite Hp /=.
  have Hb := capacity_check_budget Hq.
  case: a Ha => [i|] Ha /=; rewrite Hb /=.
  - have Hi : i \in U :|: capacity_used p.
    { by rewrite inE capacity_used_mem Ha orbT. }
    by rewrite (capacity_setU1 Hi).
  - apply: capacity_check_more Hq. exact: leqnSn.
Qed.

Theorem capacity_complete_insert p a q : a \in p -> capacity_complete (p ++ q) ->
  capacity_complete (p ++ a :: q).
Proof.
  move=> Ha /andP [Hs Hne]; apply/andP; split.
  - exact: capacity_check_insert Ha Hs.
  - move: Hne; rewrite !capacity_used_cat.
    case: a Ha => [i|] Ha /=; last done.
    have Hi : i \in capacity_used p by rewrite capacity_used_mem.
    by rewrite setUA (setUC (capacity_used p) [set i]) (capacity_setU1 Hi).
Qed.

Theorem capacity_pumping_closed (d0 : E) u v :
  capacity_complete u -> pumping.pumping E d0 u v -> capacity_complete v.
Proof.
  move=> Hu Hp.
  have [p [q [a [Heu Hev Ha]]]] := pumping_decompose E d0 u v Hp.
  subst u v. exact: capacity_complete_insert Ha Hu.
Qed.

Lemma capacity_check_prefix c U p q :
  capacity_check c U (p ++ q) -> capacity_check c U p.
Proof. by rewrite capacity_check_cat => /andP []. Qed.

Lemma capacity_check_enough c U w : #|I| <= c -> capacity_check c U w.
Proof.
  elim: w c U => [|[i|] w IH] c U Hc /=;
    have HU : #|U| <= c := leq_trans (max_card U) Hc;
    rewrite HU /=; try done.
  - exact: IH Hc.
  - apply: IH. exact: leq_trans Hc (leqnSn c).
Qed.

Lemma capacity_check_additions c (U : {set I}) k w : #|U| <= c ->
  capacity_check (c + k) U w -> capacity_check c U (nseq k None ++ w).
Proof.
  elim: k c => [|k IH] c HU Hw; first by move: Hw; rewrite addn0.
  rewrite /= HU /=; apply: IH.
  - exact: leq_trans HU (leqnSn c).
  - by move: Hw; rewrite addnS addSn.
Qed.

Lemma capacity_safe_completion (default : I) w : capacity_safe w ->
  exists v, capacity_complete (w ++ v).
Proof.
  move=> Hs; rewrite /capacity_safe in Hs.
  exists (nseq #|I| None ++ [::Some default]); apply/andP; split.
  - rewrite /capacity_safe capacity_check_cat Hs /= add0n set0U.
    apply: capacity_check_additions.
    + by move: (capacity_check_final Hs); rewrite set0U add0n.
    + apply: capacity_check_enough. exact: leq_addl.
  - apply/eqP=> Hz.
    have Hin : default \in capacity_used (w ++ (nseq #|I| None ++ [::Some default])).
    { by rewrite capacity_used_mem !mem_cat mem_seq1 eqxx !orbT. }
    by move: Hin; rewrite Hz inE.
Qed.

Lemma capacity_viable_spec (default : I) w : capacity_safe w = true <->
  exists v, capacity_complete (w ++ v) = true.
Proof.
  split.
  - move=> Hs; exact (@capacity_safe_completion default w Hs).
  - move=> [v /andP [Hs _]]. exact: capacity_check_prefix Hs.
Qed.

Definition capacity_family (default : I) : protocol_family E :=
  {| accepts := fun _ => capacity_complete;
     viable := fun _ => capacity_safe;
     viable_spec := fun _ w => capacity_viable_spec default w |}.

Theorem capacity_certified default : certified (capacity_family default).
Proof. move=> c; exact: capacity_shuffle_closed. Qed.

(* The counter can be capped at the number of distinct identities.  The
   extra option is a permanent rejecting state for a failed prefix. *)
Definition capacity_cap (c : nat) : 'I_(#|I|).+1 :=
  @Ordinal (#|I|).+1 (minn #|I| c) (leq_ltn_trans (geq_minl _ _) (ltnSn _)).
Definition capacity_state := (Finite.clone (option ('I_(#|I|).+1 * {set I})) _).
Definition capacity_transition (q : capacity_state) (a : E) : capacity_state :=
  if q is Some (c,U) then
    if a is Some i then
      if #|i |: U| <= val c then Some (c, i |: U) else None
    else Some (capacity_cap (val c).+1, U)
  else None.
Definition capacity_final (q : capacity_state) : bool :=
  if q is Some (_,U) then U != set0 else false.
Definition capacity_dfa : dfa E :=
  {| dfa_state := capacity_state;
     dfa_s := Some (capacity_cap 0, set0);
     dfa_fin := [set q | capacity_final q];
     dfa_trans := capacity_transition |}.

Lemma capacity_cap_budget (U : {set I}) c :
  (#|U| <= val (capacity_cap c)) = (#|U| <= c).
Proof. by rewrite /= leq_min (max_card U). Qed.
Lemma capacity_cap_succ c :
  capacity_cap (val (capacity_cap c)).+1 = capacity_cap c.+1.
Proof.
  apply/val_inj => /=.
  case: (leqP c #|I|) => Hcn; first done.
  rewrite (minn_idPl (leqnSn #|I|)).
  by rewrite (minn_idPl (leq_trans (ltnW Hcn) (leqnSn c))).
Qed.
Lemma capacity_delta_dead w : @delta E capacity_dfa None w = None.
Proof. by elim: w => [|a w IH] /=. Qed.

Lemma capacity_delta c (U : {set I}) w : #|U| <= c ->
  @delta E capacity_dfa (Some (capacity_cap c,U)) w =
  if capacity_check c U w
  then Some (capacity_cap (c + capacity_adds w), U :|: capacity_used w)
  else None.
Proof.
  elim: w c U => [|[i|] w IH] c U HU.
  - by rewrite /= HU /= addn0 setU0.
  - rewrite /= HU /= /capacity_transition capacity_cap_budget.
    case Hnew: (#|i |: U| <= c).
    + rewrite (IH c (i |: U) Hnew) add0n.
      by rewrite setUCA setUA.
    + rewrite capacity_delta_dead.
      have Hbad : capacity_check c (i |: U) w = false.
      { apply/negP=> Hcheck. by move: (capacity_check_budget Hcheck); rewrite Hnew. }
      by rewrite Hbad.
  - rewrite /= HU /= /capacity_transition capacity_cap_succ.
    have HU' : #|U| <= c.+1 := leq_trans HU (leqnSn c).
    rewrite (IH c.+1 U HU').
    by rewrite add1n addnS addSn.
Qed.

Theorem capacity_dfa_correct w : (w \in dfa_lang capacity_dfa) = capacity_complete w.
Proof.
  rewrite inE /dfa_accept /= (capacity_delta (U := set0) w) ?cards0 //.
  rewrite /capacity_complete /capacity_safe.
  case H: (capacity_check 0 set0 w) => /=;
    by rewrite inE /capacity_final /= ?set0U.
Qed.

Theorem capacity_regular : regular (fun w => capacity_complete w).
Proof. exists capacity_dfa; move=> w; by rewrite capacity_dfa_correct. Qed.

(* Sharing a single allocation between two fresh identities is the precise
   obstruction to inheriting histories.  Repeated use of one identity is safe. *)
Lemma capacity_single_use i : capacity_complete [:: None; Some i] = true.
Proof.
  rewrite /capacity_complete /capacity_safe /= !cards0 !setU0 !cards1 /=.
  by rewrite -cards_eq0 cards1.
Qed.

Lemma capacity_two_uses_bad i j : i != j ->
  capacity_safe [:: None; Some i; Some j] = false.
Proof.
  move=> Hij; rewrite /capacity_safe /= !cards0 !setU0 !cards1 /=.
  by rewrite cardsU1 inE eq_sym (negbTE Hij) cards1.
Qed.

Lemma capacity_two_uses_incomplete i j : i != j ->
  capacity_complete [:: None; Some i; Some j] = false.
Proof. by move=> Hij; rewrite /capacity_complete (capacity_two_uses_bad Hij). Qed.

Theorem capacity_not_residual (i j : I) : i != j ->
  ~ residual_shuffle_closed (fun w => capacity_complete w = true).
Proof.
  move=> Hij H.
  have Hsh : trace_languages.shuffle [::Some i] [::Some j] [::Some i;Some j].
  { apply: shuffle_concat. }
  have Hbad := H [::None] [::Some i] [::Some j] [::Some i;Some j]
    (capacity_single_use i) (capacity_single_use j) Hsh.
  by move: Hbad; rewrite /residual /= (capacity_two_uses_incomplete Hij).
Qed.

Theorem capacity_not_kellogg (default : I) c (i j : I) : i != j ->
  ~ kellogg_error_closed (prefix_language (protocol (capacity_family default) c)).
Proof.
  move=> Hij H.
  have Hsub : trace_subsequence [::None] [::None;Some i].
  { constructor. constructor 3. constructor. }
  have Hi : prefix_language (protocol (capacity_family default) c) [::None;Some i].
  { apply viable_prefix, complete_viable. exact: capacity_single_use. }
  have Hbad : ~ prefix_language (protocol (capacity_family default) c)
    [::None;Some i;Some j].
  { rewrite -viable_prefix /= (capacity_two_uses_bad Hij). discriminate. }
  apply: (H [::None] [::None;Some i] (Some j) Hsub Hi Hbad).
  apply viable_prefix, complete_viable. exact: capacity_single_use.
Qed.

Theorem capacity_certified_not_kellogg (default : I) c (i j : I) : i != j ->
  certified (capacity_family default) /\
  ~ kellogg_error_closed (prefix_language (protocol (capacity_family default) c)).
Proof. move=> Hij; split; [exact: capacity_certified | exact: capacity_not_kellogg Hij]. Qed.

(* The generic checker theorems give the actual per-object capacity property,
   at every reachable prefix and at normal completion, respectively. *)
Corollary capacity_program_prefix_sound (default : I) FT s m :
  check_program (capacity_family default) FT s = true ->
  program_prefix s initial_machine m ->
  forall l, (l < next_loc m)%coq_nat -> capacity_safe (object_history m l) = true.
Proof.
  move=> HT HE l Hl.
  apply: (proj2 (viable_prefix (capacity_family default) (classes m l) _)).
  exact: (typestate_prefix_sound FT (@capacity_certified default) HT HE Hl).
Qed.

Corollary capacity_program_completion_sound (default : I) FT s m :
  check_program (capacity_family default) FT s = true ->
  program_execution s initial_machine m ->
  forall l, (l < next_loc m)%coq_nat -> capacity_complete (object_history m l) = true.
Proof.
  move=> HT HE l Hl.
  exact: (typestate_completion_sound FT (@capacity_certified default) HT HE Hl).
Qed.

(* A transparent implementation avoids the proof library's locked finite-set
   cardinality operations.  Its list of occupied identities is duplicate-free;
   the following refinement lemmas identify the exact same prefix language. *)
Fixpoint capacity_scan (c : nat) (used : seq I) (w : seq E) : bool :=
  (size used <= c) &&
  if w is a :: v then
    if a is Some i then
      capacity_scan c (if i \in used then used else i :: used) v
    else capacity_scan c.+1 used v
  else true.

Lemma capacity_card_seq (u : seq I) : uniq u -> #|[set::u]| = size u.
Proof.
  move/card_uniqP=> <-. apply: eq_card => i. by rewrite inE.
Qed.

Lemma capacity_scan_correct c u w : uniq u ->
  capacity_scan c u w = capacity_check c [set::u] w.
Proof.
  elim: w c u => [|[i|] w IH] c u Hu; rewrite /= (capacity_card_seq Hu) //.
  - case Hi: (i \in u).
    + rewrite (capacity_setU1 (U := [set::u])) ?inE //.
      by rewrite IH.
    + rewrite IH ?set_cons //; by rewrite /= Hi.
  - by rewrite IH.
Qed.

Lemma capacity_used_nonempty w :
  (capacity_used w != set0) = has (fun a => if a is Some _ then true else false) w.
Proof.
  elim: w => [|[i|] w IH] /=; rewrite ?eqxx //.
  apply/negP=> /eqP H0.
  have Hin : i \in i |: capacity_used w := setU11 i _.
  by move: Hin; rewrite H0 inE.
Qed.

Definition capacity_safe_query w := capacity_scan 0 [::] w.
Definition capacity_complete_query w :=
  capacity_safe_query w && has (fun a => if a is Some _ then true else false) w.

Lemma capacity_safe_query_correct w : capacity_safe_query w = capacity_safe w.
Proof. by rewrite /capacity_safe_query /capacity_safe capacity_scan_correct ?set_nil. Qed.

Lemma capacity_complete_query_correct w :
  capacity_complete_query w = capacity_complete w.
Proof.
  by rewrite /capacity_complete_query /capacity_complete capacity_safe_query_correct
    capacity_used_nonempty.
Qed.

Definition capacity_executable_family (default : I) : protocol_family E.
Proof.
  refine {| accepts := fun _ => capacity_complete_query;
            viable := fun _ => capacity_safe_query |}.
  move=> c w; rewrite capacity_safe_query_correct (capacity_viable_spec default).
  split=> [[v Hv]|[v Hv]]; exists v;
    by move: Hv; rewrite capacity_complete_query_correct.
Defined.

Theorem capacity_executable_certified default : certified (capacity_executable_family default).
Proof.
  move=> c u v w; rewrite /protocol /= !capacity_complete_query_correct.
  exact: capacity_shuffle_closed.
Qed.

End Capacity.

(* Executable regressions use two resource identities.  Both aliases reserve
   their own slot, so their independently completed histories may interleave. *)
Local Notation CapacityNames := (Finite.clone bool _).
Local Notation CapacityEvents := (Finite.clone (option bool) _).

Definition two_capacity_family : protocol_family CapacityEvents :=
  @capacity_executable_family CapacityNames false.
Definition capacity_fields (c : class) (_ : field) := c.

Definition capacity_alias_client : statement CapacityEvents := sequence
  [:: New 0 0; Copy 1 0; Call 0 None; Call 1 None;
      Call 0 (Some false); Call 1 (Some true)].

Example capacity_alias_client_accepted :
  check_program two_capacity_family capacity_fields capacity_alias_client = true.
Proof. by vm_compute. Qed.

Definition capacity_reuse_client : statement CapacityEvents := sequence
  [:: New 0 0; Call 0 None; Call 0 (Some false); Call 0 (Some false)].

Example capacity_reuse_client_accepted :
  check_program two_capacity_family capacity_fields capacity_reuse_client = true.
Proof. by vm_compute. Qed.

Definition capacity_overdraw_client : statement CapacityEvents := sequence
  [:: New 0 0; Call 0 None; Call 0 (Some false); Call 0 (Some true)].

Example capacity_overdraw_client_rejected :
  check_program two_capacity_family capacity_fields capacity_overdraw_client = false.
Proof. by vm_compute. Qed.

Definition capacity_unfinished_alias_client : statement CapacityEvents := sequence
  [:: New 0 0; Copy 1 0; Call 0 None; Call 0 (Some false)].

Example capacity_unfinished_alias_client_rejected :
  check_program two_capacity_family capacity_fields capacity_unfinished_alias_client = false.
Proof. by vm_compute. Qed.

(* A final count test would accept this trace, but its first use has already
   exceeded the capacity.  The prefix-sensitive query and DFA both reject it. *)
Example capacity_late_allocation_rejected :
  @capacity_safe CapacityNames [:: Some false; None] = false /\
  ([:: Some false; None] \in dfa_lang (capacity_dfa CapacityNames)) = false.
Proof.
  rewrite capacity_dfa_correct -capacity_safe_query_correct -capacity_complete_query_correct.
  by vm_compute.
Qed.

Definition capacity_alias_final : machine CapacityEvents :=
  let m := allocate initial_machine 0 0 in
  let m := bind m 1 0 in
  let m := emit m 0 None in
  let m := emit m 1 None in
  let m := emit m 0 (Some false) in
  let m := emit m 1 (Some true) in
  clear_refs m.

Example capacity_alias_client_terminates :
  program_execution capacity_alias_client initial_machine capacity_alias_final.
Proof.
  unfold capacity_alias_final. apply source_execution_instrument.
  - reflexivity.
  - unfold capacity_alias_client; simpl.
    repeat (eapply execution_seq;
      [apply execution_primitive; econstructor; reflexivity|]); constructor.
Qed.

Example capacity_alias_actual_history :
  next_loc capacity_alias_final = 1 /\ classes capacity_alias_final 0 = 0 /\
  object_history capacity_alias_final 0 = [::None;None;Some false;Some true].
Proof. vm_compute; auto. Qed.

Example capacity_alias_actual_history_complete :
  @capacity_complete CapacityNames (object_history capacity_alias_final 0) = true.
Proof.
  have H := typestate_completion_sound capacity_fields
    (@capacity_executable_certified CapacityNames false)
    capacity_alias_client_accepted capacity_alias_client_terminates
    (l := 0) (le_n 1).
  by move: H; rewrite /protocol /= capacity_complete_query_correct.
Qed.
