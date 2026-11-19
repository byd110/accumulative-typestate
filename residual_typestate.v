(* The class/history checker implements the paper's regular-expression rules.
   Environment equality is observational: obsolete association-list entries
   impose no obligations.  The converse assumes related input environments;
   it does not assert that every expression is a class-history residual. *)
From Coq Require Import List Arith Bool.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import languages dfa regexp.
From Accumulation Require Import syntax trace_languages protocols typestate regular_protocols.
Import ListNotations.
Set Implicit Arguments.

Section RegexOperations.
Variable A : finType.
Definition denote (r : regexp A) : language A := fun w => (w \in r) = true.
Definition regex_nullable (r : regexp A) := ([] \in r).
Definition regex_nonempty (r : regexp A) : bool := dfa_inhab (re_to_dfa r).

(* Any expression for the left quotient implements the paper's derivative.
   This verified construction reuses RegLang's DFA/expression conversions. *)
Definition regex_derivative (a : A) (r : regexp A) : regexp A :=
  dfa_to_re (restart (re_to_dfa r) (delta (dfa_s (re_to_dfa r)) [a])).

Lemma regex_derivative_correct a r w :
  denote (regex_derivative a r) w <-> denote r (a :: w).
Proof.
  unfold denote, regex_derivative.
  by rewrite -dfa_to_re_correct restart_accept re_to_dfa_correct.
Qed.
Lemma regex_nullable_spec r : regex_nullable r = true <-> denote r [].
Proof. reflexivity. Qed.
Lemma regex_nonempty_spec r : regex_nonempty r = true <-> exists w, denote r w.
Proof.
  split.
  - move/dfa_inhabP=> [w Hw]. exists w.
    unfold denote. by move: Hw; rewrite re_to_dfa_correct.
  - move=> [w Hw]. apply/dfa_inhabP; exists w.
    by rewrite re_to_dfa_correct.
Qed.
End RegexOperations.

Section ResidualRepresentation.
Variable A : finType.
Variable P : protocol_family A.
Variable field_type : class -> field -> class.
Variable initial : class -> regexp A.
Hypothesis initial_correct : forall c w, denote (initial c) w <-> protocol P c w.

Definition represents c w (r : regexp A) :=
  forall v, denote r v <-> residual (protocol P c) w v.
Definition regex_environment := fmap (class * regexp A).
Definition environments_related (g : environment A) (G : regex_environment) :=
  forall x, match get g x, get G x with
  | None, None => True
  | Some (c,w), Some (d,r) => c = d /\ represents c w r
  | _, _ => False
  end.

Lemma initial_represents c : represents c [] (initial c).
Proof. intros v; apply initial_correct. Qed.
Lemma derivative_represents c w r a : represents c w r ->
  represents c (w ++ [a]) (regex_derivative a r).
Proof.
  intros H v. rewrite regex_derivative_correct H residual_snoc. reflexivity.
Qed.
Lemma represents_nullable c w r : represents c w r ->
  (regex_nullable r = true <-> accepts P c w = true).
Proof. intros H. rewrite regex_nullable_spec H residual_nullable. reflexivity. Qed.
Lemma represents_nonempty c w r : represents c w r ->
  (regex_nonempty r = true <-> viable P c w = true).
Proof.
  intros H. rewrite regex_nonempty_spec viable_spec.
  split; intros [v Hv]; exists v; apply H; exact Hv.
Qed.
Lemma related_empty : environments_related [] [].
Proof. intros x; exact I. Qed.
Lemma related_put g G x c w r : environments_related g G -> represents c w r ->
  environments_related (put g x (Some (c,w))) (put G x (Some (c,r))).
Proof.
  intros H Hr y. destruct (Nat.eq_dec y x) as [->|Hne].
  - rewrite !get_put_same. auto.
  - rewrite !get_put_other; [apply H|exact Hne|exact Hne].
Qed.
Lemma related_history_lookup g G x c w : environments_related g G ->
  get g x = Some (c,w) ->
  exists r, get G x = Some (c,r) /\ represents c w r.
Proof.
  intros H E. specialize (H x); rewrite E in H.
  destruct (get G x) as [[d r]|] eqn:Er; [|contradiction].
  destruct H as [-> H]. exists r; auto.
Qed.
Lemma related_regex_lookup g G x c r : environments_related g G ->
  get G x = Some (c,r) ->
  exists w, get g x = Some (c,w) /\ represents c w r.
Proof.
  intros H E. specialize (H x); rewrite E in H.
  destruct (get g x) as [[d w]|] eqn:Ew; [|contradiction].
  destruct H as [-> H]. exists w; auto.
Qed.

Definition regex_retirable (G : regex_environment) x :=
  match get G x with None => true | Some (_,r) => regex_nullable r end.
Definition regex_all_complete (G : regex_environment) :=
  forall x c r, get G x = Some (c,r) -> regex_nullable r = true.

Lemma retirable_correspondence g G x : environments_related g G ->
  (retirable P g x = true <-> regex_retirable G x = true).
Proof.
  intros H; specialize (H x). unfold retirable, regex_retirable.
  destruct (get g x) as [[c w]|], (get G x) as [[d r]|];
    try contradiction; [|reflexivity].
  destruct H as [-> H]. symmetry; now apply represents_nullable.
Qed.

Lemma completion_correspondence g G : environments_related g G ->
  (all_complete P g = true <-> regex_all_complete G).
Proof.
  intros HR. rewrite all_complete_spec. split.
  - intros H x c r E.
    destruct (related_regex_lookup x HR E) as [w [Ew Hrep]].
    apply (proj2 (represents_nullable Hrep)). now apply (H x c w).
  - intros H x c w E.
    destruct (related_history_lookup x HR E) as [r [Er Hrep]].
    apply (proj1 (represents_nullable Hrep)). now apply (H x c r).
Qed.

(* These are the paper's expression-valued transfer rules.  In particular,
   assignments and loads restart at initial, calls take a derivative, and
   Finish tests every current binding before returning the empty map. *)
Inductive regex_type_step : regex_environment -> statement A -> regex_environment -> Prop :=
| regex_type_new G x c : regex_retirable G x = true ->
    regex_nonempty (initial c) = true ->
    regex_type_step G (New x c) (put G x (Some (c,initial c)))
| regex_type_copy G x y c r : get G y = Some (c,r) ->
    regex_retirable G x = true -> regex_nonempty (initial c) = true ->
    regex_type_step G (Copy x y) (put G x (Some (c,initial c)))
| regex_type_load G x y f c r : get G y = Some (c,r) ->
    regex_retirable G x = true -> regex_nonempty (initial (field_type c f)) = true ->
    regex_type_step G (Load x y f) (put G x (Some (field_type c f,initial (field_type c f))))
| regex_type_store G x f y c r d q : get G x = Some (c,r) ->
    get G y = Some (d,q) -> field_type c f = d -> regex_type_step G (Store x f y) G
| regex_type_call G x a c r : get G x = Some (c,r) ->
    regex_nonempty (regex_derivative a r) = true ->
    regex_type_step G (Call x a) (put G x (Some (c,regex_derivative a r)))
| regex_type_finish G : regex_all_complete G -> regex_type_step G Finish [].

Inductive regex_typed_stmt : regex_environment -> statement A -> regex_environment -> Prop :=
| regex_typed_primitive G i G' : regex_type_step G i G' -> regex_typed_stmt G i G'
| regex_typed_skip G : regex_typed_stmt G Skip G
| regex_typed_seq G s Gm t G' : regex_typed_stmt G s Gm ->
    regex_typed_stmt Gm t G' -> regex_typed_stmt G (Seq s t) G'.

Theorem primitive_history_to_regex g i g' G :
  type_step P field_type g i g' -> environments_related g G ->
  exists G', regex_type_step G i G' /\ environments_related g' G'.
Proof.
  intros HT HR. destruct HT.
  - exists (put G x (Some (c,initial c))). split.
    + constructor.
      * apply (proj1 (retirable_correspondence x HR)); exact H.
      * apply (proj2 (represents_nonempty (initial_represents c))); exact H0.
    + apply related_put; [exact HR|apply initial_represents].
  - destruct (related_history_lookup y HR H) as [r [Er Hrep]].
    exists (put G x (Some (c,initial c))). split.
    + eapply regex_type_copy; [exact Er| |].
      * apply (proj1 (retirable_correspondence x HR)); exact H0.
      * apply (proj2 (represents_nonempty (initial_represents c))); exact H1.
    + apply related_put; [exact HR|apply initial_represents].
  - destruct (related_history_lookup y HR H) as [r [Er Hrep]].
    exists (put G x (Some (field_type c f,initial (field_type c f)))). split.
    + eapply regex_type_load; [exact Er| |].
      * apply (proj1 (retirable_correspondence x HR)); exact H0.
      * apply (proj2 (represents_nonempty (initial_represents (field_type c f)))); exact H1.
    + apply related_put; [exact HR|apply initial_represents].
  - destruct (related_history_lookup x HR H) as [r [Er Hrep]].
    destruct (related_history_lookup y HR H0) as [q [Eq Hq]].
    exists G; split; [eapply regex_type_store; eauto|exact HR].
  - destruct (related_history_lookup x HR H) as [r [Er Hrep]].
    exists (put G x (Some (c,regex_derivative a r))). split.
    + eapply regex_type_call; [exact Er|].
      apply (proj2 (represents_nonempty (derivative_represents a Hrep))); exact H0.
    + apply related_put; [exact HR|now apply derivative_represents].
  - exists []; split; [constructor|apply related_empty].
    apply (proj1 (completion_correspondence HR)); exact H.
Qed.

Theorem primitive_regex_to_history G i G' g :
  regex_type_step G i G' -> environments_related g G ->
  exists g', type_step P field_type g i g' /\ environments_related g' G'.
Proof.
  intros HT HR. destruct HT.
  - exists (put g x (Some (c,[]))). split.
    + constructor.
      * apply (proj2 (retirable_correspondence x HR)); exact H.
      * apply (proj1 (represents_nonempty (initial_represents c))); exact H0.
    + apply related_put; [exact HR|apply initial_represents].
  - destruct (related_regex_lookup y HR H) as [w [Ew Hrep]].
    exists (put g x (Some (c,[]))). split.
    + eapply type_copy; [exact Ew| |].
      * apply (proj2 (retirable_correspondence x HR)); exact H0.
      * apply (proj1 (represents_nonempty (initial_represents c))); exact H1.
    + apply related_put; [exact HR|apply initial_represents].
  - destruct (related_regex_lookup y HR H) as [w [Ew Hrep]].
    exists (put g x (Some (field_type c f,[]))). split.
    + eapply type_load; [exact Ew| |].
      * apply (proj2 (retirable_correspondence x HR)); exact H0.
      * apply (proj1 (represents_nonempty (initial_represents (field_type c f)))); exact H1.
    + apply related_put; [exact HR|apply initial_represents].
  - destruct (related_regex_lookup x HR H) as [w [Ew Hrep]].
    destruct (related_regex_lookup y HR H0) as [v [Ev Hv]].
    exists g; split; [eapply type_store; eauto|exact HR].
  - destruct (related_regex_lookup x HR H) as [w [Ew Hrep]].
    exists (put g x (Some (c,w ++ [a]))). split.
    + eapply type_call; [exact Ew|].
      apply (proj1 (represents_nonempty (derivative_represents a Hrep))); exact H0.
    + apply related_put; [exact HR|now apply derivative_represents].
  - exists []; split; [constructor|apply related_empty].
    apply (proj2 (completion_correspondence HR)); exact H.
Qed.

Theorem statement_history_to_regex g s g' G :
  typed_stmt P field_type g s g' -> environments_related g G ->
  exists G', regex_typed_stmt G s G' /\ environments_related g' G'.
Proof.
  intros HT; revert G. induction HT; intros G HR.
  - destruct (primitive_history_to_regex H HR) as [G' [HS HE]].
    exists G'; split; [now constructor|exact HE].
  - exists G; split; [apply regex_typed_skip|exact HR].
  - destruct (IHHT1 G HR) as [Gm [HS Hm]].
    destruct (IHHT2 Gm Hm) as [G' [HT Hg']].
    exists G'; split; [eapply regex_typed_seq; eauto|exact Hg'].
Qed.

Theorem statement_regex_to_history G s G' g :
  regex_typed_stmt G s G' -> environments_related g G ->
  exists g', typed_stmt P field_type g s g' /\ environments_related g' G'.
Proof.
  intros HT; revert g. induction HT; intros g HR.
  - destruct (primitive_regex_to_history H HR) as [g' [HS HE]].
    exists g'; split; [now constructor|exact HE].
  - exists g; split; [apply type_skip|exact HR].
  - destruct (IHHT1 g HR) as [gm [HS Hm]].
    destruct (IHHT2 gm Hm) as [g' [HT Hg']].
    exists g'; split; [eapply type_seq; eauto|exact Hg'].
Qed.

(* An executable check has precisely the expression-rule successes for every
   reachable representation.  Output maps remain related pointwise. *)
Theorem residual_checker_correspondence g G s : environments_related g G ->
  ((exists g', check_stmt P field_type s g = Some g') <->
   exists G', regex_typed_stmt G s G').
Proof.
  intros HR; split.
  - intros [g' HC]. apply check_stmt_spec in HC.
    destruct (statement_history_to_regex HC HR) as [G' [HT HE]]. now exists G'.
  - intros [G' HT].
    destruct (statement_regex_to_history HT HR) as [g' [HC HE]].
    exists g'; now apply check_stmt_spec.
Qed.

Lemma regex_typed_seq_inv G s t G' : regex_typed_stmt G (Seq s t) G' ->
  exists Gm, regex_typed_stmt G s Gm /\ regex_typed_stmt Gm t G'.
Proof. intros H; inversion H; subst; eauto. inversion H0. Qed.
Lemma regex_typed_finish_inv G G' : regex_typed_stmt G Finish G' -> G' = [].
Proof. intros H; inversion H; subst. inversion H0; reflexivity. Qed.
Lemma regex_instrument_output G s G' : regex_typed_stmt G (instrument s) G' -> G' = [].
Proof.
  intros H. destruct (regex_typed_seq_inv H) as [Gm [Hs Hf]].
  now apply regex_typed_finish_inv in Hf.
Qed.

Theorem residual_program_correspondence s :
  check_program P field_type s = true <->
  finish_free s /\ regex_typed_stmt [] (instrument s) [].
Proof.
  rewrite check_program_spec. split.
  - intros [HF HT]; split; [exact HF|].
    destruct (statement_history_to_regex HT related_empty) as [G' [HR HE]].
    have E := regex_instrument_output HR. subst G'; exact HR.
  - intros [HF HT]; split; [exact HF|].
    destruct (statement_regex_to_history HT related_empty) as [g' [HR HE]].
    destruct (typed_stmt_seq HR) as [gm [Hs Hf]].
    destruct (typed_stmt_finish Hf) as [_ E]. subst g'; exact HR.
Qed.

End ResidualRepresentation.

Section RegularInstance.
Variable A : finType.
Variable field_type : class -> field -> class.
Variable spec : class -> regexp A.
Lemma regular_initial_correct c w :
  denote (closure_regex (spec c)) w <-> protocol (regular_family spec) c w.
Proof.
  unfold denote, protocol, regular_family; simpl.
  by rewrite closure_regex_covered.
Qed.

(* This instance discharges the representation hypothesis for the executable
   regular-seed protocols used by the end-to-end client theorems. *)
Theorem regular_residual_program_correspondence s :
  check_program (regular_family spec) field_type s = true <->
  finish_free s /\ regex_typed_stmt field_type (fun c => closure_regex (spec c))
    [] (instrument s) [].
Proof.
  apply residual_program_correspondence.
  exact regular_initial_correct.
Qed.
End RegularInstance.
