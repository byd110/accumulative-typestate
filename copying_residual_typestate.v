(* The optional checker implements copying of regular-expression residuals.
   Ordinary transfers reuse the baseline expression rules; enabled assignments
   inherit the source expression and retain outgoing-target completion. *)
From Coq Require Import List Bool.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import regexp.
From Accumulation Require Import syntax trace_languages protocols typestate
  regular_protocols copying_typestate residual_typestate.
Import ListNotations.
Set Implicit Arguments.

Section CopyingResidualRepresentation.
Variable A : finType.
Variable P : protocol_family A.
Variable FT : class -> field -> class.
Variable initial : class -> regexp A.
Variable mode : class -> bool.
Hypothesis initial_correct : forall c w, denote (initial c) w <-> protocol P c w.

Inductive regex_copy_type_step : regex_environment A -> statement A -> regex_environment A -> Prop :=
| regex_copy_ordinary G i G' : regex_type_step FT initial G i G' ->
    (forall x y, i <> Copy x y) -> regex_copy_type_step G i G'
| regex_copy_assignment G x y c r : get G y = Some (c,r) ->
    regex_retirable G x = true ->
    (if mode c then True else regex_nonempty (initial c) = true) ->
    regex_copy_type_step G (Copy x y)
      (put G x (Some (c,if mode c then r else initial c))).

Inductive regex_copy_typed_stmt : regex_environment A -> statement A -> regex_environment A -> Prop :=
| regex_copy_typed_primitive G i G' : regex_copy_type_step G i G' ->
    regex_copy_typed_stmt G i G'
| regex_copy_skip G : regex_copy_typed_stmt G Skip G
| regex_copy_seq G s Gm t G' : regex_copy_typed_stmt G s Gm ->
    regex_copy_typed_stmt Gm t G' -> regex_copy_typed_stmt G (Seq s t) G'.

Lemma ordinary_history_to_copy g i g' : type_step P FT g i g' ->
  (forall x y, i <> Copy x y) -> type_step_with_copy P FT mode g i g'.
Proof.
  intros H Hnot. destruct H.
  - constructor; assumption.
  - exfalso. exact (Hnot x y Logic.eq_refl).
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - constructor; assumption.
Qed.
Lemma ordinary_history_to_regex_copy g i g' G : type_step P FT g i g' ->
  (forall x y, i <> Copy x y) -> environments_related P g G ->
  exists G', regex_copy_type_step G i G' /\ environments_related P g' G'.
Proof.
  intros HT Hnot HR.
  destruct (primitive_history_to_regex initial initial_correct HT HR) as [G' [HE HG]].
  exists G'. split. now apply regex_copy_ordinary. exact HG.
Qed.

Theorem copying_primitive_history_to_regex g i g' G :
  type_step_with_copy P FT mode g i g' -> environments_related P g G ->
  exists G', regex_copy_type_step G i G' /\ environments_related P g' G'.
Proof.
  intros HT HR. destruct HT.
  - eapply ordinary_history_to_regex_copy; [constructor; eauto|discriminate|exact HR].
  - destruct (related_history_lookup y HR H) as [r [Er Hr]].
    exists (put G x (Some (c,if mode c then r else initial c))). split.
    + apply regex_copy_assignment with (r := r).
      * exact Er.
      * exact (proj1 (retirable_correspondence x HR) H0).
      * destruct (mode c); [exact I|].
        apply (proj2 (represents_nonempty (initial_represents initial initial_correct c))). exact H1.
    + destruct (mode c); apply related_put; auto.
      apply initial_represents. exact initial_correct.
  - eapply ordinary_history_to_regex_copy; [econstructor; eauto|discriminate|exact HR].
  - eapply ordinary_history_to_regex_copy; [econstructor; eauto|discriminate|exact HR].
  - eapply ordinary_history_to_regex_copy; [econstructor; eauto|discriminate|exact HR].
  - eapply ordinary_history_to_regex_copy; [constructor; eauto|discriminate|exact HR].
Qed.

Theorem copying_primitive_regex_to_history G i G' g :
  regex_copy_type_step G i G' -> environments_related P g G ->
  exists g', type_step_with_copy P FT mode g i g' /\ environments_related P g' G'.
Proof.
  intros HT HR. destruct HT.
  - destruct (primitive_regex_to_history initial_correct H HR) as [g' [Ht Hg]].
    exists g'. split. now apply ordinary_history_to_copy. exact Hg.
  - destruct (related_regex_lookup y HR H) as [w [Ew Hw]].
    exists (put g x (Some (c,if mode c then w else []))). split.
    + apply copy_type_copy with (w := w).
      * exact Ew.
      * exact (proj2 (retirable_correspondence x HR) H0).
      * destruct (mode c); [exact I|].
        apply (proj1 (represents_nonempty (initial_represents initial initial_correct c))). exact H1.
    + destruct (mode c); apply related_put; auto.
      apply initial_represents. exact initial_correct.
Qed.

Theorem copying_statement_history_to_regex g s g' G :
  typed_stmt_with_copy P FT mode g s g' -> environments_related P g G ->
  exists G', regex_copy_typed_stmt G s G' /\ environments_related P g' G'.
Proof.
  intros HT. revert G. induction HT; intros G HR.
  - destruct (copying_primitive_history_to_regex H HR) as [G' [Hs Hg]].
    exists G'. split; [now apply regex_copy_typed_primitive|exact Hg].
  - exists G. split; [apply regex_copy_skip|exact HR].
  - destruct (IHHT1 G HR) as [Gm [Hs Hm]].
    destruct (IHHT2 Gm Hm) as [G' [Ht Hg]].
    exists G'. split; [eapply regex_copy_seq; eauto|exact Hg].
Qed.
Theorem copying_statement_regex_to_history G s G' g :
  regex_copy_typed_stmt G s G' -> environments_related P g G ->
  exists g', typed_stmt_with_copy P FT mode g s g' /\ environments_related P g' G'.
Proof.
  intros HT. revert g. induction HT; intros g HR.
  - destruct (copying_primitive_regex_to_history H HR) as [g' [Hs Hg]].
    exists g'. split; [now apply copy_typed_primitive|exact Hg].
  - exists g. split; [apply copy_type_skip|exact HR].
  - destruct (IHHT1 g HR) as [gm [Hs Hm]].
    destruct (IHHT2 gm Hm) as [g' [Ht Hg]].
    exists g'. split; [eapply copy_type_seq; eauto|exact Hg].
Qed.
Theorem copying_residual_checker_correspondence g G s : environments_related P g G ->
  ((exists g', check_stmt_with_copy P FT mode s g = Some g') <->
   exists G', regex_copy_typed_stmt G s G').
Proof.
  intros HR. split.
  - intros [g' HC]. apply check_stmt_with_copy_spec in HC.
    destruct (copying_statement_history_to_regex HC HR) as [G' [HT HG]]. now exists G'.
  - intros [G' HT]. destruct (copying_statement_regex_to_history HT HR) as [g' [HC HG]].
    exists g'. now apply check_stmt_with_copy_spec.
Qed.
Lemma regex_copy_typed_seq_inv G s t G' : regex_copy_typed_stmt G (Seq s t) G' ->
  exists Gm, regex_copy_typed_stmt G s Gm /\ regex_copy_typed_stmt Gm t G'.
Proof.
  intros H. inversion H; subst; eauto.
  match goal with Hp : regex_copy_type_step _ (Seq _ _) _ |- _ => inversion Hp; subst end.
  match goal with Hp : regex_type_step _ _ _ (Seq _ _) _ |- _ => inversion Hp end.
Qed.
Lemma regex_copy_typed_finish_inv G G' : regex_copy_typed_stmt G Finish G' -> G' = [].
Proof.
  intros H. inversion H; subst.
  match goal with Hp : regex_copy_type_step _ Finish _ |- _ => inversion Hp; subst end.
  match goal with Hp : regex_type_step _ _ _ Finish _ |- _ => inversion Hp; reflexivity end.
Qed.
Lemma regex_copy_instrument_output G s G' :
  regex_copy_typed_stmt G (instrument s) G' -> G' = [].
Proof.
  intros H. destruct (regex_copy_typed_seq_inv H) as [Gm [Hs Hf]].
  now apply regex_copy_typed_finish_inv in Hf.
Qed.

Theorem copying_residual_program_correspondence s :
  check_program_with_copy P FT mode s = true <->
  finish_free s /\ regex_copy_typed_stmt [] (instrument s) [].
Proof.
  rewrite check_program_with_copy_spec. split.
  - intros [HF HT]. split; [exact HF|].
    destruct (copying_statement_history_to_regex HT (related_empty A P)) as [G' [HR HG]].
    have E := regex_copy_instrument_output HR. subst G'. exact HR.
  - intros [HF HT]. split; [exact HF|].
    destruct (copying_statement_regex_to_history HT (related_empty A P)) as [g' [HR HG]].
    apply check_stmt_with_copy_spec in HR.
    have E := check_stmt_with_copy_instrument P FT mode s [] HR. subst g'.
    now apply check_stmt_with_copy_spec.
Qed.
End CopyingResidualRepresentation.

Section RegularInstance.
Variable A : finType.
Variable FT : class -> field -> class.
Variable spec : class -> regexp A.
Variable mode : class -> bool.
Theorem copying_regular_residual_program_correspondence s :
  check_program_with_copy (regular_family spec) FT mode s = true <->
  finish_free s /\ regex_copy_typed_stmt FT (fun c => closure_regex (spec c)) mode
    [] (instrument s) [].
Proof.
  apply copying_residual_program_correspondence. exact (@regular_initial_correct A spec).
Qed.
End RegularInstance.
