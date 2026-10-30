(* Nonvacuity and boundaries of the language-level accumulation bridge. *)
From Coq Require Import List Arith Bool Lia.
From Accumulation Require Import trace_languages protocols syntax semantics
  copying_typestate copying_soundness examples copying_examples
  residual_certification_examples accumulation_bridge.
Import ListNotations.
Set Implicit Arguments.

Lemma accumulation_subsequence_length {A} (u v : list A) :
  trace_subsequence u v -> length u <= length v.
Proof. intros H; induction H; simpl; lia. Qed.

Lemma two_calls_prefix_characterization c w :
  prefix_language (protocol two_calls c) w <->
  forallb (fun b => b) w = true.
Proof. symmetry. exact (@viable_prefix bool two_calls c w). Qed.

Lemma two_calls_safe_extension c :
  subsequence_safe_extension (prefix_language (protocol two_calls c)).
Proof.
  intros u v a _ Hv Hua.
  apply two_calls_prefix_characterization in Hv.
  apply two_calls_prefix_characterization in Hua.
  apply two_calls_prefix_characterization.
  rewrite forallb_app in Hua. apply andb_true_iff in Hua.
  rewrite forallb_app, Hv. exact (proj2 Hua).
Qed.

Lemma two_calls_kellogg_error_closed c :
  kellogg_error_closed (prefix_language (protocol two_calls c)).
Proof. apply safe_extension_kellogg_error_closed, two_calls_safe_extension. Qed.

Lemma two_calls_completion_stable c : completion_stable (protocol two_calls c).
Proof.
  intros u v Hsub Hu Hv.
  change (two_calls_accept c u = true) in Hu.
  change (two_calls_accept c v = true).
  apply two_calls_prefix_characterization in Hv.
  unfold two_calls_accept in Hu |- *.
  apply andb_true_iff in Hu. destruct Hu as [_ Hlen].
  rewrite Hv. change ((2 <=? length v) = true).
  apply Nat.leb_le. apply Nat.leb_le in Hlen.
  pose proof (accumulation_subsequence_length Hsub). lia.
Qed.

Theorem two_calls_accumulation_contract c :
  accumulation_contract (protocol two_calls c).
Proof. split; auto using two_calls_safe_extension, two_calls_completion_stable. Qed.

Theorem two_calls_residuals_via_accumulation c :
  residual_shuffle_closed (protocol two_calls c).
Proof.
  apply accumulation_contract_residual_shuffle_closed, two_calls_accumulation_contract.
Qed.

Theorem two_calls_copying_certified_via_accumulation mode :
  copying_certified two_calls mode.
Proof.
  apply kellogg_protocol_copying_certified;
    auto using two_calls_kellogg_error_closed, two_calls_completion_stable.
Qed.

(* An existing, nontrivial accepted client inherits one call's evidence at an
   assignment.  Its object-completion guarantee now follows through the
   accumulation summary, rather than the earlier direct shuffle proof. *)
Theorem inherited_progress_sound_via_accumulation m :
  program_execution inherited_progress initial_machine m ->
  forall l, l < next_loc m ->
    protocol two_calls (classes m l) (object_history m l).
Proof.
  eapply copying_program_completion_sound.
  - apply two_calls_copying_certified_via_accumulation.
  - exact inherited_progress_accepted.
Qed.

(* Every unary history can be extended to an odd length.  Hence every
   ordinary call is safe, while two complete single calls need not compose
   to a complete history.  Safety alone cannot discharge completion. *)
Definition odd_unary_completion : language unit :=
  fun w => exists n, length w = 2 * n + 1.

Lemma odd_unary_prefix w : prefix_language odd_unary_completion w.
Proof.
  exists (tt :: w). unfold odd_unary_completion.
  exists (length w). rewrite length_app. simpl. lia.
Qed.

Example odd_unary_safe_extension :
  subsequence_safe_extension (prefix_language odd_unary_completion).
Proof. intros u v a Hsub Hv Hua. apply odd_unary_prefix. Qed.

Example odd_unary_kellogg_error_closed :
  kellogg_error_closed (prefix_language odd_unary_completion).
Proof. apply safe_extension_kellogg_error_closed, odd_unary_safe_extension. Qed.

Example odd_unary_not_shuffle_closed : ~ shuffle_closed odd_unary_completion.
Proof.
  intros H.
  assert (Hone : odd_unary_completion [tt]) by (exists 0; reflexivity).
  assert (Hsh : shuffle [tt] [tt] [tt;tt]) by
    (constructor; constructor 3; constructor).
  destruct (H [tt] [tt] [tt;tt] Hone Hone Hsh) as [n Hn]. simpl in Hn. lia.
Qed.

Example odd_unary_not_completion_stable : ~ completion_stable odd_unary_completion.
Proof.
  intros H.
  assert (Hone : odd_unary_completion [tt]) by (exists 0; reflexivity).
  assert (Hsub : trace_subsequence [tt] [tt;tt]) by
    (constructor; apply trace_subsequence_empty).
  destruct (H [tt] [tt;tt] Hsub Hone (odd_unary_prefix _)) as [n Hn].
  simpl in Hn. lia.
Qed.

(* Residual shuffle closure is weaker than the complete summary contract:
   a protocol may accept zero or at least two calls, but reject exactly one.
   Its residuals are shuffle closed even though completion can be lost along
   a viable extension.  No identification with a pumping closure is assumed. *)
Definition gap_unary_completion : language unit :=
  fun w => length w = 0 \/ 2 <= length w.

Lemma gap_unary_prefix w : prefix_language gap_unary_completion w.
Proof.
  exists [tt;tt]. right. rewrite length_app. simpl. lia.
Qed.

Example gap_unary_residual_shuffle_closed :
  residual_shuffle_closed gap_unary_completion.
Proof.
  intros p u v w Hu Hv Hsh.
  unfold residual, gap_unary_completion in *.
  rewrite !length_app in *. pose proof (shuffle_length Hsh). lia.
Qed.

Example gap_unary_not_completion_stable : ~ completion_stable gap_unary_completion.
Proof.
  intros H.
  assert (Hempty : gap_unary_completion []) by (left; reflexivity).
  pose proof (H [] [tt] (trace_subsequence_empty _) Hempty (gap_unary_prefix _)) as Hbad.
  unfold gap_unary_completion in Hbad. simpl in Hbad. lia.
Qed.

Example gap_unary_not_accumulation_contract : ~ accumulation_contract gap_unary_completion.
Proof. intros [_ Hcomplete]. exact (gap_unary_not_completion_stable Hcomplete). Qed.

(* The earlier seed-certified separation also lies outside this sufficient
   contract: its initial language is shuffle closed, but one residual is not. *)
Example separating_protocol_not_accumulation_contract :
  ~ accumulation_contract (protocol separating_family 0).
Proof.
  intros H. apply separating_residual_not_closed.
  now apply accumulation_contract_residual_shuffle_closed.
Qed.
