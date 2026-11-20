(* Runnable exact-protocol example: K_last = u {u,b}* b.
   We encode u by false and b by true.  Requiring the final b is essential:
   ubub completes, while ubu is viable but incomplete. *)
From Coq Require Import List Bool Lia.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import dfa regexp.
From Accumulation Require Import pumping trace_languages protocols exact_protocols
  syntax semantics typestate soundness regular_protocols.
Set Implicit Arguments.

Local Notation B := (Finite.clone bool _).
Local Notation LastState := (Finite.clone (option (option bool)) _).

(* None: initial; Some None: rejecting sink; Some (Some b): a word
   starting with u has been read, and b is its most recent event. *)
Definition k_last_dfa : dfa B :=
  {| dfa_state := LastState; dfa_s := None;
     dfa_fin := [set q : LastState | q == Some (Some true)];
     dfa_trans := fun q a =>
       match q with
       | None => if a then Some None else Some (Some false)
       | Some None => Some None
       | Some (Some _) => Some (Some a)
       end |}.

Definition k_last (w : seq bool) : Prop :=
  exists middle, w = false :: (middle ++ [:: true]).

Lemma k_last_delta_live b w :
  @delta B k_last_dfa (Some (Some b)) w = Some (Some (last b w)).
Proof. by elim: w b => [|a w IH] b //=. Qed.

Lemma k_last_delta_dead w : @delta B k_last_dfa (Some None) w = Some None.
Proof. by elim: w => [|a w IH] //=. Qed.

Theorem k_last_dfa_language w : (w \in dfa_lang k_last_dfa) = true <-> k_last w.
Proof.
  case: w => [|a w].
  - rewrite inE /dfa_accept /= inE /=.
    split; [discriminate|intros [middle H]; discriminate].
  - case: a.
    + rewrite inE /dfa_accept /= k_last_delta_dead inE /=.
      split; [discriminate|intros [middle H]; discriminate].
    + rewrite inE /dfa_accept /= k_last_delta_live inE /=.
      case/lastP: w => [|middle b].
      * split; [discriminate|intros [middle H]; injection H => E].
        have Hsize := congr1 size E. by rewrite size_cat /= addn1 in Hsize.
      * rewrite last_rcons.
        split.
        -- move/eqP=> E. have Eb : b = true by injection E.
           subst b. exists middle. by rewrite -cats1.
        -- intros [middle' E]. have Hlast := congr1 (last false) E.
           rewrite /= last_rcons last_cat /= in Hlast. by rewrite Hlast.
Qed.

(* Both endpoints of a shuffle come from endpoints of its components. *)
Lemma shuffle_starts_with {A} (a : A) u v w :
  (exists u', u = a :: u') -> (exists v', v = a :: v') ->
  trace_languages.shuffle u v w -> exists w', w = a :: w'.
Proof.
  intros [u' ->] [v' ->] H. inversion H; subst; eauto.
Qed.

Lemma shuffle_reversed {A} (u v w : list A) :
  trace_languages.shuffle u v w ->
  trace_languages.shuffle (List.rev u) (List.rev v) (List.rev w).
Proof.
  intros H; induction H; simpl.
  - constructor.
  - replace (List.rev v) with (List.rev v ++ [::]) at 1
      by apply List.app_nil_r.
    apply shuffle_app; [exact IHshuffle|constructor; constructor].
  - replace (List.rev u) with (List.rev u ++ [::]) at 1
      by apply List.app_nil_r.
    apply shuffle_app; [exact IHshuffle|constructor 3; constructor].
Qed.

Lemma shuffle_ends_with {A} (a : A) u v w :
  (exists u', u = u' ++ [::a]) -> (exists v', v = v' ++ [::a]) ->
  trace_languages.shuffle u v w -> exists w', w = w' ++ [::a].
Proof.
  intros [u' ->] [v' ->] H.
  pose proof (shuffle_reversed H) as Hr.
  rewrite !List.rev_app_distr /= in Hr.
  have Hstart : exists w', List.rev w = a :: w'.
  { eapply shuffle_starts_with;
      [exists (List.rev u'); reflexivity|exists (List.rev v'); reflexivity|exact Hr]. }
  destruct Hstart as [w' Hw].
  exists (List.rev w'). rewrite <- (List.rev_involutive w), Hw. reflexivity.
Qed.

Theorem k_last_shuffle_closed : shuffle_closed k_last.
Proof.
  intros u v w [u' Hu] [v' Hv] Hs.
  have Hfirst : exists rest, w = false :: rest.
  { eapply shuffle_starts_with;
      [exists (u' ++ [::true]); exact Hu|exists (v' ++ [::true]); exact Hv|exact Hs]. }
  have Hlast : exists rest, w = rest ++ [::true].
  { eapply shuffle_ends_with.
    - exists (false :: u'); exact Hu.
    - exists (false :: v'); exact Hv.
    - exact Hs. }
  destruct Hfirst as [rest Hfirst]. destruct Hlast as [[|a middle] Hlast].
  - rewrite Hfirst in Hlast; discriminate.
  - rewrite Hfirst in Hlast. injection Hlast => Htail Ha.
    subst a. exists middle. by rewrite Hfirst Htail.
Qed.

(* Transparent queries avoid the proof library's locked finite-set
   representation.  Their equivalence to the exact DFA holds for every word. *)
Definition k_last_accept (w : seq bool) : bool :=
  if w is false :: rest then last false rest else false.
Definition k_last_viable (w : seq bool) : bool :=
  if w is a :: _ then ~~ a else true.

Lemma k_last_accept_dfa w : k_last_accept w = (w \in dfa_lang k_last_dfa).
Proof.
  case: w => [|a w].
  - by rewrite inE /dfa_accept /= inE.
  - case: a.
    + by rewrite inE /dfa_accept /= k_last_delta_dead inE.
    + rewrite inE /dfa_accept /= k_last_delta_live inE /=.
      by case: (last false w).
Qed.

Lemma k_last_queries w : k_last_viable w = true <->
  exists v, k_last_accept (w ++ v) = true.
Proof.
  case: w => [|a w].
  - split; [intros _; exists [::false;true]; reflexivity|intros _; reflexivity].
  - case: a.
    + split; [discriminate|intros [v Hv]; discriminate].
    + split; [|intros _; reflexivity].
      intros _; exists [::true]. by rewrite /k_last_accept /= last_cat.
Qed.

Definition k_last_family : protocol_family B :=
  {| accepts := fun _ => k_last_accept;
     viable := fun _ => k_last_viable;
     viable_spec := fun _ => k_last_queries |}.

Theorem k_last_exact_dfa_queries c w :
  accepts k_last_family c w = accepts (exact_dfa_family (fun _ => k_last_dfa)) c w /\
  viable k_last_family c w = viable (exact_dfa_family (fun _ => k_last_dfa)) c w.
Proof.
  split; first exact: k_last_accept_dfa.
  apply Bool.eq_true_iff_eq. rewrite !viable_spec. split; intros [v Hv]; exists v.
  - change ((w ++ v \in dfa_lang k_last_dfa) = true).
    by rewrite -k_last_accept_dfa.
  - change (k_last_accept (w ++ v) = true).
    by rewrite k_last_accept_dfa.
Qed.

Theorem k_last_exact_language c w : protocol k_last_family c w <-> k_last w.
Proof. change (k_last_accept w = true <-> k_last w).
  rewrite k_last_accept_dfa. apply k_last_dfa_language. Qed.

Theorem k_last_exact_certificate : certify_exact_dfa k_last_dfa = true.
Proof.
  apply (proj2 (certify_exact_dfa_spec k_last_dfa)). intros u v w Hu Hv Hs.
  apply k_last_dfa_language. apply (@k_last_shuffle_closed u v w); try assumption;
    now apply k_last_dfa_language.
Qed.

Theorem k_last_certified : certified k_last_family.
Proof.
  intros c u v w Hu Hv Hs.
  apply k_last_exact_language in Hu; apply k_last_exact_language in Hv.
  apply k_last_exact_language. exact (@k_last_shuffle_closed u v w Hu Hv Hs).
Qed.

Definition k_last_fields (c : class) (_ : field) := c.
Definition k_last_complete_client : statement bool := sequence
  [:: New 0 0; Call 0 false; Call 0 true; Call 0 false; Call 0 true].
Definition k_last_incomplete_client : statement bool := sequence
  [:: New 0 0; Call 0 false; Call 0 true; Call 0 false].

Example k_last_ubub_complete : accepts k_last_family 0 [::false;true;false;true] = true.
Proof. vm_compute; reflexivity. Qed.
Example k_last_ubu_incomplete : accepts k_last_family 0 [::false;true;false] = false.
Proof. vm_compute; reflexivity. Qed.
Example k_last_ubu_viable : viable k_last_family 0 [::false;true;false] = true.
Proof. vm_compute; reflexivity. Qed.
Example k_last_complete_client_accepted :
  check_program k_last_family k_last_fields k_last_complete_client = true.
Proof. vm_compute; reflexivity. Qed.
Example k_last_incomplete_client_rejected :
  check_program k_last_family k_last_fields k_last_incomplete_client = false.
Proof. vm_compute; reflexivity. Qed.

Definition k_last_complete_final : machine bool :=
  let m := allocate initial_machine 0 0 in
  let m := emit m 0 false in let m := emit m 0 true in
  let m := emit m 0 false in let m := emit m 0 true in clear_refs m.

Example k_last_complete_client_terminates :
  program_execution k_last_complete_client initial_machine k_last_complete_final.
Proof.
  unfold k_last_complete_client, k_last_complete_final.
  apply source_execution_instrument; [reflexivity|]. cbn [sequence].
  repeat (eapply execution_seq;
    [apply execution_primitive; econstructor; reflexivity|]); constructor.
Qed.
Example k_last_complete_actual_history : next_loc k_last_complete_final = 1 /\
  object_history k_last_complete_final 0 = [::false;true;false;true].
Proof. vm_compute; auto. Qed.
Theorem k_last_client_completion_sound m :
  program_execution k_last_complete_client initial_machine m ->
  forall l, (l < next_loc m)%coq_nat -> k_last (object_history m l).
Proof.
  intros HE l Hl. apply (proj1 (k_last_exact_language (classes m l) _)).
  exact (typestate_completion_sound k_last_fields k_last_certified
    k_last_complete_client_accepted HE Hl).
Qed.

(* Seed and exact-language interfaces intentionally answer differently. *)
Definition ub_seed_regex : regexp B := Conc (Atom false) (Atom true).
Definition ub_seed_family : protocol_family B := regular_family (fun _ => ub_seed_regex).
Example ub_seed_accepts_ubu : accepts ub_seed_family 0 [::false;true;false] = true.
Proof. vm_compute; reflexivity. Qed.
Example ubu_in_pumping_closure :
  @pumping_closure B false (fun w => w == [::false;true]) [::false;true;false].
Proof.
  eapply pumping_closure_step with (w := [::false;true]).
  - apply pumping_closure_base. reflexivity.
  - vm_compute; reflexivity.
Qed.
Example k_last_not_pumping_closed :
  k_last [::false;true] /\
  @pumping B false [::false;true] [::false;true;false] /\
  ~ k_last [::false;true;false].
Proof.
  split; [exists [::]; reflexivity|]. split; [vm_compute; reflexivity|].
  rewrite -k_last_dfa_language -k_last_accept_dfa. vm_compute. discriminate.
Qed.

(* Lightweight reproducible queries; no product-certificate enumeration. *)
Eval vm_compute in accepts k_last_family 0 [::false;true;false;true].
Eval vm_compute in accepts k_last_family 0 [::false;true;false].
Eval vm_compute in viable k_last_family 0 [::false;true;false].
Eval vm_compute in check_program k_last_family k_last_fields k_last_complete_client.
Eval vm_compute in check_program k_last_family k_last_fields k_last_incomplete_client.
Eval vm_compute in accepts ub_seed_family 0 [::false;true;false].
