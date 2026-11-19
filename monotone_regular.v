(* Finite persistent-information machines enter the existing regular-seed
   pipeline without changing their accepted language. *)
From Coq Require Import List Bool.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import dfa regexp.
From Accumulation Require Import trace_languages protocols copying_typestate
  pumping certification regular_protocols residual_certification
  monotone_protocols monotone_pumping.
Set Implicit Arguments.

Section FiniteMonotoneMachines.
Variables A S : finType.
Variable default : A.
Variable M : monotone_machine A S.
Variable enabledb : S -> A -> bool.
Variable completeb : S -> bool.
Hypothesis enabledb_spec : forall s a, enabledb s a = true <-> mm_enabled M s a.
Hypothesis completeb_spec : forall s, completeb s = true <-> mm_accept M s.

Definition machine_dfa (initial : S) : dfa A :=
  {| dfa_state := Finite.clone (option S) _;
     dfa_s := Some initial;
     dfa_fin := [set q | if q is Some s then completeb s else false];
     dfa_trans := fun q a =>
       if q is Some s then
         if enabledb s a then Some (mm_step M s a) else None
       else None |}.

Lemma machine_dfa_dead initial w :
  @delta A (machine_dfa initial) None w = None.
Proof. by elim: w => [|a w IH] //=. Qed.

Lemma machine_run_dfa initial s w t : machine_run M s w t ->
  @delta A (machine_dfa initial) (Some s) w = Some t.
Proof.
  move=> H; induction H; simpl; first reflexivity.
  have E := proj2 (enabledb_spec s a) H.
  by rewrite E.
Qed.

Lemma machine_dfa_run initial w s t :
  @delta A (machine_dfa initial) (Some s) w = Some t -> machine_run M s w t.
Proof.
  elim: w s => [|a w IH] s /=.
  - move=> [<-]. constructor.
  - case E: (enabledb s a).
    + move=> H. econstructor; [apply (proj1 (enabledb_spec s a)); exact E|].
      exact: IH H.
    + rewrite machine_dfa_dead. discriminate.
Qed.

Theorem machine_dfa_language initial w :
  (w \in dfa_lang (machine_dfa initial)) <-> machine_language M initial w.
Proof.
  rewrite inE /dfa_accept.
  split.
  - case E: (delta (dfa_s (machine_dfa initial)) w) => [t|]; rewrite inE /=;
      last discriminate.
    move=> H. exists t; split.
    + exact: machine_dfa_run E.
    + exact: (proj1 (completeb_spec t) H).
  - move=> [t [Hr Ha]].
    rewrite (machine_run_dfa initial Hr) inE /=.
    exact: (proj2 (completeb_spec t) Ha).
Qed.

Theorem finite_machine_language_regular initial :
  regular (machine_language M initial).
Proof.
  exists (machine_dfa initial). move=> w. symmetry. apply machine_dfa_language.
Qed.

Definition machine_regex initial := dfa_to_re (machine_dfa initial).

Lemma machine_regex_language initial w :
  (w \in machine_regex initial) <-> machine_language M initial w.
Proof. rewrite /machine_regex -dfa_to_re_correct. apply machine_dfa_language. Qed.

Theorem finite_machine_closure_exact initial w :
  @pumping_closure A default (regex_lang A (machine_regex initial)) w <->
  machine_language M initial w.
Proof.
  apply machine_language_pumping_fixed_point.
  move=> u. exact: machine_regex_language.
Qed.

Theorem finite_machine_seed_certificate initial :
  certify_regex (machine_regex initial) = true.
Proof.
  apply (proj2 (certify_regex_spec default (machine_regex initial))).
  move=> u v w Hu Hv Hsh. apply finite_machine_closure_exact.
  apply (@machine_language_shuffle_closed A S M initial u v w).
  - exact: (proj1 (finite_machine_closure_exact initial u) Hu).
  - exact: (proj1 (finite_machine_closure_exact initial v) Hv).
  - apply interleaving_shuffle. exact Hsh.
Qed.

Theorem finite_machine_regular_family_language initial c w :
  protocol (regular_family (fun _ => machine_regex initial)) c w <->
  machine_language M initial w.
Proof.
  rewrite (regular_family_language default). apply finite_machine_closure_exact.
Qed.

Theorem finite_machine_copying_certificate initial :
  certify_copying_regex (machine_regex initial) = true.
Proof.
  apply (proj2 (certify_copying_regex_spec (fun _ => machine_regex initial) 0)).
  move=> p u v w Hu Hv Hsh. unfold trace_languages.residual in *.
  apply finite_machine_regular_family_language.
  apply (@machine_language_residual_shuffle_closed A S M initial p u v w).
  - exact: (proj1 (finite_machine_regular_family_language initial 0 (p ++ u)) Hu).
  - exact: (proj1 (finite_machine_regular_family_language initial 0 (p ++ v)) Hv).
  - exact Hsh.
Qed.
End FiniteMonotoneMachines.
