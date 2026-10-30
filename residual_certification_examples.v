(* The original condition does not imply the optional residual condition. *)
From Coq Require Import List Bool.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import dfa regexp.
From Accumulation Require Import pumping certification regular_protocols protocols trace_languages
  copying_typestate residual_certification.
Local Notation B := (Finite.clone (option bool) _).
Local Notation a := (@None bool).
Local Notation b := (Some false).
Local Notation c := (Some true).
Definition separating_seeds : seq (seq B) :=
  [:: [::a;b]; [::a;c]; [::a;a;b;c]; [::a;b;a;c]; [::a;a;c;b]; [::a;c;a;b]].
Definition separating_regex : regexp B :=
  Plus (Conc (Atom a) (Atom b))
  (Plus (Conc (Atom a) (Atom c))
  (Plus (Conc (Atom a) (Conc (Atom a) (Conc (Atom b) (Atom c))))
  (Plus (Conc (Atom a) (Conc (Atom b) (Conc (Atom a) (Atom c))))
  (Plus (Conc (Atom a) (Conc (Atom a) (Conc (Atom c) (Atom b))))
        (Conc (Atom a) (Conc (Atom c) (Conc (Atom a) (Atom b)))))))).
Definition separating_family := @regular_family B (fun _ => separating_regex).
Example separating_original_certificate : certify_regex separating_regex = true.
Proof. vm_compute. reflexivity. Qed.
Example separating_ab_complete : accepts separating_family 0 [::a;b] = true.
Proof. vm_compute. reflexivity. Qed.
Example separating_ac_complete : accepts separating_family 0 [::a;c] = true.
Proof. vm_compute. reflexivity. Qed.
Example separating_acb_incomplete : accepts separating_family 0 [::a;c;b] = false.
Proof. vm_compute. reflexivity. Qed.
Lemma separating_residual_not_closed : ~ residual_shuffle_closed (protocol separating_family 0).
Proof.
  intros H.
  have HC : trace_languages.shuffle [::c] [::b] [::c;b].
  { constructor. constructor 3. constructor. }
  have Hbad := H [::a] [::c] [::b] [::c;b] separating_ac_complete separating_ab_complete HC.
  change (accepts separating_family 0 [::a;c;b] = true) in Hbad.
  rewrite separating_acb_incomplete in Hbad. discriminate.
Qed.
Example separating_copy_certificate_rejected : certify_copying_regex separating_regex = false.
Proof.
  apply Bool.not_true_is_false. intros HC. apply separating_residual_not_closed.
  exact (proj1 (@certify_copying_regex_spec B (fun _ => separating_regex) 0) HC).
Qed.

(* Positive certification through the verified finite-decision interface. *)
Definition universal_dfa : dfa (Finite.clone bool _) :=
  {| dfa_state := Finite.clone unit _; dfa_s := tt;
     dfa_fin := setT; dfa_trans := fun _ _ => tt |}.
Example universal_residual_certificate : certify_residuals universal_dfa = true.
Proof.
  apply certify_residuals_spec. intros p u v w Hu Hv Hs.
  unfold trace_languages.residual. rewrite inE /dfa_accept /=. by rewrite inE.
Qed.
