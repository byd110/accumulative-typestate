(* Two distinct persistent protocol structures: ordered milestones and
   independently configured services.  These are concrete three-/four-event
   instances of the generic monotone-machine construction. *)
From Coq Require Import List Bool.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import dfa.
From Accumulation Require Import trace_languages protocols syntax semantics
  typestate copying_typestate monotone_protocols monotone_regular
  persistent_pattern_queries accumulation_bridge certification
  coverage_simulation pattern_seed_automata.
Set Implicit Arguments.

Definition milestone_alphabet := Finite.clone (option bool) _.
Definition milestone_state := Finite.clone (bool * bool * bool)%type _.
Local Notation t := (@None bool).
Local Notation i := (Some false).
Local Notation r := (Some true).
Definition milestone_enabled (s : milestone_state) (a : milestone_alphabet) :=
  match a with None => true | Some false => s.1.1 | Some true => s.1.2 end.
Definition milestone_step (s : milestone_state) (a : milestone_alphabet) : milestone_state :=
  match a with None => (true,s.1.2,s.2)
  | Some false => (s.1.1,true,s.2) | Some true => (s.1.1,s.1.2,true) end.
Definition milestone_complete (s : milestone_state) := s.2.
Definition milestone_initial : milestone_state := (false,false,false).
Definition milestone_machine : monotone_machine milestone_alphabet milestone_state.
Proof.
  refine {| mm_le := fun s z => (s.1.1 = true -> z.1.1 = true) /\
      (s.1.2 = true -> z.1.2 = true) /\ (s.2 = true -> z.2 = true);
    mm_enabled := fun s a => milestone_enabled s a = true;
    mm_step := milestone_step; mm_accept := fun s => milestone_complete s = true |}.
  - intros [[a b] c]. simpl. intuition.
  - intros [[a b] c] [[d e] f] [[g h] j]. simpl. intuition.
  - intros [[a b] c] [[d e] f] [[|]|]; simpl; intuition.
  - intros [[a b] c] [[d e] f] [[|]|]; simpl; intuition.
  - intros [[a b] c] [[|]|]; simpl; intuition.
  - intros [[a b] c] [[d e] f]. simpl. intuition.
Defined.
Lemma milestone_enabled_spec s a :
  milestone_enabled s a = true <-> mm_enabled milestone_machine s a.
Proof. reflexivity. Qed.
Lemma milestone_complete_spec s :
  milestone_complete s = true <-> mm_accept milestone_machine s.
Proof. reflexivity. Qed.
Definition milestone_suffix : seq milestone_alphabet := [::t;i;r].
Lemma milestone_suffix_completes s :
  exists z, persistent_run milestone_alphabet milestone_state milestone_machine milestone_enabled s milestone_suffix = Some z /\
    milestone_complete z = true.
Proof. exists (true,true,true). destruct s as [[a b] c]. split; reflexivity. Qed.
Definition milestone_family :=
  @persistent_family milestone_alphabet milestone_state milestone_machine
    milestone_enabled milestone_complete milestone_initial
    milestone_suffix milestone_suffix_completes.
Theorem milestone_copying_certified mode : copying_certified milestone_family mode.
Proof. apply persistent_copying_certified; [exact milestone_enabled_spec|exact milestone_complete_spec]. Qed.
Theorem milestone_accumulation_contract c : accumulation_contract (protocol milestone_family c).
Proof. apply persistent_accumulation_contract; [exact milestone_enabled_spec|exact milestone_complete_spec]. Qed.
Theorem milestone_pumping c u v :
  protocol milestone_family c u -> @pumping.pumping milestone_alphabet t u v ->
  protocol milestone_family c v.
Proof. apply persistent_pumping; [exact milestone_enabled_spec|exact milestone_complete_spec]. Qed.

Definition service_alphabet := Finite.clone (bool * bool)%type _.
Definition service_state := Finite.clone (bool * bool * bool * bool)%type _.
Local Notation st := (false,false).
Local Notation sw := (false,true).
Local Notation sc := (true,false).
Local Notation sq := (true,true).
Definition service_enabled (s : service_state) (a : service_alphabet) :=
  match a with (false,false) => true | (false,true) => s.1.1.1
  | (true,false) => true | (true,true) => s.1.2 end.
Definition service_step (s : service_state) (a : service_alphabet) : service_state :=
  match a with (false,false) => (true,s.1.1.2,s.1.2,s.2)
  | (false,true) => (s.1.1.1,true,s.1.2,s.2)
  | (true,false) => (s.1.1.1,s.1.1.2,true,s.2)
  | (true,true) => (s.1.1.1,s.1.1.2,s.1.2,true) end.
Definition service_complete (s : service_state) := s.1.1.2 && s.2.
Definition service_initial : service_state := (false,false,false,false).
Definition service_machine : monotone_machine service_alphabet service_state.
Proof.
  refine {| mm_le := fun s z => (s.1.1.1 = true -> z.1.1.1 = true) /\
      (s.1.1.2 = true -> z.1.1.2 = true) /\
      (s.1.2 = true -> z.1.2 = true) /\ (s.2 = true -> z.2 = true);
    mm_enabled := fun s a => service_enabled s a = true;
    mm_step := service_step; mm_accept := fun s => service_complete s = true |}.
  - intros [[[a b] c] d]. simpl. intuition.
  - intros [[[a b] c] d] [[[e f] g] h] [[[j k] l] m]. simpl. intuition.
  - intros [[[a b] c] d] [[[e f] g] h] [[] []]; simpl; intuition.
  - intros [[[a b] c] d] [[[e f] g] h] [[] []]; simpl; intuition.
  - intros [[[a b] c] d] [[] []]; simpl; intuition.
  - intros [[[a b] c] d] [[[e f] g] h] [H1 [H2 [H3 H4]]].
    simpl in *. move/andP => [Hb Hd]. apply/andP; split; auto.
Defined.
Lemma service_enabled_spec s a :
  service_enabled s a = true <-> mm_enabled service_machine s a.
Proof. reflexivity. Qed.
Lemma service_complete_spec s :
  service_complete s = true <-> mm_accept service_machine s.
Proof. reflexivity. Qed.
Definition service_suffix : seq service_alphabet := [::st;sw;sc;sq].
Lemma service_suffix_completes s :
  exists z, persistent_run service_alphabet service_state service_machine service_enabled s service_suffix = Some z /\
    service_complete z = true.
Proof. exists (true,true,true,true). destruct s as [[[a b] c] d]. split; reflexivity. Qed.
Definition service_family :=
  @persistent_family service_alphabet service_state service_machine
    service_enabled service_complete service_initial service_suffix service_suffix_completes.
Theorem service_copying_certified mode : copying_certified service_family mode.
Proof. apply persistent_copying_certified; [exact service_enabled_spec|exact service_complete_spec]. Qed.
Theorem service_accumulation_contract c : accumulation_contract (protocol service_family c).
Proof. apply persistent_accumulation_contract; [exact service_enabled_spec|exact service_complete_spec]. Qed.
Theorem service_pumping c u v :
  protocol service_family c u -> @pumping.pumping service_alphabet st u v ->
  protocol service_family c v.
Proof. apply persistent_pumping; [exact service_enabled_spec|exact service_complete_spec]. Qed.

(* Concrete controls distinguish the structures from a single common gate. *)
Example milestone_order_required : viable milestone_family 0 [::t;r] = false.
Proof. reflexivity. Qed.
Example milestone_earlier_stages_repeat :
  accepts milestone_family 0 [::t;i;r;t;r] = true /\
  accepts milestone_family 0 [::t;i;r;i] = true.
Proof. split; reflexivity. Qed.
Example service_first_query_before_second_setup :
  viable service_family 0 [::st;sw] = true /\
  accepts service_family 0 [::st;sw] = false /\
  accepts service_family 0 [::st;sw;sc;sq] = true.
Proof. repeat split; reflexivity. Qed.
Example service_other_order_completes : accepts service_family 0 [::sc;sq;st;sw] = true.
Proof. reflexivity. Qed.
Example service_own_setup_required : viable service_family 0 [::st;sq] = false.
Proof. reflexivity. Qed.
