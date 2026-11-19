(* Structural bounds of raw executions, independent of protocol checks. *)
From Coq Require Import List Arith Bool Lia.
From Accumulation Require Import syntax semantics.
Import ListNotations.
Set Implicit Arguments.

Record monitor_shape {A} (m : machine A) : Prop := {
  monitor_refs_bound : forall x e, get (refs m) x = Some e -> e < next_epoch m;
  monitor_owners_bound : forall e, e < next_epoch m -> owners m e < next_loc m;
  monitor_heap_bound : forall l f t, heap m l f = Some t -> t < next_loc m
}.

Lemma monitor_initial_shape {A} : monitor_shape (@initial_machine A).
Proof.
  constructor; simpl.
  - intros x e H; discriminate.
  - intros e H; lia.
  - intros l f t H; discriminate.
Qed.

Lemma monitor_install_shape {A} (m : machine A) x l n cs :
  monitor_shape m -> next_loc m <= n -> l < n ->
  monitor_shape (install m x l n cs).
Proof.
  intros HS Hn Hl; constructor; cbn [install refs next_epoch owners next_loc heap].
  - intros y e Hy. destruct (Nat.eq_dec y x) as [->|Hne].
    + rewrite get_put_same in Hy. inversion Hy; lia.
    + rewrite get_put_other in Hy by exact Hne.
      pose proof (monitor_refs_bound HS y Hy); lia.
  - intros e He. destruct (Nat.eq_dec e (next_epoch m)) as [->|Hne].
    + now rewrite update_same.
    + rewrite update_other by exact Hne.
      assert (e < next_epoch m) by lia.
      pose proof (monitor_owners_bound HS H); lia.
  - intros q f t Ht. pose proof (monitor_heap_bound HS q f Ht); lia.
Qed.

Lemma monitor_primitive_shape {A} i (m m' : machine A) :
  monitor_shape m -> primitive_step i m m' -> monitor_shape m'.
Proof.
  intros HS HR. destruct HR.
  - unfold allocate. apply monitor_install_shape; auto; lia.
  - unfold bind. apply monitor_install_shape; auto.
    apply (monitor_owners_bound HS). eapply monitor_refs_bound; eauto.
  - unfold bind. apply monitor_install_shape; auto.
    eapply monitor_heap_bound; eauto.
  - constructor; cbn [store refs next_epoch owners next_loc heap].
    + apply (monitor_refs_bound HS).
    + apply (monitor_owners_bound HS).
    + intros q k t Ht. destruct (q =? owners m e) eqn:Eq.
      * unfold update in Ht. destruct (k =? f) eqn:Ek.
        -- inversion Ht; subst t. apply (monitor_owners_bound HS).
           eapply monitor_refs_bound; eauto.
        -- eapply monitor_heap_bound; eauto.
      * eapply monitor_heap_bound; eauto.
  - constructor.
    + exact (monitor_refs_bound HS).
    + exact (monitor_owners_bound HS).
    + exact (monitor_heap_bound HS).
  - constructor; cbn [clear_refs refs next_epoch owners next_loc heap].
    + intros y d Hy; discriminate.
    + apply (monitor_owners_bound HS).
    + apply (monitor_heap_bound HS).
Qed.

Lemma monitor_step_shape {A} (c d : configuration A) :
  monitor_shape (fst c) -> raw_step c d -> monitor_shape (fst d).
Proof.
  intros HS HR; induction HR; simpl in *; auto.
  eapply monitor_primitive_shape; eauto.
Qed.

Lemma monitor_execution_shape {A} (c d : configuration A) :
  monitor_shape (fst c) -> execution c d -> monitor_shape (fst d).
Proof.
  intros HS HE. induction HE; auto.
  apply IHHE. eapply monitor_step_shape; eauto.
Qed.

Theorem monitor_program_prefix_target {A} (s : statement A) m x e :
  program_prefix s initial_machine m -> get (refs m) x = Some e ->
  owners m e < next_loc m.
Proof.
  intros [HF [t HE]] Hr.
  assert (HS : monitor_shape m).
  { exact (@monitor_execution_shape A (initial_machine,instrument s) (m,t) monitor_initial_shape HE). }
  apply (monitor_owners_bound HS). eapply monitor_refs_bound; eauto.
Qed.
