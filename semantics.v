(* Raw operational semantics with a ghost epoch for each binding. Raw calls
   are unguarded: their protocol safety is proved independently of execution.
   runtime_monitor.v layers explicit protocol checks and errors over these
   unchanged steps and proves equivalence for statically accepted programs. *)
From Coq Require Import List Arith Bool.
From Accumulation Require Import syntax trace_languages.
Import ListNotations.
Set Implicit Arguments.

Record machine (A : Type) := {
  next_loc : nat;
  classes : loc -> class;
  next_epoch : nat;
  owners : epoch -> loc;
  refs : fmap epoch;
  heap : loc -> field -> option loc;
  events : list (epoch * A)
}.
Arguments next_loc {A} _.
Arguments classes {A} _ _.
Arguments next_epoch {A} _.
Arguments owners {A} _ _.
Arguments refs {A} _.
Arguments heap {A} _ _ _.
Arguments events {A} _.

Definition initial_machine {A} : machine A :=
  {| next_loc := 0; classes := fun _ => 0; next_epoch := 0;
     owners := fun _ => 0; refs := []; heap := fun _ _ => None; events := [] |}.
Definition object_events {A} (m : machine A) l :=
  filter (fun p => Nat.eqb (owners m (fst p)) l) (events m).
Definition object_history {A} (m : machine A) l := erase_tags (object_events m l).
Definition reference {A} (m : machine A) x :=
  option_map (owners m) (get (refs m) x).
Definition local_history {A} (m : machine A) e := project e (events m).

Definition install {A} (m : machine A) x l n cs : machine A :=
  {| next_loc := n; classes := cs;
     next_epoch := S (next_epoch m); owners := update (owners m) (next_epoch m) l;
     refs := put (refs m) x (Some (next_epoch m)); heap := heap m; events := events m |}.
Definition bind {A} (m : machine A) x l : machine A :=
  install m x l (next_loc m) (classes m).
Definition allocate {A} (m : machine A) x c : machine A :=
  install m x (next_loc m) (S (next_loc m))
    (update (classes m) (next_loc m) c).
Definition emit {A} (m : machine A) e a : machine A :=
  {| next_loc := next_loc m; classes := classes m; next_epoch := next_epoch m;
     owners := owners m; refs := refs m; heap := heap m;
     events := events m ++ [(e,a)] |}.
Definition store {A} (m : machine A) l f target : machine A :=
  {| next_loc := next_loc m; classes := classes m; next_epoch := next_epoch m;
     owners := owners m; refs := refs m;
     heap := fun q => if q =? l then update (heap m l) f (Some target) else heap m q;
     events := events m |}.

(* Bulk exit changes no object, event, owner, or heap field. *)
Definition clear_refs {A} (m : machine A) : machine A :=
  {| next_loc := next_loc m; classes := classes m; next_epoch := next_epoch m;
     owners := owners m; refs := []; heap := heap m; events := events m |}.
Lemma clear_refs_history {A} (m : machine A) l :
  object_history (clear_refs m) l = object_history m l.
Proof. reflexivity. Qed.
Lemma clear_refs_retired {A} (m : machine A) e x :
  get (refs (clear_refs m)) x <> Some e.
Proof. discriminate. Qed.

(* Internal primitive updates have no protocol premises. *)
Inductive primitive_step {A} : statement A -> machine A -> machine A -> Prop :=
| run_new m x c : primitive_step (New x c) m (allocate m x c)
| run_copy m x y e : get (refs m) y = Some e ->
    primitive_step (Copy x y) m (bind m x (owners m e))
| run_load m x y f e l : get (refs m) y = Some e ->
    heap m (owners m e) f = Some l -> primitive_step (Load x y f) m (bind m x l)
| run_store m x f y e d : get (refs m) x = Some e -> get (refs m) y = Some d ->
    primitive_step (Store x f y) m (store m (owners m e) f (owners m d))
| run_call m x a e : get (refs m) x = Some e -> primitive_step (Call x a) m (emit m e a)
| run_finish m : primitive_step Finish m (clear_refs m).
Definition configuration (A : Type) := (machine A * statement A)%type.
Inductive raw_step {A} : configuration A -> configuration A -> Prop :=
| step_primitive m i m' : primitive_step i m m' -> raw_step (m,i) (m',Skip)
| step_seq m s m' s' t : raw_step (m,s) (m',s') ->
    raw_step (m,Seq s t) (m',Seq s' t)
| step_skip m t : raw_step (m,Seq Skip t) (m,t).
Inductive execution {A} : configuration A -> configuration A -> Prop :=
| exec_refl c : execution c c
| exec_step c d e : raw_step c d -> execution d e -> execution c e.

Lemma execution_trans {A} (c d e : configuration A) :
  execution c d -> execution d e -> execution c e.
Proof. intros H; induction H; intros; eauto using execution. Qed.
Lemma raw_step_context {A} (E : context A) m s m' s' :
  raw_step (m,s) (m',s') -> raw_step (m,plug E s) (m',plug E s').
Proof. intros H; induction E; simpl; auto using raw_step. Qed.
Lemma execution_context {A} (E : context A) c d :
  execution c d -> execution (fst c,plug E (snd c)) (fst d,plug E (snd d)).
Proof.
  intros H; induction H; [constructor|]. destruct c as [m s], d as [m' s']; simpl in *.
  eapply exec_step; [apply raw_step_context; exact H|exact IHexecution].
Qed.
Lemma execution_primitive {A} (s : statement A) m m' :
  primitive_step s m m' -> execution (m,s) (m',Skip).
Proof. intros H; eapply exec_step; [eapply step_primitive; exact H|constructor]. Qed.
Lemma execution_seq {A} (s t : statement A) m m' m'' :
  execution (m,s) (m',Skip) -> execution (m',t) (m'',Skip) ->
  execution (m,Seq s t) (m'',Skip).
Proof.
  intros Hs Ht. eapply execution_trans.
  - exact (execution_context (SeqLeft Hole t) Hs).
  - eapply exec_step; [apply step_skip|exact Ht].
Qed.
Lemma skip_terminal {A} (m : machine A) c : ~ raw_step (m,Skip) c.
Proof. intros H; inversion H; subst. match goal with Hp : primitive_step Skip _ _ |- _ => inversion Hp end. Qed.
Lemma execution_skip {A} (m m' : machine A) s :
  execution (m,Skip) (m',s) -> m'=m /\ s=Skip.
Proof. intros H; inversion H; subst; [auto|]. exfalso; eapply skip_terminal; eauto. Qed.

(* Low-level execution takes an already instrumented or residual statement.
   Public program helpers take source programs and insert exactly one exit. *)
Definition program_execution {A} (s : statement A) m m' :=
  finish_free s /\ execution (m,instrument s) (m',Skip).
Definition program_prefix {A} (s : statement A) m m' :=
  finish_free s /\ exists t, execution (m,instrument s) (m',t).
Theorem source_execution_instrument {A} (s : statement A) m m' :
  finish_free s -> execution (m,s) (m',Skip) ->
  program_execution s m (clear_refs m').
Proof.
  intros Hs He; split; auto. apply execution_seq with m'; auto.
  apply execution_primitive; constructor.
Qed.

(* The next redex is primitive, or removes a completed left sequence. *)
Lemma raw_step_decompose {A} (m m' : machine A) s s' : raw_step (m,s) (m',s') ->
  (exists E i, s=plug E i /\ s'=plug E Skip /\ primitive_step i m m') \/
  (exists E t, s=plug E (Seq Skip t) /\ s'=plug E t /\ m'=m).
Proof.
  intros H; remember (m,s) as c eqn:Ec; remember (m',s') as d eqn:Ed.
  revert m s m' s' Ec Ed. induction H; intros u r u' r' Ec Ed; inversion Ec; inversion Ed; subst.
  - left; exists Hole; eexists; repeat split; eauto.
  - destruct (IHraw_step _ _ _ _ eq_refl eq_refl) as [[E [i [Hs [Ht Hp]]]]|[E [v [Hs [Ht Hm]]]]]; subst.
    + left; exists (SeqLeft E t),i; auto.
    + right; exists (SeqLeft E t),v; auto.
  - right; exists Hole; eexists; repeat split; eauto.
Qed.

Lemma execution_seq_inv {A} (c d : configuration A) : execution c d ->
  forall m s t m', c=(m,Seq s t) -> d=(m',Skip) ->
  exists k, execution (m,s) (k,Skip) /\ execution (k,t) (m',Skip).
Proof.
  intros HE; induction HE; intros m s t m' Ec Ed.
  - rewrite Ec in Ed; discriminate.
  - subst c e. inversion H; subst.
    + match goal with Hp : primitive_step (Seq _ _) _ _ |- _ => inversion Hp end.
    + destruct (IHHE _ _ _ _ eq_refl eq_refl) as [k [Hs Ht]].
      exists k; split; auto. eapply exec_step; eauto.
    + exists m; split; [constructor|exact HE].
Qed.
Lemma execution_finish {A} (m m' : machine A) :
  execution (m,Finish) (m',Skip) -> m'=clear_refs m.
Proof.
  intros H; inversion H; subst.
  match goal with Hs : raw_step (m,Finish) _ |- _ => inversion Hs; subst end.
  match goal with Hp : primitive_step Finish _ _ |- _ => inversion Hp; subst end.
  match goal with He : execution (_,Skip) (_,Skip) |- _ => exact (proj1 (execution_skip He)) end.
Qed.
Theorem source_execution_iff {A} (s : statement A) m m' :
  program_execution s m m' <-> finish_free s /\
    exists k, execution (m,s) (k,Skip) /\ m'=clear_refs k.
Proof.
  split.
  - intros [HF HE]; split; auto. destruct (execution_seq_inv HE eq_refl eq_refl) as [k [Hs Hf]].
    exists k; split; auto. now apply execution_finish.
  - intros [HF [k [Hs ->]]]. now apply source_execution_instrument.
Qed.
Lemma source_step_finish_free {A} (m m' : machine A) s s' :
  raw_step (m,s) (m',s') -> finish_free s -> finish_free s'.
Proof.
  intros H; remember (m,s) as c eqn:Ec; remember (m',s') as d eqn:Ed.
  revert m s m' s' Ec Ed. induction H; intros u r u' r' Ec Ed HF;
    inversion Ec; inversion Ed; subst; try reflexivity.
  - unfold finish_free in *; simpl in *. apply andb_true_iff in HF.
    apply andb_true_iff; split; [eapply IHraw_step; eauto; tauto|tauto].
  - exact HF.
Qed.
Theorem source_execution_no_early_exit {A} (c d : configuration A) :
  execution c d -> finish_free (snd c) -> finish_free (snd d).
Proof.
  intros H; induction H; auto. intros HF; apply IHexecution.
  destruct c,d; simpl in *; eapply source_step_finish_free; eauto.
Qed.

Lemma clear_refs_events {A} (m : machine A) : events (clear_refs m)=events m.
Proof. reflexivity. Qed.
Lemma execution_snoc {A} (c d e : configuration A) :
  execution c d -> raw_step d e -> execution c e.
Proof. intros H S; eapply execution_trans; [exact H|eapply exec_step; [exact S|constructor]]. Qed.
Theorem raw_step_iff_context {A} (m m' : machine A) s s' : raw_step (m,s) (m',s') <->
  (exists E i, s=plug E i /\ s'=plug E Skip /\ primitive_step i m m') \/
  (exists E t, s=plug E (Seq Skip t) /\ s'=plug E t /\ m'=m).
Proof.
  split; [apply raw_step_decompose|].
  intros [[E [i [-> [-> H]]]]|[E [t [-> [-> ->]]]]];
    apply raw_step_context; [now apply step_primitive|apply step_skip].
Qed.
