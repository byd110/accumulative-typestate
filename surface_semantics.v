(* Ghost erasure to the paper's four maps.  Locations in the paper are arbitrary
   fresh naturals; only the finite allocated part of a renaming is injective.
   Equality below is extensional and includes all allocated histories, whether
   or not the objects are reachable from variables or fields. *)
From Coq Require Import List Arith Bool Lia.
From Accumulation Require Import syntax trace_languages semantics.
Import ListNotations.
Set Implicit Arguments.

Record surface (A : Type) := {
  surface_refs : var -> option loc;
  surface_heap : loc -> field -> option loc;
  surface_classes : loc -> option class;
  surface_history : loc -> list A
}.
Arguments surface_refs {A} _ _.
Arguments surface_heap {A} _ _ _.
Arguments surface_classes {A} _ _.
Arguments surface_history {A} _ _.

Definition initial_surface {A} : surface A :=
  {| surface_refs := fun _ => None; surface_heap := fun _ _ => None;
     surface_classes := fun _ => None; surface_history := fun _ => [] |}.
Definition surface_bind {A} (M : surface A) x l :=
  {| surface_refs := update (surface_refs M) x (Some l);
     surface_heap := surface_heap M; surface_classes := surface_classes M;
     surface_history := surface_history M |}.
Definition surface_allocate {A} (M : surface A) x c l :=
  {| surface_refs := update (surface_refs M) x (Some l);
     surface_heap := surface_heap M;
     surface_classes := update (surface_classes M) l (Some c);
     surface_history := update (surface_history M) l [] |}.
Definition surface_store {A} (M : surface A) l f t :=
  {| surface_refs := surface_refs M;
     surface_heap := update (surface_heap M) l
       (update (surface_heap M l) f (Some t));
     surface_classes := surface_classes M; surface_history := surface_history M |}.
Definition surface_emit {A} (M : surface A) l a :=
  {| surface_refs := surface_refs M; surface_heap := surface_heap M;
     surface_classes := surface_classes M;
     surface_history := update (surface_history M) l (surface_history M l ++ [a]) |}.
Definition surface_clear {A} (M : surface A) :=
  {| surface_refs := fun _ => None; surface_heap := surface_heap M;
     surface_classes := surface_classes M; surface_history := surface_history M |}.

(* The surface rules contain no epoch, event log, or ghost-step premise. *)
Inductive surface_primitive {A} : statement A -> surface A -> surface A -> Prop :=
| surface_new M x c l : surface_classes M l = None ->
    surface_primitive (New x c) M (surface_allocate M x c l)
| surface_copy M x y l : surface_refs M y = Some l ->
    surface_primitive (Copy x y) M (surface_bind M x l)
| surface_load M x y f l t : surface_refs M y = Some l ->
    surface_heap M l f = Some t ->
    surface_primitive (Load x y f) M (surface_bind M x t)
| surface_write M x f y l t : surface_refs M x = Some l ->
    surface_refs M y = Some t ->
    surface_primitive (Store x f y) M (surface_store M l f t)
| surface_call M x a l : surface_refs M x = Some l ->
    surface_primitive (Call x a) M (surface_emit M l a)
| surface_finish M : surface_primitive Finish M (surface_clear M).

Definition surface_configuration (A : Type) := (surface A * statement A)%type.
Inductive surface_step {A} : surface_configuration A -> surface_configuration A -> Prop :=
| surface_step_primitive M M' s : surface_primitive s M M' ->
    surface_step (M,s) (M',Skip)
| surface_step_seq M M' s s' t : surface_step (M,s) (M',s') ->
    surface_step (M,Seq s t) (M',Seq s' t)
| surface_step_skip M s : surface_step (M,Seq Skip s) (M,s).
Inductive surface_execution {A} : surface_configuration A -> surface_configuration A -> Prop :=
| surface_exec_refl c : surface_execution c c
| surface_exec_step c d e : surface_step c d -> surface_execution d e ->
    surface_execution c e.

(* Structural validity is independent of all protocol assumptions. *)
Record ghost_well_formed {A} (m : machine A) : Prop := {
  ghost_refs : forall x e, get (refs m) x = Some e -> e < next_epoch m;
  ghost_owners : forall e, e < next_epoch m -> owners m e < next_loc m;
  ghost_events : forall e a, In (e,a) (events m) -> e < next_epoch m;
  ghost_heap : forall l f t, heap m l f = Some t ->
    l < next_loc m /\ t < next_loc m
}.

Record represents {A} (r : loc -> loc) (m : machine A) (M : surface A) : Prop := {
  represents_injective : forall l t, l < next_loc m -> t < next_loc m ->
    r l = r t -> l = t;
  represents_classes : forall l, l < next_loc m ->
    surface_classes M (r l) = Some (classes m l);
  represents_domain : forall L c, surface_classes M L = Some c ->
    exists l, l < next_loc m /\ r l = L;
  represents_refs : forall x,
    surface_refs M x = option_map r (reference m x);
  represents_heap : forall l f, l < next_loc m ->
    surface_heap M (r l) f = option_map r (heap m l f);
  represents_heap_domain : forall L f T, surface_heap M L f = Some T ->
    exists l, l < next_loc m /\ r l = L;
  represents_histories : forall l, l < next_loc m ->
    surface_history M (r l) = object_history m l
}.

Definition extends_on (n : nat) (r r' : loc -> loc) :=
  forall l, l < n -> r' l = r l.

Lemma ghost_initial {A} : ghost_well_formed (@initial_machine A).
Proof. constructor; simpl; intros; try discriminate; try contradiction; lia. Qed.
Lemma represents_initial {A} r : represents r (@initial_machine A) initial_surface.
Proof. constructor; simpl; intros; try discriminate; try lia; reflexivity. Qed.

Lemma ghost_install {A} (m : machine A) x l n cs :
  ghost_well_formed m -> next_loc m <= n -> l < n ->
  ghost_well_formed (install m x l n cs).
Proof.
  intros H Hn Hl; constructor; cbn [install refs owners events heap next_epoch next_loc].
  - intros y e Hy; destruct (Nat.eq_dec y x) as [->|Hne].
    + rewrite get_put_same in Hy; inversion Hy; lia.
    + rewrite get_put_other in Hy by exact Hne.
      pose proof (ghost_refs H y Hy); lia.
  - intros e He; destruct (Nat.eq_dec e (next_epoch m)) as [->|Hne].
    + now rewrite update_same.
    + rewrite update_other by exact Hne.
      pose proof (ghost_owners H (e:=e) ltac:(lia)); lia.
  - intros e a He; pose proof (ghost_events H e a He); lia.
  - intros q f t Ht; destruct (ghost_heap H q f Ht); lia.
Qed.

Lemma ghost_install_history {A} (m : machine A) x l n cs q :
  ghost_well_formed m ->
  object_history (install m x l n cs) q = object_history m q.
Proof.
  intros H; unfold object_history, object_events; cbn [install owners events].
  f_equal. apply filter_ext_in. intros [e a] Hin; simpl.
  rewrite update_other; [reflexivity|]. pose proof (ghost_events H e a Hin); lia.
Qed.

Lemma filter_none {T} (p : T -> bool) ls :
  (forall x, In x ls -> p x = false) -> filter p ls = [].
Proof.
  induction ls as [|x ls IH]; simpl; auto. intros H.
  rewrite H by now left. apply IH; intros y Hy; apply H; now right.
Qed.

Lemma ghost_fresh_history {A} (m : machine A) : ghost_well_formed m ->
  object_history m (next_loc m) = [].
Proof.
  intros H; unfold object_history, object_events.
  assert (E : filter (fun p : epoch * A => owners m (fst p) =? next_loc m)
    (events m) = []).
  { apply filter_none. intros [e a] Hin; simpl. apply Nat.eqb_neq.
    pose proof (ghost_events H e a Hin) as He.
    pose proof (ghost_owners H He); lia. }
  now rewrite E.
Qed.

Lemma ghost_reference_install {A} (m : machine A) x l n cs y :
  ghost_well_formed m ->
  reference (install m x l n cs) y = update (reference m) x (Some l) y.
Proof.
  intros H; unfold reference; cbn [install refs owners].
  destruct (Nat.eq_dec y x) as [->|Hne].
  - rewrite get_put_same, update_same; simpl; now rewrite update_same.
  - rewrite get_put_other, update_other by exact Hne.
    destruct (get (refs m) y) as [e|] eqn:E; simpl; auto.
    rewrite update_other; auto. pose proof (ghost_refs H y E); lia.
Qed.

Lemma ghost_history_emit {A} (m : machine A) e a l :
  object_history (emit m e a) l =
    if owners m e =? l then object_history m l ++ [a] else object_history m l.
Proof.
  unfold object_history, object_events; cbn [emit owners events].
  rewrite filter_app; simpl. destruct (owners m e =? l); simpl.
  - unfold erase_tags; now rewrite map_app.
  - now rewrite app_nil_r.
Qed.

Lemma represents_reference {A} r (m : machine A) M x L :
  represents r m M -> surface_refs M x = Some L ->
  exists e, get (refs m) x = Some e /\ r (owners m e) = L.
Proof.
  intros H E; rewrite (represents_refs H x) in E.
  unfold reference in E. destruct (get (refs m) x) as [e|] eqn:F;
    simpl in E; try discriminate. inversion E; subst; eauto.
Qed.

Lemma represents_fresh {A} r (m : machine A) M L :
  represents r m M -> surface_classes M L = None ->
  forall l, l < next_loc m -> r l <> L.
Proof.
  intros H E l Hl Eq. rewrite <- Eq, (represents_classes H Hl) in E; discriminate.
Qed.

Definition fresh_location r n := S (fold_right Nat.max 0 (map r (seq 0 n))).
Lemma fresh_location_bound r n l : l < n -> r l < fresh_location r n.
Proof.
  intros Hl; unfold fresh_location.
  assert (Hin : In (r l) (map r (seq 0 n))).
  { apply in_map. apply in_seq; lia. }
  generalize dependent (map r (seq 0 n)). intros ls Hin.
  induction ls as [|a ls IH]; simpl in *; [contradiction|].
  destruct Hin as [<-|Hin]; [lia|specialize (IH Hin); lia].
Qed.
Lemma represents_exists_fresh {A} r (m : machine A) M : represents r m M ->
  surface_classes M (fresh_location r (next_loc m)) = None.
Proof.
  intros H; destruct (surface_classes M (fresh_location r (next_loc m)))
    as [c|] eqn:E; auto.
  destruct (represents_domain H _ E) as [l [Hl Er]].
  pose proof (fresh_location_bound r Hl); lia.
Qed.

Lemma rename_reference {A} (m : machine A) r r' x : ghost_well_formed m ->
  extends_on (next_loc m) r r' ->
  option_map r' (reference m x) = option_map r (reference m x).
Proof.
  intros H E; unfold reference.
  destruct (get (refs m) x) as [e|] eqn:F; simpl; auto.
  rewrite E; auto. apply (ghost_owners H). eapply ghost_refs; eauto.
Qed.

Lemma rename_heap {A} (m : machine A) r r' l f : ghost_well_formed m ->
  extends_on (next_loc m) r r' ->
  option_map r' (heap m l f) = option_map r (heap m l f).
Proof.
  intros H E; destruct (heap m l f) as [t|] eqn:F; simpl; auto.
  rewrite E; auto. now destruct (ghost_heap H l f F).
Qed.

Lemma extend_old r n L : extends_on n r (update r n L).
Proof. intros l Hl; apply update_other; lia. Qed.

Lemma represents_bind {A} r (m : machine A) M x l :
  ghost_well_formed m -> represents r m M -> l < next_loc m ->
  represents r (bind m x l) (surface_bind M x (r l)).
Proof.
  intros H R Hl; constructor; cbn [bind install next_loc classes heap
    surface_bind surface_refs surface_classes surface_heap surface_history].
  - apply (represents_injective R).
  - apply (represents_classes R).
  - apply (represents_domain R).
  - intros y; unfold bind; rewrite ghost_reference_install by exact H.
    destruct (Nat.eq_dec y x) as [->|Hne].
    + now rewrite !update_same.
    + rewrite !update_other by exact Hne. apply (represents_refs R).
  - apply (represents_heap R).
  - apply (represents_heap_domain R).
  - intros q Hq; unfold bind; rewrite ghost_install_history by exact H.
    apply (represents_histories R Hq).
Qed.

Lemma represents_allocate {A} r (m : machine A) M x c L :
  ghost_well_formed m -> represents r m M -> surface_classes M L = None ->
  represents (update r (next_loc m) L) (allocate m x c)
    (surface_allocate M x c L).
Proof.
  intros H R Fresh.
  pose proof (represents_fresh R Fresh) as F.
  pose proof (@extend_old r (next_loc m) L) as Ext.
  constructor; cbn [allocate install next_loc classes heap surface_allocate
    surface_refs surface_classes surface_heap surface_history].
  - intros l t Hl Ht E.
    destruct (Nat.eq_dec l (next_loc m)) as [->|Hlne];
      destruct (Nat.eq_dec t (next_loc m)) as [->|Htne]; auto.
    + rewrite update_same, update_other in E by exact Htne.
      exfalso; apply (F t ltac:(lia)); symmetry; exact E.
    + rewrite update_other, update_same in E by exact Hlne.
      exfalso; apply (F l ltac:(lia)); exact E.
    + rewrite !update_other in E by assumption.
      eapply represents_injective; eauto; lia.
  - intros l Hl; destruct (Nat.eq_dec l (next_loc m)) as [->|Hne].
    + now rewrite !update_same.
    + rewrite (Ext l ltac:(lia)).
      rewrite update_other by (apply F; lia).
      try rewrite update_other by exact Hne.
      apply (represents_classes R); lia.
  - intros T d E; destruct (Nat.eq_dec T L) as [->|Hne].
    + exists (next_loc m); split; [lia|apply update_same].
    + rewrite update_other in E by exact Hne.
      destruct (represents_domain R _ E) as [l [Hl Er]].
      exists l; split; [lia|rewrite Ext by exact Hl; exact Er].
  - intros y; unfold allocate; rewrite ghost_reference_install by exact H.
    destruct (Nat.eq_dec y x) as [->|Hne].
    + rewrite !update_same; simpl; now rewrite update_same.
    + rewrite !update_other by exact Hne.
      rewrite (@rename_reference A m r (update r (next_loc m) L) y H Ext). apply (represents_refs R).
  - intros l f Hl; destruct (Nat.eq_dec l (next_loc m)) as [->|Hne].
    + rewrite update_same.
      assert (GH : heap m (next_loc m) f = None).
      { destruct (heap m (next_loc m) f) as [t|] eqn:E; auto.
        destruct (ghost_heap H _ f E); lia. }
      assert (SH : surface_heap M L f = None).
      { destruct (surface_heap M L f) as [T|] eqn:E; auto.
        destruct (represents_heap_domain R _ f E) as [q [Hq Eq]].
        exfalso; apply (F q Hq); exact Eq. }
      now rewrite GH, SH.
    + rewrite update_other by exact Hne.
      rewrite (@rename_heap A m r (update r (next_loc m) L) l f H Ext). apply (represents_heap R); lia.
  - intros T f U E; destruct (represents_heap_domain R _ f E) as [l [Hl El]].
    exists l; split; [lia|rewrite Ext by exact Hl; exact El].
  - intros l Hl; unfold allocate; rewrite ghost_install_history by exact H.
    destruct (Nat.eq_dec l (next_loc m)) as [->|Hne].
    + rewrite !update_same. symmetry; now apply ghost_fresh_history.
    + rewrite (Ext l ltac:(lia)).
      rewrite update_other by (apply F; lia).
      try rewrite update_other by exact Hne.
      apply (represents_histories R); lia.
Qed.

Lemma represents_store {A} r (m : machine A) M l f t :
  ghost_well_formed m -> represents r m M -> l < next_loc m -> t < next_loc m ->
  represents r (store m l f t) (surface_store M (r l) f (r t)).
Proof.
  intros H R Hl Ht; constructor; cbn [store next_loc classes heap
    surface_store surface_refs surface_classes surface_heap surface_history].
  - apply (represents_injective R).
  - apply (represents_classes R).
  - apply (represents_domain R).
  - apply (represents_refs R).
  - intros q k Hq; destruct (Nat.eq_dec q l) as [->|Hne].
    + rewrite update_same, Nat.eqb_refl.
      destruct (Nat.eq_dec k f) as [->|Hkf].
      * now rewrite !update_same.
      * rewrite !update_other by exact Hkf. apply (represents_heap R k Hl).
    + assert (Rne : r q <> r l).
      { intros E; apply Hne; eapply represents_injective; eauto. }
      rewrite update_other by exact Rne.
      assert (Qne : (q =? l) = false) by (apply Nat.eqb_neq; exact Hne).
      rewrite Qne. apply (represents_heap R k Hq).
  - intros T k U E; destruct (Nat.eq_dec T (r l)) as [->|Hne].
    + exists l; auto.
    + rewrite update_other in E by exact Hne.
      eapply represents_heap_domain; eauto.
  - apply (represents_histories R).
Qed.

Lemma represents_emit {A} r (m : machine A) M e a :
  ghost_well_formed m -> represents r m M -> e < next_epoch m ->
  represents r (emit m e a) (surface_emit M (r (owners m e)) a).
Proof.
  intros H R He; pose proof (ghost_owners H He) as Hl.
  constructor; cbn [emit next_loc classes heap
    surface_emit surface_refs surface_classes surface_heap surface_history].
  - apply (represents_injective R).
  - apply (represents_classes R).
  - apply (represents_domain R).
  - apply (represents_refs R).
  - apply (represents_heap R).
  - apply (represents_heap_domain R).
  - intros q Hq; rewrite ghost_history_emit.
    destruct (Nat.eq_dec q (owners m e)) as [->|Hne].
    + rewrite update_same, Nat.eqb_refl, (represents_histories R Hl); reflexivity.
    + assert (Rne : r q <> r (owners m e)).
      { intros E; apply Hne; eapply represents_injective; eauto. }
      rewrite update_other by exact Rne.
      assert (Qne : (owners m e =? q) = false) by (apply Nat.eqb_neq; lia).
      rewrite Qne. apply (represents_histories R Hq).
Qed.

Lemma represents_clear {A} r (m : machine A) M : represents r m M ->
  represents r (clear_refs m) (surface_clear M).
Proof.
  intros R; constructor; cbn [clear_refs next_loc classes heap
    surface_clear surface_refs surface_classes surface_heap surface_history].
  - apply (represents_injective R).
  - apply (represents_classes R).
  - apply (represents_domain R).
  - reflexivity.
  - apply (represents_heap R).
  - apply (represents_heap_domain R).
  - apply (represents_histories R).
Qed.

Lemma represents_get {A} r (m : machine A) M x e : represents r m M ->
  get (refs m) x = Some e -> surface_refs M x = Some (r (owners m e)).
Proof.
  intros R E; rewrite (represents_refs R x); unfold reference; now rewrite E.
Qed.

Lemma ghost_primitive {A} i (m m' : machine A) :
  ghost_well_formed m -> primitive_step i m m' -> ghost_well_formed m'.
Proof.
  intros H S; destruct S.
  - unfold allocate; apply ghost_install; auto; lia.
  - unfold bind; apply ghost_install; auto.
    apply (ghost_owners H); eapply ghost_refs; eauto.
  - unfold bind; apply ghost_install; auto.
    now destruct (ghost_heap H _ f H1).
  - constructor; cbn [store refs owners events heap next_loc next_epoch].
    + apply (ghost_refs H).
    + apply (ghost_owners H).
    + apply (ghost_events H).
    + intros q k t E; destruct (q =? owners m e) eqn:Eq.
      * apply Nat.eqb_eq in Eq; subst q.
        unfold update in E; destruct (k =? f).
        -- inversion E; subst t; split; apply (ghost_owners H);
             eapply ghost_refs; eauto.
        -- eapply ghost_heap; eauto.
      * eapply ghost_heap; eauto.
  - constructor; cbn [emit refs owners events heap next_loc next_epoch].
    + apply (ghost_refs H).
    + apply (ghost_owners H).
    + intros d b Hin; apply in_app_or in Hin; destruct Hin as [Hin|[E|[]]].
      * eapply ghost_events; eauto.
      * inversion E; subst; eapply ghost_refs; eauto.
    + apply (ghost_heap H).
  - constructor; cbn [clear_refs refs owners events heap next_loc next_epoch].
    + intros; discriminate.
    + apply (ghost_owners H).
    + apply (ghost_events H).
    + apply (ghost_heap H).
Qed.

Lemma primitive_locations_monotone {A} i (m m' : machine A) :
  primitive_step i m m' -> next_loc m <= next_loc m'.
Proof. intros H; destruct H; simpl; lia. Qed.

Theorem ghost_surface_primitive {A} r i (m m' : machine A) M :
  ghost_well_formed m -> represents r m M -> primitive_step i m m' ->
  exists r' M', extends_on (next_loc m) r r' /\
    surface_primitive i M M' /\ represents r' m' M'.
Proof.
  intros H R S; destruct S.
  - pose (L := fresh_location r (next_loc m)).
    assert (Fresh : surface_classes M L = None) by now apply represents_exists_fresh.
    exists (update r (next_loc m) L), (surface_allocate M x c L).
    split; [apply extend_old|]. split; [now constructor|].
    now apply represents_allocate.
  - exists r, (surface_bind M x (r (owners m e))).
    split; [intros q Hq; reflexivity|]. split.
    + constructor; eapply represents_get; eauto.
    + apply represents_bind; auto. apply (ghost_owners H); eapply ghost_refs; eauto.
  - exists r, (surface_bind M x (r l)).
    split; [intros q Hq; reflexivity|]. split.
    + eapply surface_load; [eapply represents_get; eauto|].
      rewrite (represents_heap R f); [now rewrite H1|].
      apply (ghost_owners H); eapply ghost_refs; eauto.
    + apply represents_bind; auto. now destruct (ghost_heap H _ f H1).
  - exists r, (surface_store M (r (owners m e)) f (r (owners m d))).
    split; [intros q Hq; reflexivity|]. split.
    + constructor; eapply represents_get; eauto.
    + apply represents_store; auto; apply (ghost_owners H); eapply ghost_refs; eauto.
  - exists r, (surface_emit M (r (owners m e)) a).
    split; [intros q Hq; reflexivity|]. split.
    + constructor; eapply represents_get; eauto.
    + apply represents_emit; auto; eapply ghost_refs; eauto.
  - exists r, (surface_clear M).
    split; [intros q Hq; reflexivity|]. split; [constructor|now apply represents_clear].
Qed.

(* This converse covers every fresh location permitted by the paper.  The
   extended map agrees with the old map on all previously allocated objects. *)
Theorem surface_ghost_primitive {A} r i (m : machine A) M M' :
  ghost_well_formed m -> represents r m M -> surface_primitive i M M' ->
  exists r' m', extends_on (next_loc m) r r' /\
    primitive_step i m m' /\ represents r' m' M'.
Proof.
  intros H R S; destruct S.
  - exists (update r (next_loc m) l), (allocate m x c).
    split; [apply extend_old|]. split; [constructor|now apply represents_allocate].
  - destruct (represents_reference y R H0) as [e [He <-]].
    exists r, (bind m x (owners m e)).
    split; [intros q Hq; reflexivity|]. split; [now constructor|].
    apply represents_bind; auto. apply (ghost_owners H); eapply ghost_refs; eauto.
  - destruct (represents_reference y R H0) as [e [He <-]].
    assert (Hl : owners m e < next_loc m).
    { apply (ghost_owners H); eapply ghost_refs; eauto. }
    rewrite (represents_heap R f Hl) in H1.
    destruct (heap m (owners m e) f) as [q|] eqn:Eq; simpl in H1; try discriminate.
    inversion H1; subst t. exists r, (bind m x q).
    split; [intros k Hk; reflexivity|]. split; [econstructor; eauto|].
    apply represents_bind; auto. now destruct (ghost_heap H _ f Eq).
  - destruct (represents_reference x R H0) as [e [He <-]].
    destruct (represents_reference y R H1) as [d [Hd <-]].
    exists r, (store m (owners m e) f (owners m d)).
    split; [intros q Hq; reflexivity|]. split; [econstructor; eauto|].
    apply represents_store; auto; apply (ghost_owners H); eapply ghost_refs; eauto.
  - destruct (represents_reference x R H0) as [e [He <-]].
    exists r, (emit m e a).
    split; [intros q Hq; reflexivity|]. split; [econstructor; eauto|].
    apply represents_emit; auto; eapply ghost_refs; eauto.
  - exists r, (clear_refs m).
    split; [intros q Hq; reflexivity|]. split; [constructor|now apply represents_clear].
Qed.

Lemma surface_step_context {A} (E : context A) M s M' s' :
  surface_step (M,s) (M',s') ->
  surface_step (M,plug E s) (M',plug E s').
Proof. intros H; induction E; simpl; auto using surface_step. Qed.

Lemma surface_execution_context {A} (E : context A) c d :
  surface_execution c d ->
  surface_execution (fst c,plug E (snd c)) (fst d,plug E (snd d)).
Proof.
  intros H; induction H; [constructor|].
  destruct c as [M s], d as [M' s']; simpl in *.
  eapply surface_exec_step; [apply surface_step_context; exact H|exact IHsurface_execution].
Qed.

Lemma surface_step_decompose {A} (M M' : surface A) s s' : surface_step (M,s) (M',s') ->
  (exists E i, s=plug E i /\ s'=plug E Skip /\ surface_primitive i M M') \/
  (exists E t, s=plug E (Seq Skip t) /\ s'=plug E t /\ M'=M).
Proof.
  intros H; remember (M,s) as c eqn:Ec; remember (M',s') as d eqn:Ed.
  revert M s M' s' Ec Ed. induction H; intros u r u' r' Ec Ed;
    inversion Ec; inversion Ed; subst.
  - left; exists Hole; eexists; repeat split; eauto.
  - destruct (IHsurface_step _ _ _ _ eq_refl eq_refl)
      as [[E [i [Hs [Ht Hp]]]]|[E [v [Hs [Ht Hm]]]]]; subst.
    + left; exists (SeqLeft E t),i; auto.
    + right; exists (SeqLeft E t),v; auto.
  - right; exists Hole; eexists; repeat split; eauto.
Qed.

Lemma ghost_raw_step {A} (c d : configuration A) :
  raw_step c d -> ghost_well_formed (fst c) -> ghost_well_formed (fst d).
Proof.
  intros S; induction S; simpl; intros WF; auto.
  eapply ghost_primitive; eauto.
Qed.

Lemma ghost_execution {A} (c d : configuration A) :
  execution c d -> ghost_well_formed (fst c) -> ghost_well_formed (fst d).
Proof.
  intros E; induction E; auto. intros WF; apply IHE; eapply ghost_raw_step; eauto.
Qed.

Lemma surface_execution_trans {A} (c d e : surface_configuration A) :
  surface_execution c d -> surface_execution d e -> surface_execution c e.
Proof. intros H; induction H; intros; eauto using surface_execution. Qed.

Lemma step_locations_monotone {A} (c d : configuration A) :
  raw_step c d -> next_loc (fst c) <= next_loc (fst d).
Proof.
  intros S; induction S; simpl in *; auto.
  eapply primitive_locations_monotone; eauto.
Qed.

Theorem ghost_surface_step {A} r (m m' : machine A) M s s' :
  ghost_well_formed m -> represents r m M -> raw_step (m,s) (m',s') ->
  exists r' M', extends_on (next_loc m) r r' /\
    surface_step (M,s) (M',s') /\ represents r' m' M'.
Proof.
  intros H R S; destruct (raw_step_decompose S)
    as [[E [i [-> [-> P]]]]|[E [t [-> [-> ->]]]]].
  - destruct (ghost_surface_primitive H R P) as [r' [M' [Ext [Sp Rp]]]].
    exists r', M'; split; auto. split; auto.
    apply surface_step_context; now constructor.
  - exists r, M; split; [intros l Hl; reflexivity|]. split; auto.
    apply surface_step_context; constructor.
Qed.

Theorem surface_ghost_step {A} r (m : machine A) M M' s s' :
  ghost_well_formed m -> represents r m M -> surface_step (M,s) (M',s') ->
  exists r' m', extends_on (next_loc m) r r' /\
    raw_step (m,s) (m',s') /\ represents r' m' M'.
Proof.
  intros H R S; destruct (surface_step_decompose S)
    as [[E [i [-> [-> P]]]]|[E [t [-> [-> ->]]]]].
  - destruct (surface_ghost_primitive H R P) as [r' [m' [Ext [Sp Rp]]]].
    exists r', m'; split; auto. split; auto.
    apply raw_step_context; now constructor.
  - exists r, m; split; [intros l Hl; reflexivity|]. split; auto.
    apply raw_step_context; constructor.
Qed.

Theorem ghost_surface_execution {A} (c d : configuration A) r M :
  ghost_well_formed (fst c) -> represents r (fst c) M -> execution c d ->
  exists r' M', extends_on (next_loc (fst c)) r r' /\
    surface_execution (M,snd c) (M',snd d) /\ represents r' (fst d) M'.
Proof.
  intros H R E; revert r M H R.
  induction E as [c|c d e S E IH]; intros r M H R.
  - exists r, M; split; [intros l Hl; reflexivity|]; split; auto; constructor.
  - destruct c as [m s], d as [md sd], e as [me se]; simpl in *.
    destruct (ghost_surface_step H R S) as [rd [Md [Ext [Sd Rd]]]].
    destruct (IH rd Md (ghost_raw_step S H) Rd) as [re [Me [Exte [Se Re]]]].
    exists re, Me; split.
    + intros l Hl; rewrite Exte; [apply Ext; exact Hl|].
      pose proof (step_locations_monotone S); simpl in *; lia.
    + split; auto; eapply surface_exec_step; eauto.
Qed.

Theorem surface_ghost_execution {A} (c d : surface_configuration A) r m :
  ghost_well_formed m -> represents r m (fst c) -> surface_execution c d ->
  exists r' m', extends_on (next_loc m) r r' /\
    execution (m,snd c) (m',snd d) /\ represents r' m' (fst d).
Proof.
  intros H R E; revert r m H R.
  induction E as [c|c d e S E IH]; intros r m H R.
  - exists r, m; split; [intros l Hl; reflexivity|]; split; auto; constructor.
  - destruct c as [M s], d as [Md sd], e as [Me se]; simpl in *.
    destruct (surface_ghost_step H R S) as [rd [md [Ext [Sd Rd]]]].
    destruct (IH rd md (ghost_raw_step Sd H) Rd) as [re [me [Exte [Se Re]]]].
    exists re, me; split.
    + intros l Hl; rewrite Exte; [apply Ext; exact Hl|].
      pose proof (step_locations_monotone Sd); simpl in *; lia.
    + split; auto; eapply exec_step; eauto.
Qed.

Definition surface_program_execution {A} (s : statement A) M M' :=
  finish_free s /\ surface_execution (M,instrument s) (M',Skip).
Definition surface_program_prefix {A} (s : statement A) M M' :=
  finish_free s /\ exists t, surface_execution (M,instrument s) (M',t).

Theorem ghost_surface_program {A} r (s : statement A) m m' M :
  ghost_well_formed m -> represents r m M -> program_execution s m m' ->
  exists r' M', extends_on (next_loc m) r r' /\
    surface_program_execution s M M' /\ represents r' m' M'.
Proof.
  intros H R [F E]. destruct (@ghost_surface_execution A (m,instrument s) (m',Skip) r M H R E)
    as [r' [M' [Ext [E' R']]]]. exists r',M'; split; [exact Ext|]; split; [split; assumption|exact R'].
Qed.

Theorem surface_ghost_program {A} r (s : statement A) m M M' :
  ghost_well_formed m -> represents r m M -> surface_program_execution s M M' ->
  exists r' m', extends_on (next_loc m) r r' /\
    program_execution s m m' /\ represents r' m' M'.
Proof.
  intros H R [F E]. destruct (@surface_ghost_execution A (M,instrument s) (M',Skip) r m H R E)
    as [r' [m' [Ext [E' R']]]]. exists r',m'; split; [exact Ext|]; split; [split; assumption|exact R'].
Qed.

Theorem ghost_surface_prefix {A} r (s : statement A) m m' M :
  ghost_well_formed m -> represents r m M -> program_prefix s m m' ->
  exists r' M', extends_on (next_loc m) r r' /\
    surface_program_prefix s M M' /\ represents r' m' M'.
Proof.
  intros H R [F [t E]]. destruct (@ghost_surface_execution A (m,instrument s) (m',t) r M H R E)
    as [r' [M' [Ext [E' R']]]]. exists r',M'; split; auto; split; auto.
  split; auto; now exists t.
Qed.

Theorem surface_ghost_prefix {A} r (s : statement A) m M M' :
  ghost_well_formed m -> represents r m M -> surface_program_prefix s M M' ->
  exists r' m', extends_on (next_loc m) r r' /\
    program_prefix s m m' /\ represents r' m' M'.
Proof.
  intros H R [F [t E]]. destruct (@surface_ghost_execution A (M,instrument s) (M',t) r m H R E)
    as [r' [m' [Ext [E' R']]]]. exists r',m'; split; auto; split; auto.
  split; auto; now exists t.
Qed.

(* Partial maps are compared by lookup, not by a list representation, and
   unallocated histories are deliberately unobservable. *)
Definition surface_observationally_equal {A} (M N : surface A) : Prop :=
  (forall x, surface_refs M x = surface_refs N x) /\
  (forall l f, surface_heap M l f = surface_heap N l f) /\
  (forall l, surface_classes M l = surface_classes N l) /\
  (forall l c, surface_classes M l = Some c ->
    surface_history M l = surface_history N l).

Theorem represents_extensional {A} r (m : machine A) M N :
  represents r m M -> represents r m N -> surface_observationally_equal M N.
Proof.
  intros R S; split.
  - intros x; now rewrite (represents_refs R x), (represents_refs S x).
  - split.
    + intros L f; destruct (surface_heap M L f) as [T|] eqn:E.
      * destruct (represents_heap_domain R L f E) as [l [Hl <-]].
        rewrite (represents_heap R f Hl) in E.
        rewrite (represents_heap S f Hl); symmetry; exact E.
      * destruct (surface_heap N L f) as [T|] eqn:F; auto.
        destruct (represents_heap_domain S L f F) as [l [Hl <-]].
        rewrite (represents_heap R f Hl) in E.
        rewrite (represents_heap S f Hl) in F; congruence.
    + split.
      * intros L; destruct (surface_classes M L) as [c|] eqn:E.
        -- destruct (represents_domain R L E) as [l [Hl <-]].
           rewrite (represents_classes R Hl) in E.
           rewrite (represents_classes S Hl); symmetry; exact E.
        -- destruct (surface_classes N L) as [c|] eqn:F; auto.
           destruct (represents_domain S L F) as [l [Hl <-]].
           rewrite (represents_classes R Hl) in E; discriminate.
      * intros L c E; destruct (represents_domain R L E) as [l [Hl <-]].
        now rewrite (represents_histories R Hl), (represents_histories S Hl).
Qed.

Theorem represented_classes_finite {A} r (m : machine A) M : represents r m M ->
  exists entries : list (loc * class), forall L c,
    surface_classes M L = Some c <-> In (L,c) entries.
Proof.
  intros R; exists (map (fun l => (r l,classes m l)) (seq 0 (next_loc m))).
  intros L c; split.
  - intros E; destruct (represents_domain R L E) as [l [Hl <-]].
    rewrite (represents_classes R Hl) in E; inversion E; subst c.
    apply in_map_iff; exists l; split; [reflexivity|apply in_seq; lia].
  - intros E; apply in_map_iff in E; destruct E as [l [Eq Hin]].
    apply in_seq in Hin. inversion Eq; subst. apply (represents_classes R); lia.
Qed.

Definition ghost_all_objects {A} (Q : class -> list A -> Prop) (m : machine A) :=
  forall l, l < next_loc m -> Q (classes m l) (object_history m l).
Definition surface_all_objects {A} (Q : class -> list A -> Prop) (M : surface A) :=
  forall L c, surface_classes M L = Some c -> Q c (surface_history M L).

Theorem represents_all_objects {A} r (m : machine A) M Q : represents r m M ->
  (ghost_all_objects Q m <-> surface_all_objects Q M).
Proof.
  intros R; split.
  - intros H L c E; destruct (represents_domain R L E) as [l [Hl <-]].
    rewrite (represents_classes R Hl) in E; inversion E; subst c.
    rewrite (represents_histories R Hl); apply H; exact Hl.
  - intros H l Hl; rewrite <- (represents_histories R Hl).
    apply H; apply (represents_classes R Hl).
Qed.

Theorem ghost_surface_prefix_properties {A} (s : statement A) Q :
  (forall m, program_prefix s initial_machine m -> ghost_all_objects Q m) <->
  (forall M, surface_program_prefix s initial_surface M -> surface_all_objects Q M).
Proof.
  split; intros H.
  - intros M E. destruct (@surface_ghost_prefix A (fun l => l) s
      initial_machine initial_surface M ghost_initial (represents_initial _) E)
      as [r [m [Ext [Ex R]]]].
    apply (proj1 (represents_all_objects Q R)); now apply H.
  - intros m E. destruct (@ghost_surface_prefix A (fun l => l) s
      initial_machine m initial_surface ghost_initial (represents_initial _) E)
      as [r [M [Ext [Ex R]]]].
    apply (proj2 (represents_all_objects Q R)); now apply H.
Qed.

Theorem ghost_surface_completion_properties {A} (s : statement A) Q :
  (forall m, program_execution s initial_machine m -> ghost_all_objects Q m) <->
  (forall M, surface_program_execution s initial_surface M -> surface_all_objects Q M).
Proof.
  split; intros H.
  - intros M E. destruct (@surface_ghost_program A (fun l => l) s
      initial_machine initial_surface M ghost_initial (represents_initial _) E)
      as [r [m [Ext [Ex R]]]].
    apply (proj1 (represents_all_objects Q R)); now apply H.
  - intros m E. destruct (@ghost_surface_program A (fun l => l) s
      initial_machine m initial_surface ghost_initial (represents_initial _) E)
      as [r [M [Ext [Ex R]]]].
    apply (proj2 (represents_all_objects Q R)); now apply H.
Qed.

Corollary ghost_surface_prefix_safety {A} (K : class -> language A) (s : statement A) :
  (forall m, program_prefix s initial_machine m ->
    forall l, l < next_loc m -> prefix_language (K (classes m l)) (object_history m l)) <->
  (forall M, surface_program_prefix s initial_surface M ->
    forall L c, surface_classes M L = Some c -> prefix_language (K c) (surface_history M L)).
Proof. apply (@ghost_surface_prefix_properties A s (fun c w => prefix_language (K c) w)). Qed.

Corollary ghost_surface_completion_safety {A} (K : class -> language A) (s : statement A) :
  (forall m, program_execution s initial_machine m ->
    forall l, l < next_loc m -> K (classes m l) (object_history m l)) <->
  (forall M, surface_program_execution s initial_surface M ->
    forall L c, surface_classes M L = Some c -> K c (surface_history M L)).
Proof. apply (@ghost_surface_completion_properties A s K). Qed.
