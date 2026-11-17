(* Operational semantics with a ghost epoch for each binding. Calls are
   unguarded: protocol safety is a theorem, never an execution premise. *)
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
Definition retire {A} (m : machine A) x : machine A :=
  {| next_loc := next_loc m; classes := classes m; next_epoch := next_epoch m;
     owners := owners m; refs := put (refs m) x None; heap := heap m;
     events := events m |}.
Definition store {A} (m : machine A) l f target : machine A :=
  {| next_loc := next_loc m; classes := classes m; next_epoch := next_epoch m;
     owners := owners m; refs := refs m;
     heap := fun q => if q =? l then update (heap m l) f (Some target) else heap m q;
     events := events m |}.

Inductive raw_step {A} : instruction A -> machine A -> machine A -> Prop :=
| run_new m x c : raw_step (New x c) m (allocate m x c)
| run_copy m x y e : get (refs m) y = Some e ->
    raw_step (Copy x y) m (bind m x (owners m e))
| run_load m x y f e l : get (refs m) y = Some e ->
    heap m (owners m e) f = Some l -> raw_step (Load x y f) m (bind m x l)
| run_store m x f y e d : get (refs m) x = Some e -> get (refs m) y = Some d ->
    raw_step (Store x f y) m (store m (owners m e) f (owners m d))
| run_call m x a e : get (refs m) x = Some e -> raw_step (Call x a) m (emit m e a)
| run_finish m x e : get (refs m) x = Some e -> raw_step (Finish x) m (retire m x).

Inductive execution {A} : list (instruction A) -> machine A -> machine A -> Prop :=
| execution_nil m : execution [] m m
| execution_cons i is m m' m'' : raw_step i m m' -> execution is m' m'' ->
    execution (i :: is) m m''.

Definition program_execution {A} (s : statement A) m m' :=
  exists p, path s p /\ execution p m m'.
Definition program_prefix {A} (s : statement A) m m' :=
  exists p q, path s (p ++ q) /\ execution p m m'.
