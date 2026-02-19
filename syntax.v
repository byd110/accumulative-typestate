(* the basic syntax for checkol *)

Require Import String.
Require Import Coq.Sets.Ensembles.
From RecordUpdate Require Import RecordSet.
From RecordUpdate Require Import RecordUpdate.
From RegLang Require Import languages.
Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import all_ssreflect.

(* ------------------SYNTAX------------------*)
Definition var : Type := nat.
Definition method_name : Type := nat.
Definition class_name : Type := nat.

(* Protocol *)
Parameter char : eqType.
Definition eps : word char := [::].
Definition protocol : Type := dlang char.


(* Definition r_a := { x : a | x = Assignable \/ x = Final}. *)

(* Canonical projection for assignability *)
(* Definition r_a_proj (x : r_a) : a := proj1_sig x. *)

(* Qualified type  *)
Record qualified_type := {
  pi : protocol; (* Type qualifier *)
  sctype: class_name; (* Class name *)
}.

Definition s_env := list qualified_type.

Inductive expr : Type :=
  | ENull : expr
  | EVar : var -> expr
  | EField : var -> var -> expr.

Inductive stmt: Type :=
  | SSkip: stmt (* skip *)
  | SLocal: class_name -> var -> stmt (* T x*)
  | SVarAss: var -> expr -> stmt (* x = e *)
  | SFldWrite: var -> var -> var -> stmt (* x.f = y *)
  | SNew: var -> class_name -> list var -> stmt (* x = new q_c C(y1, ..., yn) *)
  | SCall: var -> var -> method_name -> list var -> stmt (* x = y.m(z1, ..., zn) *)
  (* | SCast: var -> q -> class_name -> var -> stmt x = (q C) y  *)
  | SSeq: stmt -> stmt -> stmt. (* s1; s2 *)

Definition field_type : Type := class_name.

(* Field declaration with assignability and mutability *)
Record field_def := {
  ftype : field_type; (* Field type *)
  fname : var; (* Field name, the name should match the index from the field list *)
}.

Record constructor_body :={
  super_call: list var; (* Super(f1, ..., fn)*)
  assignments: list (var * var); (* this.f1 = f_1; ...; this.fn = f_n *)
}.

Record constructor_sig := {
  sparams : list class_name; (* T x1, ..., T xn Parameters for super call *) (*s -> super*)
  cparams : list class_name; (* T y1, ..., T yn Parameters for field assignment *) (*c -> current*)
}.

Record constructor_def := {
  csignature : constructor_sig; (* Constructor signature *)
  cbody : constructor_body; (* Constructor body *)
}.

Record method_body := {
  mbody_stmt: stmt; (* Method body expression *)
  mreturn: var; (* Return variable *)
}.

Record method_sig := {
  mret : qualified_type; (* Return type *)
  mname : method_name; (* Method name *)
  mreceiver: class_name; (*T this*)
  mparams : list class_name; (* T x1, ..., T xn *)
}.

Record method_def := {
  msignature : method_sig; (* Method signature *)
  mbody : method_body; (* Method body *)
}.

Record class_body := {
  fields : list field_def; (* Class fields *)
  constructor: constructor_def; (* Constructor declaration *)
  methods : list method_def; (* Class methods *)
}.

Record class_sig := {
  class_qualifier : protocol; (* Mutable, Immutable, or RDM *)
  cname : class_name; (* Class name, need to be the same as the index from class_table *)
  super : option class_name; (* Superclass name *)
}.

Record class_def := {
  signature : class_sig; (* Class signature *)
  body : class_body; (* Class body *)
}.

Record program_def := {
  classes: list class_def; (* List of class declarations *)
  main_statement: stmt; (* Main statement *)
}.

(* Class table is a list of class declarations *)
Definition class_table := list class_def.

(* ------------------RUNTIME MODEL------------------*)

(* Initialization state *)
(* Inductive init: Type := 
  | initing
  | inited. *)

(* Runtime protocol *)
Definition protocol_r : Type := dlang char.

(* Runtime conformance check *)
Definition Prot_conf (pi : protocol) : bool :=
  eps \in pi.

(* Static qualified type *)
(* Runtime type *)
Record runtime_type := mkruntime_type {
  rqtype: protocol_r; (* Runtime mutability *)
  rctype: class_name; (* Class name *)
}.

(* Memory address *)
Definition Loc : Type := nat.

(* Runtime value *)
Inductive value : Type :=
  | Null_a : value
  | Iot: Loc -> value.

(* Field mapping *)
Definition fields_mapping := list value. 
Definition var_mapping   := list value.

Record r_env := mkr_env {
  vars: var_mapping; (* Variable mapping *)
  (* Initialization state *)
  (* init_state: init; *)
}.

(* Runtime object *)
Record Obj := mkObj {
  rt_type: runtime_type; (* Runtime type *)
  fields_map: fields_mapping; (* Field mapping *)
}.

Definition heap          := list Obj.

(* AOSEN: just a test *)
(* Instance settable_r_env : Settable _ :=
  mkSettable (generate_setters mkr_env vars init_state). *)
Record test := mktest {
  abc: nat;
  bcd: nat;
}.

Definition example_env := mktest 42 1.

Definition updated_env := example_env <|abc := 100|>.