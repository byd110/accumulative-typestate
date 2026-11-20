# Foundations for Typestate Checking without Alias Analysis

This development proves the regular-seed construction, exact shuffle-closure
certification, and the draft's per-reference typestate safety and completion
theorems. It contains an executable finite checker and a verified connection
from a finite table of regular seeds to accepted client programs. An optional
per-class mode copies assignment histories when every reachable residual is
also shuffle closed, with a separate verified certificate and soundness proof.
An explicit semantic bridge relates these closure conditions to the
first-error subsequence property of Kellogg et al.'s *Accumulation Analysis*.
Parameterized protocol families cover persistent prerequisites, count
thresholds, and reusable capacity. Concrete ordered-milestone and independent-service
protocols add distinct persistent structures. Their executable queries, certificates,
exact seed languages, and aliasing clients are verified in the same core.

Start with the [claim-to-theorem map](CLAIM_THEOREM_MAP.md) for current paper
claims, exact theorem signatures, hypotheses, and remaining gaps. The
[paper-side artifact guide](../paper/ARTIFACT_README.md) gives a shorter result
index. Rocq is the only planned submission artifact.

For the paper's programming language, start with `statement` and `context` in
[syntax.v](syntax.v), then `surface_monitored_step` in
[surface_monitor.v](surface_monitor.v). These define straight-line statements,
left-to-right evaluation contexts, runtime protocol checks, and terminal errors.
[surface_semantics.v](surface_semantics.v) supplies the four-map state and
primitive updates. The unguarded relations in that file and
[semantics.v](semantics.v) support the soundness proofs. Bidirectional
simulations relate ghost and surface executions, both raw and monitored;
separate theorems establish that the guards cannot fail for accepted programs.

## Build and check

Tested with Coq/Rocq **8.20.0**, MathComp ssreflect **2.3.0**, Hierarchy Builder
**1.10.1**, and OCaml **4.14.2**. The RegLang sources are bundled in `RegLang/`.
The core reference calculus itself uses only the standard library.
GNU Make and Python 3 are also required. Exact prover dependencies are recorded
in [coq-accumulation.opam](coq-accumulation.opam).

With opam installed and initialized, create a dedicated switch from this
directory (dependency installation requires network access):

```sh
opam switch create accumulation-artifact ocaml-base-compiler.4.14.2
eval "$(opam env --switch=accumulation-artifact --set-switch)"
opam repository add rocq-released https://rocq-prover.org/opam/released
opam install . --deps-only
```

Once those dependencies are available, the proof build is offline and needs no
separately installed RegLang package. Run the following in this directory:

```sh
make -j2          # generates Makefile.coq and builds every listed source
make check       # source-hole check, then independent coqchk kernel checking
make assumptions # reprints the assumptions of the principal theorems
make clean       # remove generated proof artifacts
```

For a clean verification, run `make clean` first, then the three build/check
commands. Each must exit with status zero. `make check` scans the sources
listed in [_CoqProject](_CoqProject) and kernel-checks the audit/example
dependency closure. `make assumptions` prints the reports listed in
[audit.v](audit.v), each expected to say `Closed under the global context`.
These files are the authoritative source and audit inventories. To measure the
current project definitions and proofs, run `coqwc *.v`; this excludes comments
and the bundled RegLang sources, and includes examples and audit queries.

`_CoqProject` maps project modules to `Accumulation` and the bundled library to
`RegLang`. Coq reports an overlapping-loadpath warning because the latter is a
subdirectory. The explicit second mapping is intentional. The wrapper Makefile
replaces the old generated build, whose root mapping misnamed the library.
`Makefile.conf` is an unused legacy generated file. Current configuration is
`Makefile.coq.conf`. No system-installed RegLang binary is used by this build.

All project and bundled-library sources are checked for proof holes and new
global assumptions. The principal Rocq theorem audits report **Closed under the
global context**, including both end-to-end regular-program theorems. The existing
optional minimal-corpus argument in `pumping.v` uses classical logic. The new
certification and typestate results do not depend on that argument.

## Module map

| Layer | Files and contract |
| --- | --- |
| Existing language theory | `pumping.v`: pumping, singleton regex, bounded-star normalization, regularity, factorization, exact seed criterion, minimal corpora. |
| General trace languages | `trace_languages.v`: shuffle, residuals, prefix shuffle closure, exact tagged partitions and finite shuffle composition. |
| Coverage | `coverage.v`: executable block recognizer and equivalence to the singleton regex. `coverage_simulation.v`: the singleton automaton's reachable-state simulation, equivalence to that recognizer, and an at-most-`length(seed)+1` state bound. |
| Finite certification | `finite_shuffles.v`: complete shuffle enumeration. `certification.v`: Boolean seed/regex certification iff shuffle closedness, and checked rejection witnesses. |
| Decidable protocols | `protocols.v`: verified completion/viability interface. `regular_protocols.v`: explicit closure regex and an implementation using normalized-seed coverage for membership and DFA residual inhabitation for viability. |
| Exact protocol inputs | `exact_protocols.v`: DFA and regex adapters that preserve the supplied language, exact shuffle certification, and client completion soundness. `exact_protocol_examples.v`: the unchanged last-build protocol, accepted/rejected clients, and its distinction from pumping seeds. |
| Programming language | `syntax.v`: direct statements, finite maps, evaluation contexts, the finish-free source fragment, and single-exit instrumentation. `semantics.v`: unguarded primitive updates, configuration steps, finite execution, and the source/instrumented execution equivalence. `surface_semantics.v`: bidirectional ghost/surface simulation with arbitrary fresh locations, extensional observations, and all-object property transfer. |
| Runtime protocol checks | `monitor_shape.v`: raw references and heap targets denote allocated locations. `runtime_monitor.v`: explicit protocol-error outcomes, object-history call checks, allocation viability, a single all-object completion guard at bulk `Finish`, contextual errors, and raw/monitored prefix and final equivalence for accepted baseline and copying programs. `surface_monitor.v`: independent guarded surface rules, guard correspondence, successful/error execution simulations, and surface safety, completion, necessity, and monitor equivalence. |
| Typestate system | `typestate.v`: one class/history environment, structural statement typing/checking, current-binding bulk completion, and checker equivalence. `residual_typestate.v` and `copying_residual_typestate.v`: baseline and optional history/regex representation, primitive and structural transfer, and program acceptance correspondence. `residual_invariants.v`: reachable residual expression environments, binding agreement, viable views, and retired completion. |
| Metatheory | `invariants.v`: binding epochs, heap/class agreement, retired obligations, and preservation. `soundness.v`: prefix safety and all-object completion. `necessity.v`: completion soundness of the baseline core checker iff every class protocol is shuffle closed. `regular_soundness.v`: finite class-table certification composed with the client checker. |
| Optional history copying | `copying_typestate.v`: per-class mode and exact recovery of the original checker. `copying_languages.v`, `copying_soundness.v`: completion-continuation invariant, bulk-clear and configuration preservation, and source-program safety. `residual_certification.v`: exact finite DFA certificate. `copying_regular_soundness.v`: certified regular-seed integration. |
| Accumulation relationship | `accumulation_bridge.v`: first-error subsequence law, exact safety/residual-shuffle correspondence, and sufficient completion contract. `accumulation_integration.v`: observation interpretation, existing finite certificates, and client-soundness consequences. `accumulation_examples.v`: an inhabited contract and separating examples. `kellogg_separation.v`: the first-error separation and a concrete unsafe client when copying lacks its certificate. |
| Persistent machines | `monotone_protocols.v`: guarded runs, shuffle-closed derivatives, and safe repeat insertion. `monotone_pumping.v`: pumping closure. `monotone_regular.v`: finite DFA/regex representation and both certificates. |
| Prerequisite and threshold families | `prerequisite_patterns.v` and `prerequisite_examples.v`: monotone prerequisite predicates, all-of/any-of instances, exact displayed seed languages, and checked inherited aliases. `threshold_patterns.v` and `threshold_examples.v`: arbitrary thresholds, exact queries, saturated finite states, exact seeds including threshold zero, and checked aliases in both modes. |
| Ordered milestones and independent services | `persistent_pattern_queries.v`: exact executable queries, regularity, closure, accumulation laws, and checker soundness for finite monotone machines with a completing suffix. `milestone_service_patterns.v`: two concrete machines. `milestone_service_seeds.v`: exact displayed seeds. `milestone_service_examples.v`: checked clients and an explicit aliasing execution. |
| Reusable capacity | `capacity_patterns.v`: the prefix budget invariant over finite resource identities, basic certification, regularity, separation from residual closure and accumulation, and checked clients. `capacity_seed_table.v` and `capacity_seed_patterns.v`: checked exact correspondence with the displayed two-name six-seed language. `pattern_seed_automata.v`: generic frontier and DFA simulation lemmas. |
| Verification | `examples.v`, `certification_examples.v`, `copying_examples.v`, `residual_certification_examples.v`, `accumulation_examples.v`, `runtime_monitor_examples.v`, `audit.v`, and `check_sources.py`. |

The [bundled-library notice](RegLang/README.md) records RegLang's provenance,
known differences from upstream, and [CeCILL-B license](RegLang/LICENSE).

## Principal interfaces

- `covers_simulation_correct`: the reachable-state simulator agrees with exact
  singleton coverage. It considers both looping and advancing when both apply.
- `simulation_state_bound`: every simulated frontier has at most `|seed|+1`
  states. States encode consumed milestones and the remaining suffix. Deduplication
  is explicit. Lists implement sets, so this is a state bound, not a mechanized
  machine-time or constant-time-membership bound.
- `certify_regex_spec`: certification is necessary and sufficient for the
  pumping closure of an arbitrary regular expression to be shuffle closed.
- `seed_shuffle_coveredP`: the semantic seed criterion also applies to arbitrary
  proposition-valued seed sets. Executable certification uses finite enumeration.
- `regex_counterexample_sound`: rejection returns two accepted input histories,
  their shuffle, and a proof that the shuffled history is not accepted.
- `regex_counterexample_complete` and `regex_counterexample_none`: rejection
  always returns a witness, and witness absence is equivalent to certification.
- `check_step_sound` / `check_step_complete`, `check_stmt_spec`, `check_program_spec`: the executable
  client checker implements the declarative rules exactly.
- `instrument_single_exit`, `source_execution_iff`, and
  `source_execution_no_early_exit`: source programs exclude `Finish`, and
  instrumentation appends exactly one event-free bulk exit after source execution.
- `residual_program_correspondence` / `regular_residual_program_correspondence`:
  the baseline history checker accepts exactly the instrumented programs typed
  by the regular-expression rules. `copying_residual_program_correspondence`
  and `copying_regular_residual_program_correspondence` prove the same equivalence
  for optional inheritance, copying the source expression exactly when enabled. Related environments agree through current
  lookups; arbitrary expressions need not be representable by a class history.
- `reachable_residual_configuration` / `copying_reachable_residual_configuration`:
  every reachable configuration of an accepted source has a regex environment
  that types its remaining statement to the empty environment. Runtime bindings
  denote the corresponding viable residuals; retired views are complete. The
  copying theorem retains the completing-continuation invariant for overlapping
  views. Regular-seed variants discharge the initial representation premise.
- `ghost_surface_execution` / `surface_ghost_execution`: finite executions
  correspond in both directions after erasing epochs and renaming allocated
  locations. `ghost_surface_prefix_safety` / `ghost_surface_completion_safety`
  transfer properties of every allocated object, including unreachable ones.
- `typestate_prefix_sound` / `typestate_completion_sound`: accepted programs are
  safe at every executable prefix and complete on termination, for every
  allocated object, including unreachable objects.
- `baseline_runtime_no_error` / `copying_runtime_no_error`: accepted programs
  cannot produce the explicit `ProtocolError` outcome, under the respective
  protocol certificates.
- `baseline_runtime_equivalence` / `copying_runtime_equivalence`: accepted
  programs have exactly the same successful final states in raw and monitored
  execution. The raw-to-monitored direction establishes that guards do not
  remove accepted executions; error freedom is not obtained by assuming guards.
  `baseline_runtime_prefix_equivalence` and `copying_runtime_prefix_equivalence`
  also preserve each reachable residual statement. `surface_runtime_*` and
  `surface_copying_runtime_*` establish the corresponding results for the
  paper-style surface maps, with arbitrary fresh location names.
- `completion_sound_iff_certified`: raw completion soundness of this baseline core
  checker is equivalent to shuffle closedness of every class protocol. The
  converse realizes any two complete histories and their chosen interleaving
  by an accepted, terminating two-alias client.
  `surface_completion_sound_iff_certified` transfers the equivalence to raw
  surface executions; successful checked completion is not its premise.
- `regular_program_prefix_sound` / `regular_program_completion_sound`: the same
  guarantees after successful Boolean certification of a finite class table.

For concrete executions, inspect `aliases_terminates`,
`abandoned_object_terminates`/`abandoned_object_complete`, and
`inherited_progress_terminates`. These exhibit accepted terminating clients,
including an unreachable allocated object and overlapping inherited views.
`raw_invalid_call_executes` shows that the operational semantics permits a
protocol-invalid call: safety is a theorem about accepted programs.
The corresponding monitored execution reports `ProtocolError`, as shown by
`invalid_call_monitor_errors`. `runtime_monitor_examples.v` also checks invalid
allocation, incomplete exit for an unreachable object, a completed binding while
another continues, and successful baseline and inherited-history executions.
`noncanonical_surface_execution` and `noncanonical_surface_equipped` allocate
locations 37 and 5 and reconstruct a matching ghost execution. Both objects
remain observable after bulk exit removes their references.

### Enforcing an exact protocol instead of pumping seeds

`regular_family` interprets its regular expressions as seeds and recognizes
their pumping closures; `check_regular_program` combines their certification
with client checking. To enforce a supplied language unchanged, use
`exact_dfa_family` or `exact_regex_family` from
[exact_protocols.v](exact_protocols.v), followed by `check_program`.
The adapter theorems prove exact acceptance and viability queries. Client
soundness additionally requires `certified` for that family: client acceptance
alone does not certify a protocol. `certify_exact_dfa` and
`certify_exact_regex` provide exact closure decisions for these inputs.

[exact_protocol_examples.v](exact_protocol_examples.v) gives a four-state DFA
for `K_last = u {u,b}* b`, with `false` encoding `u` and `true` encoding `b`.
The exact checker accepts the completed history `ubub` and rejects a client
ending at `ubu`. The latter prefix remains viable: one more `b` completes it.
In contrast, the pumping closure of seed `ub` already accepts `ubu` as complete.
The executable example uses transparent queries to avoid RegLang's locked
finite-set representation. `k_last_exact_dfa_queries` proves that both queries
equal those of `exact_dfa_family` for every class and word.
Run this walkthrough from the package root after building:

```sh
coqtop -quiet -Q proof Accumulation -Q proof/RegLang RegLang <<'ROCQ'
From mathcomp Require Import all_ssreflect.
From Accumulation Require Import protocols typestate exact_protocols exact_protocol_examples.
Eval vm_compute in accepts k_last_family 0 [::false;true;false;true].
Eval vm_compute in accepts k_last_family 0 [::false;true;false].
Eval vm_compute in viable k_last_family 0 [::false;true;false].
Eval vm_compute in check_program k_last_family k_last_fields k_last_complete_client.
Eval vm_compute in check_program k_last_family k_last_fields k_last_incomplete_client.
Eval vm_compute in accepts ub_seed_family 0 [::false;true;false].
Check k_last_exact_dfa_queries.
Check k_last_exact_certificate.
Check k_last_complete_client_terminates.
Check k_last_client_completion_sound.
ROCQ
```

The six evaluations return `true`, `false`, `true`, `true`, `false`, `true`.
`k_last_dfa_language` proves the language equation for every word, and
`k_last_shuffle_closed` proves closure structurally. `k_last_exact_certificate`
then follows from the certificate's specification. This walkthrough evaluates
the exact language and client queries; it does not benchmark the reference
certificate's bounded-word enumeration over the product automaton.

### Runtime checks and the program boundary

`runtime_monitor.v` adds protocol guards to direct configuration steps.
Allocation requires a viable empty history. A call checks the updated aggregate
history of its receiver object; `runtime_call_guard` relates that test to the
old history followed by the called event. Copying, loads, and stores preserve
object histories and need no protocol guard.

A source program satisfies `finish_free`; its instrumented form is `Seq s Finish`.
The single bulk `Finish` clears all reference bindings without changing objects,
fields, classes, ownership, or events. The raw rule has no protocol premise.
Its monitored counterpart checks `runtime_exit_check` once, accepting exactly
when every allocated object's history is complete. There is no second check
outside execution. `runtime_exit_check_clear` proves that clearing references
preserves this aggregate predicate. Failed guards produce terminal
`ProtocolError`, which evaluation contexts propagate without executing their
continuation.

The static exit rule checks every current binding and returns the empty
environment. `all_complete_spec` ignores shadowed entries and states the exact
lookup-based obligation. `invariant_clear_refs` and `ci_clear_refs` retain
previously retired obligations while completing every still-live epoch.
Undefined references and field loads have no primitive step; the development
does not reclassify them as protocol errors or prove initialization progress.

## Relationship to Accumulation Analysis

The bridge extracts a trace property from Kellogg, Shadab, Sridharan, and
Ernst, [*Accumulation Analysis*, ECOOP 2022](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2022.10).
It does not rebuild their automata, calculus, analysis, or characterization
theorem. In our setting, let `P = prefix_language K`, and let
`u ⊑ v` mean an order-preserving subsequence, retaining repeated occurrences.
The encoded source condition is

```
u ⊑ v  /\  P v  /\  ~ P (v ++ [a])  ->  ~ P (u ++ [a]).
```

The premise `P v` matters: the final event first makes the actual history
nonviable. The shorter trace may have failed earlier. We interpret non-error
as extendibility to completion, which is not automatic for an arbitrary
non-error state of the source paper's automaton.

| Proven relationship | Theorem |
| --- | --- |
| The source condition is equivalent to preservation of a permitted next event along viable supersequences, given decidable viability. | `kellogg_error_closed_iff_safe_extension` |
| The source condition holds exactly when every residual of **P** is shuffle closed, given decidable viability. | `kellogg_error_closed_iff_residual_prefix_shuffle_closed` |
| Residual shuffle closure of **K** implies the source condition on **P**. | `residual_shuffle_closed_kellogg_error_closed` |
| Safe extension plus persistent completion imply residual shuffle closure of **K**, hence ordinary shuffle closure. | `accumulation_contract_residual_shuffle_closed`, `accumulation_contract_shuffle_closed` |
| Treating a call and a completion check as observations gives one persistence law equivalent to the two-part contract. | `observations_accumulate_iff_contract` |
| The extracted error and completion conditions imply success of both existing certificates for a compiled regular-seed protocol. | `kellogg_regular_certificates` |
| Those conditions supply the existing checker's prefix safety and all-object completion guarantees, for any assignment mode. | `kellogg_program_prefix_sound`, `kellogg_program_completion_sound` |

Persistent completion is the separate premise
`u ⊑ v -> K u -> P v -> K v`. It corresponds to requiring completion
permission to persist, motivated by the source paper's treatment
of acceptance as a legal “go out of scope” observation. The observation
interface adds no runtime event: bulk `Finish` clears all current bindings and preserves object histories.
No comparison of the two analyses' accepted programs is asserted, and no
new executable test for the extracted laws is introduced.

`kellogg_separation.v` also gives a concrete client showing why inheritance
needs the stronger certificate. `separating_copy_unsound_without_residual_certificate`
proves acceptance by the unchecked local copying checker, a terminating raw
execution, and the invalid object history `acb`. The certified entry point
requires the residual certificate and rejects this protocol for copying.

`two_calls_accumulation_contract` inhabits the contract with a protocol that
requires at least two occurrences of one event and forbids the other event.
`inherited_progress_sound_via_accumulation` derives completion for an accepted
client that copies an incomplete view and advances both aliases. Two unary
languages delimit the result: odd-length complete words have universally
viable prefixes but fail complete-history shuffle closure. Words of length
zero or at least two have shuffle-closed residuals but fail completion
stability. The existing seed-certified `separating_family` also fails the
full contract. These are kernel-checked witnesses, not just bounded tests.

The generic bridge assumes neither regularity nor a finite alphabet.
Decidability is explicit where the negative error law is converted to the
positive law. `protocol_family` supplies it via its verified viability query.
The regular-seed integration retains the existing finite-alphabet and
default-symbol parameters. All new theorem audits are closed under the
global context.

## Verified protocol patterns

The families in the paper's [protocol-pattern section](../paper/discussion.tex)
instantiate the existing `protocol_family` interface. Their Boolean viability
queries mean exactly that some completing suffix exists. Completion is a client
policy: the new examples require the final ordered milestone or both independent
queries; the prerequisite, threshold, and capacity models require a designated use.

The `monotone_machine` interface in [monotone_protocols.v](monotone_protocols.v)
requires upward-closed guards and acceptance, monotone enabled transitions,
and inflationary transitions. `machine_language_residual_shuffle_closed` and
`machine_language_repeat` prove continuation composition and repeat insertion.
[monotone_pumping.v](monotone_pumping.v) connects repetition to pumping closure.
For finite alphabets and states with Boolean guard and acceptance queries,
[monotone_regular.v](monotone_regular.v) constructs a DFA and a regular seed
expression: `finite_machine_regular_family_language` proves exact language
equality, and `finite_machine_seed_certificate` and
`finite_machine_copying_certificate` establish both certificates.

| Family | Definitions and main guarantees |
| --- | --- |
| Ordered milestones | [milestone_service_patterns.v](milestone_service_patterns.v): `milestone_family` permits the first `i` only after `t` and the first `r` only after `i`; earlier events remain enabled. Completion requires `r`. `milestone_copying_certified`, `milestone_pumping`, and `milestone_accumulation_contract` prove both checking modes, pumping closure, and accumulation safety with stable completion. |
| Independent services | [milestone_service_patterns.v](milestone_service_patterns.v): `service_family` requires `t` before `w` and `c` before `q`, with both queries required for completion. `service_copying_certified`, `service_pumping`, and `service_accumulation_contract` prove the same properties. Each service may be used before the other is configured. |
| Persistent prerequisites | [prerequisite_patterns.v](prerequisite_patterns.v): `prerequisite_spec` packages a satisfiable monotone Boolean predicate on a finite feature set. `all_prerequisites` and `any_prerequisites` instantiate it. `prerequisite_viable_spec`, `prerequisite_protocol_copying_certified`, `prerequisite_language_regular`, and `prerequisite_regular_family_exact` connect queries, both modes, and regular seeds. |
| Count thresholds | [threshold_patterns.v](threshold_patterns.v): `threshold_family N` permits `Use` only after at least `N` increments and permits subsequent increments and uses. `threshold_queries`, `threshold_language_shape`, and `threshold_copying_certified` characterize queries and both modes for every natural `N`. [threshold_examples.v](threshold_examples.v): `threshold_finite_language`, `threshold_regular`, and `threshold_regular_family_exact` justify the saturated finite-state representation. |
| Reusable capacity | [capacity_patterns.v](capacity_patterns.v): `capacity_safeP` equates the executable check with the requirement that every prefix uses at most as many distinct identities as it has capacity additions. `capacity_viable_spec`, `capacity_certified`, and `capacity_regular` give exact viability, basic certification, and regularity. With two distinct identities, `capacity_not_residual` and `capacity_certified_not_kellogg` prove the stronger conditions fail. |

The manuscript abbreviates ordered events `t,i,r` as `a,b,c` and service
events `t,w,c,q` as `a,b,c,d`. These are changes of event names: the
source seeds and theorems below retain their mnemonic names.

The ordered-milestone and independent-service results are concrete three- and
four-event instances. Their common wrapper, [persistent_pattern_queries.v](persistent_pattern_queries.v),
provides generic exact queries and soundness from a finite monotone machine and
a suffix that completes every state. Both new patterns satisfy the extracted
accumulation contract; reusable capacity supplies the separation from that law.

The pumping closures of the concrete seeds equal the **whole** modeled
languages. In [milestone_service_seeds.v](milestone_service_seeds.v),
`milestone_displayed_seeds_exact` covers `{tir}`, and
`service_displayed_seeds_exact` covers `{twcq,tcwq,tcqw,ctwq,ctqw,cqtw}`.
In [prerequisite_examples.v](prerequisite_examples.v),
`builder_displayed_seeds_exact` covers `{abu,bau}` and
`alternative_displayed_seeds_exact` covers `{au,bu,abu,aub,bau,bua}`.
These Boolean equalities connect to pumping closure through `coveredb_spec`.
In [threshold_examples.v](threshold_examples.v),
`threshold_singleton_seed_exact` covers `{a^N u}` when `N > 0`, and
`threshold_zero_seeds_exact` covers `{u,au,ua}` when `N = 0`.
In [capacity_seed_patterns.v](capacity_seed_patterns.v),
`capacity_six_seeds_exact` covers `{ab,ac,aabc,abac,aacb,acab}` for two identities.
The letters in these displays follow the paper; the modules use their stated
Boolean or option encodings.

[milestone_service_examples.v](milestone_service_examples.v) checks the ordered
client and an out-of-order rejection. Its inherited service client has local
histories `twcq` and actual object history `twwccqq`; the module proves checker
acceptance, rejection without inheritance, a terminating execution, and
`service_alias_completion`. A client using only the first service is incomplete.

The family modules also check clients and failures. The builder and threshold
examples accept inherited aliases, reject the corresponding client without
inheritance, and exhibit terminating runs and exact object histories.
`threshold_counts_not_sets` shows that one and two increments have different
permissions despite containing the same event set. Capacity examples accept
fresh-history aliases and repeated use of one identity; they reject overdraw,
late capacity additions, and an incomplete alias. The `prerequisite_checked_*`,
`threshold_*_sound`, and `capacity_program_*_sound` results connect these families
to the existing prefix/completion guarantees.

For direct evaluation, `capacity_executable_family` uses a duplicate-free list
of occupied identities. `capacity_safe_query_correct` and
`capacity_complete_query_correct` prove equality with the finite-set model;
`capacity_executable_certified` supplies the generic checker premise. The
capacity clients evaluate this implementation, and their completion example
transfers the resulting guarantee back to the semantic language.

The capacity frontier table can be reproduced without overwriting the source:

```sh
python3 generate_capacity_frontier.py > /tmp/capacity_seed_table.v
diff -u capacity_seed_table.v /tmp/capacity_seed_table.v
```

The new frontier tables can likewise be reproduced without overwriting sources:

```sh
python3 generate_milestone_service_frontiers.py > /tmp/milestone_service_seed_tables.v
diff -u milestone_service_seed_tables.v /tmp/milestone_service_seed_tables.v
```

The Python generators are untrusted. Rocq checks each table's initial frontier,
every transition, acceptance, and simulation into the corresponding semantic DFA.
The exact-language proof therefore covers arbitrary words. The paper's
SQLite schema operations and the selected `ImageWriteParam` fragment motivate
the two new event interpretations. Earlier AutoValue, Commons CLI, and append-only
`ArrayList` examples remain supported by the artifact. These results do not
verify the library implementations or translations into the core calculus.

## Semantic choices and scope

A qualifier is a class and its local history. Its denotation is the exact left
residual `history⁻¹ K`. A call appends one event, viability tests nonemptiness,
and completion tests nullability. The checker contains no locations, epochs,
heap-object histories, or alias sets. This history representation is a simple
verified implementation of residuals, not a minimized-automaton implementation.

In the baseline mode, allocation, copying, and field loading start a **fresh binding history**.
Overwriting a binding first requires its old history to be complete. Bulk
`Finish` removes all bindings and does not deallocate objects. Stores preserve
local histories and check field classes. `typed_stmt` and `check_stmt` compose
sequencing through one intermediate environment. `Skip` preserves that
environment and is terminal operationally. Public program checking and execution
take finish-free sources and append the common exit automatically.

`residual_typestate.v` relates each class/history qualifier to an expression
whose denotation is its exact residual. Verified derivative, inhabitation, and
nullability operations justify each baseline transfer, sequencing, and bulk
completion. `copying_residual_typestate.v` extends both directions to inherited
assignment expressions while reusing the ordinary expression rules. The converse starts from related environments; it does not claim
that every arbitrary expression is a residual of a fixed class protocol.

For the optional mode, `check_program_with_copy` takes a Boolean mode per class.
An enabled class must satisfy `residual_shuffle_closed`, which quantifies over
all left derivatives, including the initial state. Assignment copies the
source view and keeps the outgoing-target completion check. This also retains
the existing completion requirement on self-assignment. Allocation and field
loads still start fresh. Source and target then advance independently.
The checker still stores no locations, alias relation, or copying genealogy.
`fresh_program_unchanged` proves exact recovery of the baseline checker when
all modes are disabled.

`certify_residuals_spec` proves that the executable DFA certificate succeeds
exactly when every reachable derivative is shuffle closed. A tagged alphabet
records which continuation supplies each event to a product of three states.
The reference implementation uses the bundled DFA finite inhabitation procedure,
not an optimized graph search. The cubic product-state bound is therefore not
a runtime bound. `certify_copying_regex_spec` connects the certificate to the
compiled pumping closure.

`check_regular_program_with_copy` takes the regular specifications and a list
of per-class Boolean flags, defaulting to false beyond the list. It retains
ordinary seed certification for every class and additionally certifies all
reachable residuals for each enabled class. Its two
`copying_regular_program_*_sound` theorems cover prefix safety and all-object
completion. Regression examples include nested copies, mixed modes, target
overwriting, fresh field loads, and the protocol that passes the original
certificate but fails the residual certificate.

The optional proof uses hypothetical completing continuations for epoch views.
Retagging a new epoch's continuation to its source invokes residual shuffle
closure without duplicating past events. All viable views admit a joint
completion, and completed views admit the empty future. This replaces the
partition invariant for inherited views while preserving the raw semantics.
Completing through one alias still does not discharge another alias's local
obligation, which can cause false positives.

The raw runtime carries ghost epoch tags to state the history-partition invariant.
Raw operational calls have **no protocol premise**. The original soundness
theorems prove protocol membership from the checker independently of runtime
guards. The monitored semantics adds those guards and explicit error outcomes;
its error-freedom and equivalence theorems follow from the raw results.
Class correctness is preserved by the invariant. Uninitialized field loads
have no transition, so the theorem concerns all executable prefixes and
completed executions. It does not claim initialization progress. The paper
assumes ordinary typing and scope correctness and likewise gives undefined
accesses no reduction.

The calculus has allocation, copy, fields, atomic event calls, terminal `Skip`,
sequencing, and one instrumented bulk `Finish`. It excludes conditionals,
Boolean expressions, loops, method bodies, exceptions, callbacks, and concurrency.
The core has no verified parser or correspondence with a full-language implementation. The regular-seed bridge
inherits the existing finite alphabet and a chosen default symbol in the pumping
relation. The generic client soundness proof has no finite-alphabet assumption.
All classes share the event carrier `A`. Per-class alphabets are interpreted
through their protocol languages; if complete words use only a class's events,
viability excludes an appended event outside that alphabet. A separate
class-table frontend is outside the artifact.

The implementation is executable but favors simple verified constructions.
Shuffle enumeration and finite normalization can be large. DFA viability is
a reference decision procedure, not a performance claim. Integration examples
use its proved query specification to avoid expanding enormous automaton
representations inside the proof kernel.

## Remaining release items

The author-owned sources do not yet have a declared distribution license.
The RegLang license is included separately and does not assign a license to
the rest of this project. Choose and add the project license before public
release. The opam metadata deliberately leaves that field unset.
An archival artifact URL/DOI also remains to be supplied.

The claim map records the proved source instrumentation, baseline residual
representations in both modes, and ghost/surface correspondences, alongside the remaining
scope boundaries. The baseline necessity result is mechanized for
the core checker. These remaining boundaries are
not failed proofs or admitted theorems. No container image or fresh
operating-system dependency installation has been validated. The source
builds were checked from clean copies using the stated installed toolchains.
