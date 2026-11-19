# Pumping protocols and alias-oblivious typestate

This development proves the regular-seed construction, exact shuffle-closure
certification, and the draft's per-reference typestate safety and completion
theorems. It contains an executable finite checker and a verified connection
from a finite table of regular seeds to accepted client programs. An optional
per-class mode copies assignment histories when every reachable residual is
also shuffle closed, with a separate verified certificate and soundness proof.
An explicit semantic bridge relates these closure conditions to the
first-error subsequence property of Kellogg et al.'s *Accumulation Analysis*.

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
commands. Each must exit with status zero. `make check` scans all 49 sources
listed in `_CoqProject` and kernel-checks the audit/example dependency closure.
`make assumptions` prints 185 reports, each expected to say
`Closed under the global context`. The 37 project sources contain 3,640
specification lines and 4,393 proof lines (8,033 total by `coqwc *.v`),
excluding the 12 bundled RegLang sources and comments. `_CoqProject` and
`audit.v` are the authoritative source and audit inventories.

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
| Programming language | `syntax.v`: direct statements, finite maps, evaluation contexts, the finish-free source fragment, and single-exit instrumentation. `semantics.v`: unguarded primitive updates, configuration steps, finite execution, and the source/instrumented execution equivalence. `surface_semantics.v`: bidirectional ghost/surface simulation with arbitrary fresh locations, extensional observations, and all-object property transfer. |
| Runtime protocol checks | `monitor_shape.v`: raw references and heap targets denote allocated locations. `runtime_monitor.v`: explicit protocol-error outcomes, object-history call checks, allocation viability, a single all-object completion guard at bulk `Finish`, contextual errors, and raw/monitored prefix and final equivalence for accepted baseline and copying programs. `surface_monitor.v`: independent guarded surface rules, guard correspondence, successful/error execution simulations, and surface safety, completion, necessity, and monitor equivalence. |
| Typestate system | `typestate.v`: one class/history environment, structural statement typing/checking, current-binding bulk completion, and checker equivalence. `residual_typestate.v` and `copying_residual_typestate.v`: baseline and optional history/regex representation, primitive and structural transfer, and program acceptance correspondence. `residual_invariants.v`: reachable residual expression environments, binding agreement, viable views, and retired completion. |
| Metatheory | `invariants.v`: binding epochs, heap/class agreement, retired obligations, and preservation. `soundness.v`: prefix safety and all-object completion. `necessity.v`: completion soundness of the baseline core checker iff every class protocol is shuffle closed. `regular_soundness.v`: finite class-table certification composed with the client checker. |
| Optional history copying | `copying_typestate.v`: per-class mode and exact recovery of the original checker. `copying_languages.v`, `copying_soundness.v`: completion-continuation invariant, bulk-clear and configuration preservation, and source-program safety. `residual_certification.v`: exact finite DFA certificate. `copying_regular_soundness.v`: certified regular-seed integration. |
| Accumulation relationship | `accumulation_bridge.v`: first-error subsequence law, exact safety/residual-shuffle correspondence, and sufficient completion contract. `accumulation_integration.v`: observation interpretation, existing finite certificates, and client-soundness consequences. `accumulation_examples.v`: an inhabited contract and separating examples. `kellogg_separation.v`: the first-error separation and a concrete unsafe client when copying lacks its certificate. |
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
