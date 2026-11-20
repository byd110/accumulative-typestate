# Paper claims and Rocq theorems

This map expands the result index in [the artifact guide](../paper/ARTIFACT_README.md).
It distinguishes what the Rocq development proves from the paper's mathematical
arguments, presentation refinements, and implementation boundaries. The map is
about the current source declarations. Build and reproduction instructions are
in [README.md](README.md).

**The main result is an end-to-end execution guarantee.** Successful regular-seed
certification and successful core client checking imply viability of every
allocated object's history at every executable prefix and acceptance of each
history at a completed execution. Optional history inheritance has the same
conclusions under the stronger residual certificate. Neither raw result assumes
protocol safety in the call rule. The monitored semantics adds explicit error
outcomes, and its error freedom and equivalence follow from these raw results.
For the fixed baseline core checker,
the converse also holds: completion soundness for all accepted clients implies
shuffle closure of every class protocol. Here necessity and the iff result
concern **raw completion soundness**, not completion of successful monitored
runs, whose exit guard enforces acceptance by definition. The monitor proves
certification implies error freedom and execution equivalence; a converse for
monitored error freedom is not asserted or mechanized here.

Read the classifications as follows:

- **PROVEN:** the cited declarations entail the claim within the stated model
  and hypotheses.
- **WEAKER:** a part of the paper statement, or its stated generality,
  lies beyond the cited mechanized result. The gap column identifies that part.
- **UNMECHANIZED:** a paper argument or model/implementation correspondence has
  no theorem in this development. This classification does not mean the claim
  is false.
- **SOURCE/BUILD FACT:** a reproducible statement about files or tool output,
  rather than a mathematical theorem.

The declaration index reproduces the indexed signatures verbatim. The
protocol-pattern table links directly to its definitions and theorem sources.
Section parameters are generalized theorem parameters, not extra axioms.
LaTeX labels identify paper results independently of their printed numbering.

## Claim extraction and traceability

### Direct execution and its correspondences

Source programs contain no `Finish`; `instrument` appends it once. Both raw and
monitored execution reduce configurations containing a machine and the remaining
statement. Structural typing uses one environment at every program point.

| Claim | Evidence | Verdict and boundary |
| --- | --- | --- |
| Public execution uses direct statements, evaluation contexts, terminal `Skip`, and sequencing. | `raw_step`, `execution`, `raw_step_decompose`, `raw_step_context`, `execution_context` | PROVEN. No path enumeration or branch constructor is part of the supported language. |
| Source instrumentation appends exactly one bulk exit after source execution. | [`instrument_single_exit`](#declaration-instrument-single-exit), [`source_execution_iff`](#declaration-source-execution-iff), [`source_execution_no_early_exit`](#declaration-source-execution-no-early-exit) | PROVEN for finish-free sources. Exit preserves the event log and every object's history. |
| Bulk static completion inspects current bindings and preserves retired obligations. | [`all_complete_spec`](#declaration-all-complete-spec), [`invariant_clear_refs`](#declaration-invariant-clear-refs), [`ci_clear_refs`](#declaration-ci-clear-refs) | PROVEN. Obsolete association-list entries impose no additional completion obligation. |
| Both class/history checkers implement their expression rules. | [`residual_checker_correspondence`](#declaration-residual-checker-correspondence), [`residual_program_correspondence`](#declaration-residual-program-correspondence), [`regular_residual_program_correspondence`](#declaration-regular-residual-program-correspondence), [`copying_residual_program_correspondence`](#declaration-copying-residual-program-correspondence), [`copying_regular_residual_program_correspondence`](#declaration-copying-regular-residual-program-correspondence) | PROVEN for related input environments and a correct initial expression per class; the regular-seed instance discharges that representation premise. The converse does not represent arbitrary expressions as class histories. |
| Reachable configurations carry a corresponding residual expression environment. | [`reachable_residual_configuration`](#declaration-reachable-residual-configuration), [`copying_reachable_residual_configuration`](#declaration-copying-reachable-residual-configuration), [`regular_reachable_residual_configuration`](#declaration-regular-reachable-residual-configuration), [`copying_regular_reachable_residual_configuration`](#declaration-copying-regular-reachable-residual-configuration) | PROVEN. A canonical derivative expression for each history preserves literal empty output typing. Live views have nonempty residuals and retired views are complete. Inherited views retain the continuation invariant instead of being identified with disjoint event histories. |
| Epoch bookkeeping can be erased and reconstructed for arbitrary fresh surface locations. | [`ghost_surface_execution`](#declaration-ghost-surface-execution), [`surface_ghost_execution`](#declaration-surface-ghost-execution), [`represents_extensional`](#declaration-represents-extensional) | PROVEN in both directions with an injective renaming on allocated locations. Map observations are extensional; no equality of association-list encodings or literal final location names is asserted. |
| Surface and ghost executions have the same all-object prefix and final properties. | [`ghost_surface_prefix_safety`](#declaration-ghost-surface-prefix-safety), [`ghost_surface_completion_safety`](#declaration-ghost-surface-completion-safety) | PROVEN for every allocated object, including unreachable ones. Ordinary initialization and termination remain outside the theorem. |
| Allocation checks empty-history viability; calls check the updated receiver history. | `runtime_guard`, `monitored_step`, [`runtime_call_guard`](#declaration-runtime-call-guard) | PROVEN. Failed guards produce `ProtocolError`; undefined ordinary accesses have no primitive step. |
| The single bulk `Finish` checks every allocated object's completion. | [`runtime_exit_check_spec`](#declaration-runtime-exit-check-spec), [`runtime_exit_check_clear`](#declaration-runtime-exit-check-clear) | PROVEN. The guard is part of the instrumented primitive; there is no additional program-boundary guard. |
| Guarded surface executions and errors agree with the ghost monitor. | [`runtime_surface_guard`](#declaration-runtime-surface-guard), [`ghost_surface_monitored_execution`](#declaration-ghost-surface-monitored-execution), [`surface_ghost_monitored_execution`](#declaration-surface-ghost-monitored-execution), [`ghost_surface_error_equivalence`](#declaration-ghost-surface-error-equivalence) | PROVEN for independently defined guarded surface rules, with the same location-renaming boundary as raw simulation. |
| Surface source programs retain safety, completion, monitor equivalence, and baseline necessity. | [`surface_typestate_prefix_sound`](#declaration-surface-typestate-prefix-sound), [`surface_typestate_completion_sound`](#declaration-surface-typestate-completion-sound), [`surface_copying_prefix_sound`](#declaration-surface-copying-prefix-sound), [`surface_copying_completion_sound`](#declaration-surface-copying-completion-sound), [`surface_completion_sound_iff_certified`](#declaration-surface-completion-sound-iff-certified) | PROVEN. Necessity quantifies over raw surface completion; it is not a consequence of the monitored exit guard. |
| Protocol errors propagate through evaluation contexts and are terminal. | [`monitored_error_context`](#declaration-monitored-error-context), [`monitored_error_terminal`](#declaration-monitored-error-terminal) | PROVEN. The remaining continuation does not execute after an error. |
| Accepted baseline and inherited-history programs cannot signal protocol errors. | [`baseline_runtime_no_error`](#declaration-baseline-runtime-no-error), [`copying_runtime_no_error`](#declaration-copying-runtime-no-error) | PROVEN under ordinary or mode-aware certification, using raw prefix/completion soundness. |
| Restoring guards preserves accepted final executions and reachable residual configurations. | [`baseline_runtime_equivalence`](#declaration-baseline-runtime-equivalence), [`copying_runtime_equivalence`](#declaration-copying-runtime-equivalence), [`baseline_runtime_prefix_equivalence`](#declaration-baseline-runtime-prefix-equivalence), [`copying_runtime_prefix_equivalence`](#declaration-copying-runtime-prefix-equivalence) | PROVEN in both directions with the same ghost machine and residual statement. |

### Earlier language and checker results

The first table paraphrases the formal claims from the current abstract,
introduction, contribution list, mechanization section, and conclusion. Repeated claims remain visible
so that an abstract-level statement can be checked without inferring its intended
scope from the body. The next table covers every numbered lemma, proposition, and
theorem in the technical development. Paper links identify source files, with
section or result labels in the link text where available, rather than source
line numbers. The first table's paraphrases are not verbatim quotations.

| Claim and source | Current paper claim (paraphrased) | Evidence | Verdict | Exact scope or gap |
| --- | --- | --- | --- | --- |
| A1 [Abstract](../paper/abstract.tex) | Alias tracking can be omitted when operations through one reference preserve permissions established through other references to the same object. | [`typestate_prefix_sound`](#declaration-typestate-prefix-sound), [`typestate_completion_sound`](#declaration-typestate-completion-sound) | PROVEN, scoped | The formal result is for the specified independent-history checker and certified protocol family, not an arbitrary analysis satisfying an informal persistence description. |
| A2 [Abstract](../paper/abstract.tex) | The paper formalizes a checker that tracks references independently and gives a necessary and sufficient protocol condition for that checking discipline. | [`typestate_prefix_sound`](#declaration-typestate-prefix-sound), [`typestate_completion_sound`](#declaration-typestate-completion-sound), [`completion_sound_requires_certified`](#declaration-completion-sound-requires-certified), [`completion_sound_iff_certified`](#declaration-completion-sound-iff-certified) | PROVEN for the core | For this fixed baseline checker, raw all-object completion soundness holds exactly when every class protocol is shuffle closed. Source instrumentation and raw ghost/surface correspondence are proved below. This does not characterize all analyses without aliases. |
| A3 [Abstract](../paper/abstract.tex) | Calls through aliases interleave into one object history. Every interleaving of permitted complete histories must therefore remain permitted. | [`project_partition`](#declaration-project-partition), [`tagged_shuffle_closed`](#declaration-tagged-shuffle-closed), [`invariant_object_language`](#declaration-invariant-object-language) | PROVEN | Fresh epoch histories partition actual calls. Inherited histories instead use completing continuations. They do not form this partition. |
| A4 [Abstract](../paper/abstract.tex) | Regular expressions describe representative histories from which candidate protocols are constructed. A decision procedure certifies shuffle closedness or returns a counterexample. | [`pumping_normalize_correct`](#declaration-pumping-normalize-correct), [`closure_regex_correct`](#declaration-closure-regex-correct), [`certify_regex_spec`](#declaration-certify-regex-spec), [`regex_counterexample_complete`](#declaration-regex-counterexample-complete), [`regex_counterexample_none`](#declaration-regex-counterexample-none), [`regex_counterexample_sound`](#declaration-regex-counterexample-sound) | PROVEN | Finite regular-expression input, finite inhabited alphabet for the pumping relation. Total Rocq definitions give termination. No practical runtime bound is claimed. |
| A5 [Abstract](../paper/abstract.tex) | The paper connects its condition to accumulation analysis and gives a supported protocol whose safe histories violate the accumulation condition. | [`kellogg_error_closed_iff_residual_prefix_shuffle_closed`](#declaration-kellogg-error-closed-iff-residual-prefix-shuffle-closed), [`accumulation_contract_residual_shuffle_closed`](#declaration-accumulation-contract-residual-shuffle-closed), [`separating_certified_not_kellogg`](#declaration-separating-certified-not-kellogg) | PROVEN, scoped | The bridge extracts a first-error trace law and interprets non-error as extendibility to completion. It does not formalize the other analysis or compare accepted client programs. |
| A6 [Abstract](../paper/abstract.tex) | For accepted programs, execution remains safe and every allocated object’s history is accepted at termination. | [`regular_program_prefix_sound`](#declaration-regular-program-prefix-sound), [`regular_program_completion_sound`](#declaration-regular-program-completion-sound), [`copying_regular_program_prefix_sound`](#declaration-copying-regular-program-prefix-sound), [`copying_regular_program_completion_sound`](#declaration-copying-regular-program-completion-sound) | PROVEN, scoped | Accepted source programs, with a single automatically instrumented bulk exit. Completed execution is a premise. Initialization progress and termination are not conclusions. |
| A7 [Abstract](../paper/abstract.tex) | The Rocq development verifies the language constructions, certification procedures, and core checker soundness without additional axioms. | [audit.v](audit.v), [build instructions](README.md) | PROVEN for audited results | Principal theorem assumption reports establish the no-additional-axioms claim. Optional minimal-corpus results use classical logic. |
| I1 [Introduction, `sec:intro`](../paper/introduction.tex) | The sequential checker tracks each binding’s local history. Baseline assignment starts a fresh history, calls update only the receiver and require viability, and each binding must complete before it is discarded or the program exits. | [`check_step_sound`](#declaration-check-step-sound), [`check_step_complete`](#declaration-check-step-complete), [`check_stmt_spec`](#declaration-check-stmt-spec) | PROVEN | See the primitive-rule comparison below. Completion of a single alias does not discharge other bindings. |
| I2 [Introduction, `sec:intro`](../paper/introduction.tex) | For any nonempty regular shuffle-closed protocol, accepted programs are safe at every execution prefix, and all allocated objects have complete histories at termination, including unreachable objects. | [`typestate_prefix_sound`](#declaration-typestate-prefix-sound), [`typestate_completion_sound`](#declaration-typestate-completion-sound) | PROVEN, scoped | The quantified locations satisfy l < next_loc m, with no reachability restriction. |
| I3 [Introduction, `sec:intro`](../paper/introduction.tex) | Shuffle closedness is necessary for the stated discipline, which accepts every locally valid history. | [`completion_sound_requires_certified`](#declaration-completion-sound-requires-certified) | PROVEN, scoped | The converse constructs a baseline two-binding client for arbitrary complete histories and their chosen interleaving. It concerns this fixed checker, not every checker without alias information. |
| I4 [Introduction, `sec:intro`](../paper/introduction.tex) | Pumping closure preserves regularity for arbitrary regular seed languages. An exact condition on seeds yields a terminating certification procedure with counterexamples given by seed histories and their interleavings. | [`pumping_closure_regular_regex`](#declaration-pumping-closure-regular-regex), [`certify_regex_spec`](#declaration-certify-regex-spec), [`regex_counterexample_complete`](#declaration-regex-counterexample-complete), [`regex_counterexample_none`](#declaration-regex-counterexample-none), [`regex_counterexample_sound`](#declaration-regex-counterexample-sound), [`shuffle_candidates_spec`](#declaration-shuffle-candidates-spec), [`counterexample` selection and `List.find_some`](#declaration-counterexample-selection) | PROVEN, including a consequence of the selection definition | The returned histories belong to the normalized seed corpus by List.find_some and shuffle_candidates_spec. The exported regex_counterexample_sound signature states only membership in the pumping closure. Regular inputs and an inhabited finite alphabet are required; the mathematical empty-alphabet case is discussed separately. |
| I5 [Introduction, `sec:intro`](../paper/introduction.tex) | For selected classes, assignment may inherit the source history under a stronger certificate for composing continuations. This optional rule preserves prefix safety and all-object completion. | [`copy_step_spec`](#declaration-copy-step-spec), [`copying_program_prefix_sound`](#declaration-copying-program-prefix-sound), [`copying_program_completion_sound`](#declaration-copying-program-completion-sound), [`certify_copying_regex_spec`](#declaration-certify-copying-regex-spec) | PROVEN, scoped | copying_certified requires ordinary shuffle closure for every class and residual shuffle closure for enabled classes. Allocation and field loading stay fresh. Target retirement is still required. |
| I6 [Introduction, `sec:intro`](../paper/introduction.tex) | Interpreting safe histories as extendible to completion connects accumulation to composition of continuations. The accumulation condition and a separate completion condition imply the certificates for both modes. A shuffle-closed protocol violates the accumulation condition, giving a language-level separation. | [`kellogg_error_closed_iff_residual_prefix_shuffle_closed`](#declaration-kellogg-error-closed-iff-residual-prefix-shuffle-closed), [`kellogg_regular_certificates`](#declaration-kellogg-regular-certificates), [`kellogg_protocol_copying_certified`](#declaration-kellogg-protocol-copying-certified), [`separating_certified_not_kellogg`](#declaration-separating-certified-not-kellogg) | PROVEN, scoped | Completion stability is a distinct sufficient premise. The safety equivalence concerns derivatives of prefix_language K, not derivatives of K. |
| I7 [Introduction, contribution 1, `sec:intro`](../paper/introduction.tex) | The first contribution is an independent-reference typestate system, its exact protocol condition, prefix-safety and completion guarantees, and an optional history-inheritance rule. | [`typestate_prefix_sound`](#declaration-typestate-prefix-sound), [`typestate_completion_sound`](#declaration-typestate-completion-sound), [`copying_program_prefix_sound`](#declaration-copying-program-prefix-sound), [`copying_program_completion_sound`](#declaration-copying-program-completion-sound) | PROVEN, scoped | The direct source calculus, baseline necessity, automatic bulk exit, expression representations in both modes, and ghost/surface simulation are proved. Ordinary initialization and termination remain separate. |
| I8 [Introduction, contribution 2, `sec:intro`](../paper/introduction.tex) | The second contribution constructs certified protocols from regular seed specifications through regularity-preserving pumping closure and an exact, terminating seed criterion that returns counterexamples on failure. | [`pumping_normalize_correct`](#declaration-pumping-normalize-correct), [`pumping_closure_regular_regex`](#declaration-pumping-closure-regular-regex), [`seed_shuffle_coveredP`](#declaration-seed-shuffle-coveredP), [`base_shuffle_coveredP`](#declaration-base-shuffle-coveredP), [`certify_regex_spec`](#declaration-certify-regex-spec), [`regex_counterexample_complete`](#declaration-regex-counterexample-complete), [`regex_counterexample_none`](#declaration-regex-counterexample-none), [`regex_counterexample_sound`](#declaration-regex-counterexample-sound) | PROVEN | The signature restrictions on alphabets and seed predicates are listed below. |
| I9 [Introduction, contribution 3, `sec:intro`](../paper/introduction.tex) | The third contribution connects accumulation analysis to both checking modes through sufficient safety and completion conditions, and gives a certified protocol outside the accumulation condition. | [`kellogg_program_prefix_sound`](#declaration-kellogg-program-prefix-sound), [`kellogg_program_completion_sound`](#declaration-kellogg-program-completion-sound), [`separating_certified_not_kellogg`](#declaration-separating-certified-not-kellogg) | PROVEN, scoped | The connection is semantic, under the extracted first-error interpretation and separate completion premise. |
| I10 [Introduction, contribution 4, `sec:intro`](../paper/introduction.tex) | The fourth contribution mechanizes the language constructions, certificates, accumulation connection, and core checker soundness in Rocq, with details in the Mechanization section. | [`pumping_normalize_correct`](#declaration-pumping-normalize-correct), [`certify_regex_spec`](#declaration-certify-regex-spec), [`kellogg_regular_certificates`](#declaration-kellogg-regular-certificates), [`regular_program_completion_sound`](#declaration-regular-program-completion-sound) | PROVEN | The cited Rocq modules implement this chain. |
| M1 [Mechanization, `sec:mechanization`](../paper/mechanization.tex) | The development verifies language constructions, finite certificates and rejection witnesses, the accumulation bridge, and both checker modes, connecting successful certification and checking to safety and completion. | [`pumping_normalize_correct`](#declaration-pumping-normalize-correct), [`certify_regex_spec`](#declaration-certify-regex-spec), [`regex_counterexample_sound`](#declaration-regex-counterexample-sound), [`accumulation_contract_residual_shuffle_closed`](#declaration-accumulation-contract-residual-shuffle-closed), [`regular_program_prefix_sound`](#declaration-regular-program-prefix-sound), [`regular_program_completion_sound`](#declaration-regular-program-completion-sound), [`copying_regular_program_prefix_sound`](#declaration-copying-regular-program-prefix-sound), [`copying_regular_program_completion_sound`](#declaration-copying-regular-program-completion-sound) | PROVEN, scoped | Regular-seed certification discharges the protocol premises for the fixed core checkers. Initialization progress and termination remain outside the guarantees. |
| M2 [Mechanization, `sec:mechanization`](../paper/mechanization.tex) | The executable checkers agree with the declarative rules and have proved correspondences to regular-expression qualifiers and surface semantics. | [`check_stmt_spec`](#declaration-check-stmt-spec), [`copy_step_spec`](#declaration-copy-step-spec), [`regular_residual_program_correspondence`](#declaration-regular-residual-program-correspondence), [`copying_regular_residual_program_correspondence`](#declaration-copying-regular-residual-program-correspondence), [`ghost_surface_execution`](#declaration-ghost-surface-execution), [`surface_ghost_execution`](#declaration-surface-ghost-execution) | PROVEN, scoped | Expression correspondences use related environments and a correct initial expression per class. Ghost/surface simulation uses an injective location renaming and extensional map observations. |
| M3 [Mechanization, `sec:mechanization`](../paper/mechanization.tex), formerly I11 | The principal construction, certification, and client-soundness theorems require no additional axioms. | [audit.v](audit.v), [assumption-audit instructions](README.md) | PROVEN for audited results | See the trust boundary below. Generalized protocol/certification hypotheses remain explicit inputs. Optional minimal-corpus results use classical logic and are outside the audited dependency closure. |
| M4 [Mechanization, `sec:mechanization`](../paper/mechanization.tex), formerly part of I12 | The development builds on Mathematical Components and RegLang. | [dependency and build instructions](README.md), [artifact guide](../paper/ARTIFACT_README.md) | SOURCE/BUILD FACT | RegLang is bundled. [_CoqProject](_CoqProject) lists sources and [audit.v](audit.v) lists audited declarations. `coqwc *.v` reproduces the current project definition/proof line count, excluding comments and bundled RegLang. Size is not a mathematical theorem. |
| C1 [Conclusion, `sec:conclusion`](../paper/body.tex) | Candidate protocols are constructed from representative seed specifications and certified by a finite procedure with counterexamples on failure. | [`pumping_closure_regular_regex`](#declaration-pumping-closure-regular-regex), [`certify_regex_spec`](#declaration-certify-regex-spec), [`regex_counterexample_complete`](#declaration-regex-counterexample-complete), [`regex_counterexample_sound`](#declaration-regex-counterexample-sound) | PROVEN | Same regular-language and alphabet scope as A4. Certification, rather than construction alone, establishes shuffle closure. |
| C2 [Conclusion, `sec:conclusion`](../paper/body.tex) | Permitted complete histories must remain permitted when interleaved for the fresh-history discipline to check shared objects reference by reference. Accepted programs preserve viable object histories throughout execution and complete them at normal termination. | [`typestate_prefix_sound`](#declaration-typestate-prefix-sound), [`typestate_completion_sound`](#declaration-typestate-completion-sound), [`completion_sound_iff_certified`](#declaration-completion-sound-iff-certified), [`copying_program_prefix_sound`](#declaration-copying-program-prefix-sound), [`copying_program_completion_sound`](#declaration-copying-program-completion-sound) | PROVEN for the core | The necessary-and-sufficient condition concerns the fixed fresh-history checker and raw all-object completion soundness. Both modes have the stated prefix and final guarantees under their respective certificates; completed execution remains a premise. |
| C3 [Conclusion, `sec:conclusion`](../paper/body.tex) | Stronger protocol conditions allow progress to be inherited at assignment. | [`certify_residuals_spec`](#declaration-certify-residuals-spec), [`copying_program_prefix_sound`](#declaration-copying-program-prefix-sound), [`copying_program_completion_sound`](#declaration-copying-program-completion-sound) | PROVEN | Every reachable derivative must be shuffle closed. The certificate includes the initial derivative; empty derivatives satisfy closure vacuously. Allocation and field loads remain fresh. |
| C4 [Conclusion, `sec:conclusion`](../paper/body.tex) | The paper relates both checking modes to accumulation analysis and exhibits a protocol that supports fresh histories but violates the accumulation condition. | [`kellogg_error_closed_iff_residual_prefix_shuffle_closed`](#declaration-kellogg-error-closed-iff-residual-prefix-shuffle-closed), [`kellogg_protocol_copying_certified`](#declaration-kellogg-protocol-copying-certified), [`kellogg_program_prefix_sound`](#declaration-kellogg-program-prefix-sound), [`kellogg_program_completion_sound`](#declaration-kellogg-program-completion-sound), [`separating_certified_not_kellogg`](#declaration-separating-certified-not-kellogg) | PROVEN, scoped | The equivalence concerns accumulation safety for viable prefixes. The bridge to complete histories also assumes completion stability. The separating witness compares protocol languages, not accepted client programs or implementations. |
| C5 [Conclusion, `sec:conclusion`](../paper/body.tex) | The Rocq mechanization verifies the constructions and soundness results. | M1–M3 above | PROVEN, scoped | This summarizes the verified results with their stated model, representation, and trust boundaries; it does not assert readiness as a reusable software library. |

### Numbered formal results

Statements below reproduce the named results, omitting their labels and
normalizing line breaks for the table.

| Paper result and statement (LaTeX, with line breaks normalized) | Mechanized evidence | Verdict | Exact scope or gap |
| --- | --- | --- | --- |
| [lem:context](../paper/regularity.tex)<br>If $s\pumpsto^*u$ and $t\pumpsto^*v$, then $st\pumpsto^*uv$.<br>In particular, a pumping derivation remains valid after adding a common prefix or suffix on both sides. | [`pumping_closure_cat`](#declaration-pumping-closure-cat) | PROVEN | Concatenation is compatible with pumping. This does not assert distribution of pumping closure over concatenation. |
| [lem:singleton](../paper/regularity.tex)<br>For every seed $s$, $\denote{C(s)}=\pc{\set{s}}$. | [`pumping_closure_singleton_correct`](#declaration-pumping-closure-singleton-correct) | PROVEN | Repeated seed milestones remain distinct occurrences. The formal representation takes char:finType and d0:char. |
| [lem:star-basis](../paper/regularity.tex)<br>For every regular expression $r$ over $\Sigma$, with $k=&#124;\Sigma&#124;$, $\pc{\denote{r^*}}=\pc{\denote{B_k(r)}}$. | [`pumping_closure_star_finite_basis`](#declaration-pumping-closure-star-finite-basis) | PROVEN | bounded_star_basis uses the alphabet cardinality, bounding factor count rather than factor lengths. |
| [thm:normalization](../paper/regularity.tex)<br>For every regular expression $r$, $F(r)$ is finite and<br>\[<br>\pc{\denote{r}}=\pc{F(r)}.<br>\] | [`eliminate_star_correct`](#declaration-eliminate-star-correct), [`eliminate_star_star_free`](#declaration-eliminate-star-star-free), [`star_free_finite`](#declaration-star-free-finite), [`words_of_star_free_correct`](#declaration-words-of-star-free-correct), [`pumping_normalize_correct`](#declaration-pumping-normalize-correct) | PROVEN | F(r) is represented by words_of_star_free (eliminate_star r). Closure equality, not equality of original seed languages or minimality, is proved. |
| [thm:regularity](../paper/appendix.tex)<br>Algorithm~\ref{alg:construct} terminates on every regular expression $r$ and returns a finite set $F$ and a regular expression $P$ such that<br>\[<br>F=F(r),\qquad \denote{P}=\pc{F}=\pc{\denote{r}}.<br>\]<br>Consequently, pumping closure preserves regularity. | [`pumping_closure_regular_regex`](#declaration-pumping-closure-regular-regex), [`closure_regex_correct`](#declaration-closure-regex-correct), [`pumping_normalize_correct`](#declaration-pumping-normalize-correct) | PROVEN | Total enumeration and closure_regex provide the finite witness and expression. The regularity theorem alone states existence of a recognizing automaton. Empty alphabet remains a paper-level edge case of the default-symbol representation. |
| [lem:pump-shuffle](../paper/shuffle.tex)<br>If $u\pumpsto u'$ and $\interleave{u'}{v}{w'}$, there exists $w$ such that $\interleave{u}{v}{w}$ and $w\pumpsto w'$.<br>The symmetric statement holds for a step in the right input. | [`pumping_interleaving_left`](#declaration-pumping-interleaving-left), [`pumping_interleaving_right`](#declaration-pumping-interleaving-right) | PROVEN | The removed occurrence retains an earlier source occurrence, not merely the same symbol somewhere in the word. |
| [lem:factorization](../paper/shuffle.tex)<br>If $s\pumpsto^*u$, $t\pumpsto^*v$, and $\interleave{u}{v}{w}$, then<br>\[<br>\exists z.\ \interleave{s}{t}{z}\ \land\ z\pumpsto^*w.<br>\] | [`seed_cover_interleaving_factor`](#declaration-seed-cover-interleaving-factor) | PROVEN | The output interleaving of originating seeds pumps to the full output. Original milestones are not discarded. |
| [thm:seed-criterion](../paper/shuffle.tex)<br>For every seed language $S$,<br>\[<br>\text{$S$ satisfies the seed-shuffle condition}<br>\quad\Longleftrightarrow\quad<br>\text{$\pc{S}$ is shuffle closed}.<br>\] | [`seed_shuffle_coveredP`](#declaration-seed-shuffle-coveredP), [`base_shuffle_coveredP`](#declaration-base-shuffle-coveredP) | PROVEN, scoped | seed_shuffle_coveredP covers arbitrary Prop-valued seed languages via covered_by. base_shuffle_coveredP connects Boolean seed predicates to the inductive pumping closure. Both use the inhabited finite alphabet disclosed in the paper. The empty-alphabet case is paper-level. |
| [thm:decision](../paper/appendix.tex)<br>Applied to $F(r)$, Algorithm~\ref{alg:certify} terminates and accepts exactly when $\pc{\denote{r}}$ is shuffle closed.<br>On rejection, its result $(u,v,z)$ satisfies<br>\[<br>u,v\in F(r),\qquad<br>\interleave{u}{v}{z},\qquad z\notin\pc{\denote{r}}.<br>\] | [`certify_seeds_spec`](#declaration-certify-seeds-spec), [`certify_regex_spec`](#declaration-certify-regex-spec), [`regex_counterexample_complete`](#declaration-regex-counterexample-complete), [`regex_counterexample_none`](#declaration-regex-counterexample-none), [`regex_counterexample_sound`](#declaration-regex-counterexample-sound), [`shuffle_candidates_spec`](#declaration-shuffle-candidates-spec), [`counterexample` selection and `List.find_some`](#declaration-counterexample-selection) | PROVEN, including a consequence of the selection definition | certify_regex is Boolean; regex_counterexample is its separate total diagnostic function. Witness absence agrees with success, and rejection yields a witness. Seed membership follows from unfolding regex_counterexample/counterexample, applying List.find_some, and then shuffle_candidates_spec. The exported regex_counterexample_sound signature gives the weaker closure-membership statement for the two inputs, together with interleaving and output rejection. |
| [lem:prefix-shuffle](../paper/typestate.tex)<br>If $K$ is shuffle closed, then $\pref{K}$ is shuffle closed. | [`prefix_shuffle_closed`](#declaration-prefix-shuffle-closed), [`tagged_shuffle_closed`](#declaration-tagged-shuffle-closed) | PROVEN | Finite composition requires a nonempty set of component histories, so no premise K [] is needed. |
| [lem:local](../paper/typestate.tex)<br>Let $s$ be an ordinarily well-typed program satisfying $\vdash_{\mathrm{prog}}s$.<br>If $\langle M,s'\rangle$ is reachable from the initial configuration of $s;\code{finish}$, then some $\Gamma$ with $\operatorname{dom}(\Gamma)=\operatorname{dom}(\rho)$ satisfies $\checkstmt{\Gamma}{s'}{\emptyset}$ and:<br>\begin{enumerate}<br>\item If $x$ is live in epoch $e$, $\rho(x)=\lambda(e)$ and $\Gamma(x)=(\kappa(\lambda(e)),R)$ with $\denote{R}=t_e^{-1}K_{\kappa(\lambda(e))}\neq\emptyset$.<br>\item Every retired epoch $e$ has $t_e\in K_{\kappa(\lambda(e))}$.<br>\end{enumerate} | [`preservation`](#declaration-preservation), [`execution_preservation`](#declaration-execution-preservation), [`residual_snoc`](#declaration-residual-snoc), [`residual_nullable`](#declaration-residual-nullable), [`reachable_residual_configuration`](#declaration-reachable-residual-configuration) | PROVEN for the residual configuration invariant | Configuration preservation retains one environment typing the residual statement, class/heap agreement, viable live histories, and completed retired histories. The baseline expression correspondence and bulk-clear invariant connect this representation to the paper. Initialization safety remains separate. |
| [lem:object-shuffle](../paper/typestate.tex)<br>At every runtime prefix and allocated location $\ell$, its history $h(\ell)$ is an interleaving of the histories of all epochs $e$ such that $\lambda(e)=\ell$, including retired epochs. | [`project_partition`](#declaration-project-partition), [`tagged_shuffle_closed`](#declaration-tagged-shuffle-closed), [`invariant_object_language`](#declaration-invariant-object-language) | PROVEN for fresh histories | object_history is the erasure of the relevant tagged events. Every allocated location has an epoch, including after bindings disappear. There is no separate n-ary shuffle relation. The projection theorem supplies the exact composition fact. |
| [thm:typestate](../paper/typestate.tex)<br>Let every class protocol $K_C$ be regular and shuffle closed.<br>If an ordinarily well-typed source program $s$ satisfies $\vdash_{\mathrm{prog}}s$, then every execution of $s;\code{finish}$ from the initial state has the following properties:<br>\begin{enumerate}<br>\item It never reaches $\mathsf{error}$.<br>\item At every execution prefix and allocated location $\ell$, $h(\ell)\in\pref{K_{\kappa(\ell)}}$.<br>\item On normal termination, every allocated object has a complete history: $h(\ell)\in K_{\kappa(\ell)}$, including objects no longer reachable from variables or fields.<br>\end{enumerate} | [`typestate_prefix_sound`](#declaration-typestate-prefix-sound), [`typestate_completion_sound`](#declaration-typestate-completion-sound), [`baseline_runtime_no_error`](#declaration-baseline-runtime-no-error), [`baseline_runtime_equivalence`](#declaration-baseline-runtime-equivalence) | PROVEN, scoped | The source checker inserts bulk exit and has a baseline expression-rule correspondence. Bidirectional ghost/surface simulation transfers all-object properties. Nonemptiness is checked when a binding starts. The results quantify over executable prefixes and completed runs; initialization safety and termination are not conclusions. |
| [prop:necessary](../paper/typestate.tex)<br>If arbitrary pairs of complete local histories from $K$ must combine into a complete object history under every interleaving, then $K$ must be shuffle closed. | [`completion_sound_requires_certified`](#declaration-completion-sound-requires-certified), [`completion_sound_iff_certified`](#declaration-completion-sound-iff-certified) | PROVEN for the baseline core | The formal converse turns raw completion soundness for every accepted baseline core program and execution into certified P. Its proof builds the two-binding client for arbitrary complete histories and a chosen interleaving. No converse for other analyses or the optional copying mode is asserted. |
| [cor:certified-typestate](../paper/appendix.tex)<br>If Algorithms~\ref{alg:construct} and~\ref{alg:certify} construct and certify every class protocol, an ordinarily well-typed source program accepted by the client checker has the guarantees of Theorem~\ref{thm:typestate}. | [`regular_family_certified`](#declaration-regular-family-certified), [`regular_program_prefix_sound`](#declaration-regular-program-prefix-sound), [`regular_program_completion_sound`](#declaration-regular-program-completion-sound) | PROVEN, scoped | The compiled regular-seed family is certified and composed with the source checker over a finite inhabited alphabet. regular_residual_program_correspondence connects baseline acceptance to the expression rules, including bulk exit. Nonemptiness remains a binding check; initialization progress and termination are not conclusions. |
| [thm:copying-soundness](../paper/typestate.tex)<br>Assume every class protocol is regular and shuffle closed, and every opted-in class satisfies Equation~\eqref{eq:residual-shuffle}.<br>An ordinarily well-typed program satisfying the program judgment with the optional assignment rule has all guarantees of Theorem~\ref{thm:typestate}. | [`copying_program_prefix_sound`](#declaration-copying-program-prefix-sound), [`copying_program_completion_sound`](#declaration-copying-program-completion-sound), [`copying_regular_program_prefix_sound`](#declaration-copying-regular-program-prefix-sound), [`copying_regular_program_completion_sound`](#declaration-copying-regular-program-completion-sound), [`copying_runtime_no_error`](#declaration-copying-runtime-no-error), [`copying_runtime_equivalence`](#declaration-copying-runtime-equivalence) | PROVEN for the history-based source checker | The result uses copying_certified, including nested and mixed copying, with structural execution and automatic bulk exit. It transfers through the common raw ghost/surface correspondence. copying_residual_program_correspondence connects its acceptance to expression rules that inherit the source residual. Initialization and termination remain outside the result. |
| [thm:accumulation-prefix](../paper/typestate.tex)<br>Let $K$ be a regular language and $P=\pref{K}$.<br>Equation~\eqref{eq:accumulation-error} holds if and only if every derivative $p^{-1}P$ is shuffle closed. | [`kellogg_error_closed_iff_residual_prefix_shuffle_closed`](#declaration-kellogg-error-closed-iff-residual-prefix-shuffle-closed) | PROVEN | The Rocq theorem permits any Prop-valued language K over any Type with an explicit decision procedure for prefix_language K. Regularity supplies that decision procedure for the paper's instance. No classical axiom supplies it. |
| [thm:accumulation-bridge](../paper/typestate.tex)<br>If $K$ is an accumulation contract, every derivative $p^{-1}K$ is shuffle closed.<br>In particular, $K$ is shuffle closed. | [`accumulation_contract_residual_shuffle_closed`](#declaration-accumulation-contract-residual-shuffle-closed), [`accumulation_contract_shuffle_closed`](#declaration-accumulation-contract-shuffle-closed) | PROVEN | The positive safe-extension law and completion stability form accumulation_contract. No regularity, finite alphabet, or decidability premise is needed for this implication. |

The monitored conclusions also compose with the compiled and accumulation
entry points. Unfolding `check_regular_program` supplies core acceptance and,
through `compiled_family_certified`, the certificate required by
`baseline_runtime_no_error` and `baseline_runtime_equivalence`. Unfolding
`check_regular_program_with_copy` supplies copying-checker acceptance and,
through `copying_table_sound`, the certificate required by
`copying_runtime_no_error` and `copying_runtime_equivalence`.
`kellogg_protocol_copying_certified` supplies the same certificate under the
accumulation premises. The `cor:certified-typestate` and copying/Kellogg rows
use these compositions for their monitored conclusions; no additional
specialized monitor theorem is claimed.

### Protocol-pattern families

This section links the examples in [Protocol patterns (`sec:protocol-patterns`)](../paper/discussion.tex)
to the general family theory retained in the artifact. The paper presents names,
code illustrations, and concrete protocols; the artifact also covers arbitrary
thresholds, monotone prerequisite predicates, and finite sets of capacity names.
The source links below identify the definitions and proofs directly; they do
not add reconstructed signatures to the verbatim declaration index.

The manuscript abbreviates ordered events `t,i,r` as `a,b,c` and service
events `t,w,c,q` as `a,b,c,d`. These are changes of event names: the
source seeds and theorems below retain their mnemonic names.

| Claim | Source declarations | Verdict and boundary |
| --- | --- | --- |
| Artifact support: guarded monotone, inflationary state updates with upward-closed acceptance give pumping closure and shuffle-closed derivatives. | [monotone_protocols.v](monotone_protocols.v): `monotone_machine`, `machine_run`, `machine_language`, `machine_language_residual_shuffle_closed`, `machine_language_repeat`; [monotone_pumping.v](monotone_pumping.v): `machine_language_pumping` | PROVEN. Enabled events remain enabled at larger states, and an accepted continuation can be replayed from a larger state. Generic shuffle/repetition results do not require finite state spaces. |
| A finite persistent machine has an exact regular seed representation and passes both certificates. | [monotone_regular.v](monotone_regular.v): `machine_dfa_language`, `finite_machine_language_regular`, `finite_machine_regular_family_language`, `finite_machine_seed_certificate`, `finite_machine_copying_certificate` | PROVEN for finite alphabets and states with Boolean guard/acceptance queries and their specifications. The pumping representation additionally takes a default event. Disabled transitions enter a rejecting sink. |
| Ordered milestones require first occurrences `t`, `i`, `r` in order, and later occurrences preserve established permissions. | [milestone_service_patterns.v](milestone_service_patterns.v): `milestone_family`, `milestone_copying_certified`, `milestone_pumping`, `milestone_accumulation_contract`; [milestone_service_seeds.v](milestone_service_seeds.v): `milestone_displayed_seeds_exact` | PROVEN for the concrete three-event instance and all words. The language is exactly `PC({tir})`; completion requires `r`. Both assignment modes and the extracted accumulation contract hold. This is not a parameterized theorem for arbitrary dependency graphs. |
| Independent services require `t` before `w` and `c` before `q`, and both queries for completion. | [milestone_service_patterns.v](milestone_service_patterns.v): `service_family`, `service_copying_certified`, `service_pumping`, `service_accumulation_contract`; [milestone_service_seeds.v](milestone_service_seeds.v): `service_displayed_seeds_exact` | PROVEN for the concrete four-event instance and all words. The language is exactly `PC({twcq,tcwq,tcqw,ctwq,ctqw,cqtw})`. Its residuals are shuffle closed and it satisfies accumulation; it does not establish a separation from accumulation. |
| A finite monotone machine with a common completing suffix supplies exact executable queries and checker guarantees. | [persistent_pattern_queries.v](persistent_pattern_queries.v): `persistent_viable_spec`, `persistent_language_regular`, `persistent_copying_certified`, `persistent_pumping`, `persistent_accumulation_contract`, `persistent_checked_prefix`, `persistent_checked_completion` | PROVEN under Boolean guard/acceptance specifications and a suffix that completes every machine state. The two concrete machines discharge these hypotheses constructively. |
| The ordered client checks successfully; an inherited service client completes the actual object history. | [milestone_service_examples.v](milestone_service_examples.v): `milestone_client_accepted`, `milestone_out_of_order_rejected`, `service_alias_client_accepted`, `service_alias_client_needs_inheritance`, `service_both_queries_required`, `service_alias_terminates`, `service_alias_object_history`, `service_alias_completion` | PROVEN for explicit core clients. Both service aliases have local histories `twcq`; their shared object records `twwccqq`. The same client without inheritance is rejected, and using only one service does not complete the protocol. |
| Persistent prerequisites cover any satisfiable monotone Boolean predicate on a finite set of established features. | [prerequisite_patterns.v](prerequisite_patterns.v): `prerequisite_spec`, `prerequisite_protocol`, `prerequisite_viable_spec`, `prerequisite_protocol_copying_certified`, `prerequisite_language_regular`, `prerequisite_regular_family_exact` | PROVEN. `prerequisite_spec` includes a satisfying witness. A setter establishes one feature; a use checks the predicate and records completion. At least one use is required. |
| All-of and any-of prerequisites are instances; their two-feature languages equal the pumping closures of the example seeds. | [prerequisite_patterns.v](prerequisite_patterns.v): `all_prerequisites`, `any_prerequisites`; [prerequisite_examples.v](prerequisite_examples.v): `builder_displayed_seeds_exact`, `alternative_displayed_seeds_exact`; [certification.v](certification.v): `coveredb_spec` | PROVEN. The example seeds are `{abu,bau}` and `{au,bu,abu,aub,bau,bua}` respectively. The exact theorems equate coverage and protocol acceptance for every word; `coveredb_spec` converts coverage to pumping closure. The any-of required set must be nonempty. |
| An inherited builder client is accepted and completes its actual object history; completing one alias does not discharge another. | [prerequisite_examples.v](prerequisite_examples.v): `builder_alias_client_accepted`, `builder_alias_client_needs_inheritance`, `builder_source_obligation_remains`, `builder_alias_terminates`, `builder_alias_object_history`, `builder_alias_completion` | PROVEN for the explicit core client. Its local inherited histories share the first setter, while its actual history contains that event once. The module checks acceptance, rejection controls, a terminating execution, and the object history. |
| Count-threshold protocols require at least `N` increments before every use and at least one use for completion, for arbitrary natural `N`. | [threshold_patterns.v](threshold_patterns.v): `threshold_family`, `threshold_queries`, `threshold_language_shape`, `threshold_copying_certified`, `threshold_post_use_operations_accepted`; [threshold_examples.v](threshold_examples.v): `threshold_finite_language`, `threshold_regular`, `threshold_regular_family_exact` | PROVEN. The finite representation saturates the counter at `N`; repeats and further increments remain permitted after a use. Threshold zero is included. |
| The positive-threshold language is exactly `PC({a^N u})`; threshold zero is exactly `PC({u,au,ua})`. | [threshold_examples.v](threshold_examples.v): `threshold_singleton_seed_exact`, `threshold_zero_seeds_exact` | PROVEN for arbitrary words. The singleton equality requires `N > 0`; the separate zero-threshold corpus admits increments before or after a use. |
| Threshold checking distinguishes counts with the same event set and supports aliasing clients in both modes. | [threshold_patterns.v](threshold_patterns.v): `threshold_counts_not_sets`, `threshold_aliases_accepted`, `threshold_inherited_aliases_accepted`, `threshold_inherited_aliases_need_inheritance`, `threshold_inherited_aliases_terminate`, `threshold_inherited_object_history`, `threshold_aliases_sound`, `threshold_inherited_aliases_sound` | PROVEN. At threshold two, one increment and two increments have different next-use permissions. The inherited client has an explicit terminating execution and exact object history. |
| Reusable capacity requires every prefix to use no more distinct identities than its capacity additions and requires at least one use for completion. | [capacity_patterns.v](capacity_patterns.v): `capacity_safeP`, `capacity_complete`, `capacity_viable_spec`, `capacity_certified`, `capacity_regular` | PROVEN over a finite identity type. The executable family takes a default identity to witness completion. Repeated use of an existing identity needs no additional capacity; an invalid prefix cannot be repaired by later additions. |
| The directly evaluable capacity queries implement the same semantic family. | [capacity_patterns.v](capacity_patterns.v): `capacity_scan_correct`, `capacity_safe_query_correct`, `capacity_complete_query_correct`, `capacity_executable_certified` | PROVEN for every word. A duplicate-free list represents occupied identities; its length equals the semantic set cardinality. The checked clients use these refined queries. |
| Reusable capacity passes basic certification but fails residual closure and the extracted accumulation error law when two distinct identities exist. | [capacity_patterns.v](capacity_patterns.v): `capacity_not_residual`, `capacity_not_kellogg`, `capacity_certified_not_kellogg` | PROVEN under the explicit distinct-identity hypothesis. After one capacity addition, either identity can be used separately, but the two distinct uses cannot be composed without another addition. This is a protocol-language separation. |
| For two identities, the capacity language is exactly the pumping closure of `{ab,ac,aabc,abac,aacb,acab}`. | [capacity_seed_patterns.v](capacity_seed_patterns.v): `capacity_six_seeds_exact`, `capacity_separating_family_exact`; [pattern_seed_automata.v](pattern_seed_automata.v): `finite_seed_automaton_correct`, `pattern_dfa_simulation_correct`; [capacity_seed_table.v](capacity_seed_table.v) | PROVEN for arbitrary words. Rocq checks every transition of the generated frontier table and its simulation into the independently defined capacity DFA. The generator is untrusted. |
| Basic capacity clients preserve the prefix budget and complete every allocated object's history. | [capacity_patterns.v](capacity_patterns.v): `capacity_program_prefix_sound`, `capacity_program_completion_sound`, `capacity_alias_client_accepted`, `capacity_alias_client_terminates`, `capacity_alias_actual_history`, `capacity_overdraw_client_rejected`, `capacity_unfinished_alias_client_rejected`, `capacity_late_allocation_rejected` | PROVEN for checked core programs and existing executions. Explicit positive and negative clients rule out empty-language and final-count-only interpretations. |
| SQLite schema operations, the selected `ImageWriteParam` fragment, and the earlier prerequisite/counting APIs illustrate the protocol patterns. | [Protocol-pattern API descriptions and citations](../paper/discussion.tex) | UNMECHANIZED API interpretation. The artifact verifies the event languages and core clients, not library bodies or a translation of SQL/Java programs into the calculus. The service example fixes explicit modes and valid settings; its two-query completion condition is a client policy. Ordinary parameter validity and the selected operation fragments remain part of the interpretation. |

The [reproduction instructions](README.md#verified-protocol-patterns) show how
to regenerate the capacity and milestone/service tables into `/tmp` and compare
them with the checked sources. Each generator output is a candidate certificate; the transition and
acceptance proofs establish its correctness.

### Exact-language protocol inputs

The discussion's claim that the system can enforce `K_last` unchanged is
exercised by an exact-input route. These adapters take the protocol language
itself; the regular-seed wrappers instead take its pumping closure. Client
acceptance still requires a separately established shuffle-closure premise
for soundness. The concrete certificate below is derived from a structural
proof, rather than by running the product-automaton enumerator.

| Claim or artifact interface | Exact declarations | Scope |
| --- | --- | --- |
| Exact DFA acceptance and viable prefixes | [`exact_dfa_family_language`](#declaration-exact-dfa-family-language), [`exact_dfa_family_viable`](#declaration-exact-dfa-family-viable) | PROVEN for the supplied DFA language, without pumping. |
| Exact regex interpretation and shuffle certification | [`exact_regex_family_language`](#declaration-exact-regex-family-language), [`certify_exact_regex_spec`](#declaration-certify-exact-regex-spec) | PROVEN through the existing regex-to-DFA correctness theorem. |
| Exact protocol certification implies client completion in that language | [`exact_dfa_program_completion_sound`](#declaration-exact-dfa-program-completion-sound) | PROVEN for accepted clients and completed executions, with a certificate for every class. |
| `K_last = u {u,b}* b` is enforced unchanged | [`k_last_exact_language`](#declaration-k-last-exact-language), [`k_last_shuffle_closed`](#declaration-k-last-shuffle-closed), [`k_last_exact_certificate`](#declaration-k-last-exact-certificate) | PROVEN for all words; `false` encodes `u` and `true` encodes `b`. |
| Executable example queries match the exact DFA adapter | [`k_last_exact_dfa_queries`](#declaration-k-last-exact-dfa-queries) | PROVEN acceptance and viability equality for every class and word; transparent queries avoid the library's locked finite-set representation. |
| A completed `ubub` client is accepted and an `ubu` client is rejected | [`k_last_complete_client_accepted`](#declaration-k-last-complete-client-accepted), [`k_last_incomplete_client_rejected`](#declaration-k-last-incomplete-client-rejected), [`k_last_complete_client_terminates`](#declaration-k-last-complete-client-terminates), [`k_last_client_completion_sound`](#declaration-k-last-client-completion-sound) | PROVEN with an explicit terminating witness. `ubu` remains a viable prefix, but is not complete. |
| Pumping the seed changes this completion policy | [`ub_seed_accepts_ubu`](#declaration-ub-seed-accepts-ubu), [`k_last_not_pumping_closed`](#declaration-k-last-not-pumping-closed) | PROVEN; distinguishes the two interfaces without changing either one's semantics. |

## Interfaces and supporting results from the artifact guide

These results support the headline chain or clarify examples and implementation
choices. They are not substitutes for the whole-object soundness theorems.

| Interface or claim | Declarations | What the proof establishes |
| --- | --- | --- |
| Exact coverage and the simulated frontier | [`covers_spec`](#declaration-covers-spec), [`covers_simulation_correct`](#declaration-covers-simulation-correct), [`simulation_state_bound`](#declaration-simulation-state-bound) | The direct predicate means singleton pumping reachability. The simulator returns the same result. Each frontier has at most length(seed)+1 states. No machine-time bound is proved. |
| Finite enumeration and diagnostic completeness | [`shuffles_spec`](#declaration-shuffles-spec), [`shuffle_candidates_spec`](#declaration-shuffle-candidates-spec), [`counterexample` selection and `List.find_some`](#declaration-counterexample-selection), [`counterexample_sound`](#declaration-counterexample-sound), [`counterexample_none`](#declaration-counterexample-none), [`regex_counterexample_complete`](#declaration-regex-counterexample-complete), [`regex_counterexample_none`](#declaration-regex-counterexample-none) | Every interleaving is enumerated. The selection definition and candidate-membership lemma establish that both returned input histories belong to the seed corpus; counterexample_sound exports their closure membership and the rejected interleaving. Witness absence agrees with successful certification. |
| Compiled protocol queries | [`closure_regex_correct`](#declaration-closure-regex-correct), [`dfa_viable_spec`](#declaration-dfa-viable-spec), [`regular_family_language`](#declaration-regular-family-language), [`regular_family_certified`](#declaration-regular-family-certified) | Membership agrees with the compiled pumping closure. Viability means existence of a completing suffix. Successful certificates yield protocol-family shuffle closure. |
| Exact baseline protocol condition | [`completion_sound_requires_certified`](#declaration-completion-sound-requires-certified), [`completion_sound_iff_certified`](#declaration-completion-sound-iff-certified) | For the existing baseline checker, all-object completion soundness is equivalent to certified P. This quantifies over all accepted core programs and their executions, rather than assuming the desired composition property as a premise. |
| Exact executable/declarative core checking | [`check_step_sound`](#declaration-check-step-sound), [`check_step_complete`](#declaration-check-step-complete), [`check_stmt_spec`](#declaration-check-stmt-spec) | Both directions connect the executable baseline checker to the core declarative relation. residual_program_correspondence additionally connects baseline source acceptance to the expression rules. |
| Disabling inherited histories | [`fresh_program_unchanged`](#declaration-fresh-program-unchanged) | Setting every flag to false yields exactly the original checker, as equality of Boolean results for every statement. |
| Inherited-history continuation invariant | [`future_safe_copy`](#declaration-future-safe-copy), [`copying_preservation`](#declaration-copying-preservation) | The proof retags hypothetical future events and uses the source residual once. It never shuffles two copies of the shared past. |
| Exact residual certificate | [`certify_residuals_spec`](#declaration-certify-residuals-spec), [`certify_copying_regex_spec`](#declaration-certify-copying-regex-spec) | Reachable DFA states suffice to quantify over all left derivatives. The triple product encodes two accepted continuations and their potentially rejected interleaving. |
| Safe extension versus the extracted negative error law | [`kellogg_error_closed_iff_safe_extension`](#declaration-kellogg-error-closed-iff-safe-extension), [`subsequence_safe_extension_iff_residual_prefix_shuffle_closed`](#declaration-subsequence-safe-extension-iff-residual-prefix-shuffle-closed), [`residual_shuffle_closed_kellogg_error_closed`](#declaration-residual-shuffle-closed-kellogg-error-closed) | The first equivalence requires decidability. The positive-law equivalence and complete-to-prefix implication do not. The latter does not imply completion stability. |
| Persistent calls and completion observations | [`observations_accumulate_iff_contract`](#declaration-observations-accumulate-iff-contract) | The single observation persistence law is equivalent to the two-part accumulation contract. ObserveCompletion is a specification observation, not an emitted runtime event. |
| Semantic premises supply existing certificates | [`kellogg_regular_certificates`](#declaration-kellogg-regular-certificates), [`kellogg_protocol_copying_certified`](#declaration-kellogg-protocol-copying-certified) | Error persistence plus completion stability suffice for both ordinary and residual certificates. No executable test for those new premises is introduced. |
| Executable baseline and copying witnesses | [`aliases_accepted`](#declaration-aliases-accepted), [`aliases_terminates`](#declaration-aliases-terminates), [`aliases_object_history`](#declaration-aliases-object-history), [`inherited_progress_accepted`](#declaration-inherited-progress-accepted), [`inherited_progress_terminates`](#declaration-inherited-progress-terminates), [`inherited_progress_object_history`](#declaration-inherited-progress-object-history) | Accepted clients have explicit full raw executions, with four-event and three-event object histories respectively. The inherited common prefix occurs only once in the latter history. |
| Unreachable-object completion and unguarded errors | [`abandoned_object_accepted`](#declaration-abandoned-object-accepted), [`abandoned_object_terminates`](#declaration-abandoned-object-terminates), [`abandoned_object_unreachable`](#declaration-abandoned-object-unreachable), [`abandoned_object_complete`](#declaration-abandoned-object-complete), [`raw_invalid_call_executes`](#declaration-raw-invalid-call-executes) | A completed object remains covered after its final reference is overwritten. A separate raw client executes an invalid event and reaches a nonviable history, ruling out a semantics that excludes errors by definition. |
| An inhabited accumulation contract | [`two_calls_accumulation_contract`](#declaration-two-calls-accumulation-contract), [`inherited_progress_sound_via_accumulation`](#declaration-inherited-progress-sound-via-accumulation) | The protocol requires at least two occurrences of one event, forbids another event, and supports a client copying incomplete progress. Its soundness follows through the bridge. |
| Completion implications are strict | [`odd_unary_not_shuffle_closed`](#declaration-odd-unary-not-shuffle-closed), [`gap_unary_residual_shuffle_closed`](#declaration-gap-unary-residual-shuffle-closed), [`gap_unary_not_completion_stable`](#declaration-gap-unary-not-completion-stable) | Universal viability alone does not give complete-history shuffle closure. Residual shuffle closure does not imply persistent completion. |
| Residual certification is essential for the exhibited copying client | [`separating_copy_accepted_without_certificate`](#declaration-separating-copy-accepted-without-certificate), [`separating_copy_terminates`](#declaration-separating-copy-terminates), [`separating_copy_actual_history`](#declaration-separating-copy-actual-history), [`separating_copy_actual_history_not_viable`](#declaration-separating-copy-actual-history-not-viable), [`separating_copy_unsound_without_residual_certificate`](#declaration-separating-copy-unsound-without-residual-certificate) | The concrete client allocates x, calls x.a, copies y := x, calls x.c and y.b, then performs the single instrumented bulk exit. Bypassing the required residual certificate makes the local copying checker accept, but the raw object history acb is nonviable. The residual certificate rejects this protocol. This is not a counterexample to the soundness theorem. |
| Baseline/copying and accumulation separation | [`separating_original_certificate`](#declaration-separating-original-certificate), [`separating_residual_not_closed`](#declaration-separating-residual-not-closed), [`separating_acb_not_viable`](#declaration-separating-acb-not-viable), [`separating_certified_not_kellogg`](#declaration-separating-certified-not-kellogg) | For the stated six-seed protocol, baseline certification succeeds, the residual at a is not shuffle closed, and the extracted error law fails. This is a language-level separation, not a comparison of implementations. |
| Strict hierarchy of regular protocol classes (end of §6) | [`accumulation_contract_residual_shuffle_closed`](#declaration-accumulation-contract-residual-shuffle-closed), [`gap_unary_residual_shuffle_closed`](#declaration-gap-unary-residual-shuffle-closed), [`gap_unary_not_completion_stable`](#declaration-gap-unary-not-completion-stable), [`separating_original_certificate`](#declaration-separating-original-certificate), [`separating_residual_not_closed`](#declaration-separating-residual-not-closed) | The paper combines these proven implications and witnesses: accumulation contracts are a proper subclass of residual shuffle-closed protocols, which are a proper subclass of shuffle-closed protocols. Regularity of the unary gap language is immediate from its displayed definition, and regularity of the six-seed closure follows from construction. This hierarchy concerns languages, not inclusion of accepted client programs. |

## Definitions, rules, and representation correspondence

The following comparison checks every primitive rule and the sequencing and
program rules in `paper/typestate.tex`. A representation difference is not a
false theorem. A missing correspondence proof matters when applying a core
result to the paper's surface algorithm.

| Paper rule or definition | Rocq representation | Checked premises and remaining boundary |
| --- | --- | --- |
| Pumping `w = pq`, `w′ = paq`, with `a` occurring in `p` | `pumping`, `pump_at`, `pumping_decompose`, `pumping_insert_char_after_prefix` in [pumping.v](pumping.v) | Indexed bounds ensure the copied event precedes the insertion. The default event is never read out of bounds by a successful step. The two decomposition/insertion lemmas connect the presentations. |
| Pumping closure and originating seeds | `pumping_closure`, `seed_covers`, `covered_by`, `pumping_closure_seed_corpus` | Closure is an inductive proposition, separate from the generated regex. Factorization does not assume the desired language equality. |
| Residual `u⁻¹K`, viability, nullability | `residual`, `prefix_language`, `qualifier_language`, `protocol_family.viable_spec` | A qualifier stores a class/history pair denoting an exact residual. Boolean acceptance is the definition of `protocol`. Viability is required to have a proof of its extension contract. |
| Dynamic New | `run_new`, `allocate`, `install` in [semantics.v](semantics.v); `runtime_guard`, `monitored_step` | The raw step is unguarded; its monitored version checks empty-history viability and signals `ProtocolError` on failure. Ghost locations and epochs are successive naturals. surface_ghost_primitive equips any fresh surface location with a fresh ghost epoch and extends an injective location map; ghost_surface_primitive proves the converse. |
| Static New | `type_new`, `check_bind` in [typestate.v](typestate.v) | Outgoing target is retirable. The new class's empty history is viable. The new history is empty. |
| Dynamic Assign | `run_copy`, `bind` | Source is looked up in the pre-state. A new epoch refers to the same location, including self-assignment. No event is appended. |
| Static Assign | `type_copy`, `check_step (Copy x y)` | Source lookup, target retirement, and initial viability match the fresh-history premises. Source and target can be equal. The old target must still be complete. |
| Static Assign-Copy | `copy_step_spec`, `check_step_with_copy` in [copying_typestate.v](copying_typestate.v) | When enabled, only the outgoing target's retirement is checked locally and the source history is inherited. The per-class residual condition is a global `copying_certified`/certificate premise. Viability of the inherited source follows from the invariant, without a redundant fresh-history check. |
| Dynamic Load | `run_load`, `bind` | Source binding and field lookup must succeed. An uninitialized field has no transition. Progress is not proved. |
| Static Load | `type_load`, `check_bind` | The target retires, the source binding exists, and the field class's initial history is viable. Fields always start fresh, even in copying mode. `field_type` is total. Field declaration validity belongs to the paper's ordinary typing layer. |
| Dynamic Store | `run_store`, `store` | Both bindings must exist. The location-field entry changes. Epoch owners and histories do not. |
| Static Store | `type_store` | `field_type` equals the source class, and the qualifier environment is unchanged. Heap/class agreement is preserved in the invariant. |
| Dynamic Call | `run_call`, `emit`, `runtime_guard`, `monitored_step`, `runtime_call_guard` | The raw rule requires only source lookup and can emit an invalid event. The monitored rule additionally checks viability of the updated aggregate receiver history and signals `ProtocolError` on failure. Error freedom for accepted programs follows from independent raw soundness. |
| Static Call | `type_call`, `check_step (Call x a)` | Only the receiver history is extended. The extended history must be viable. The artifact uses a common event type `A`, with no separate `a ∈ Σ_C` judgment. Per-class event admissibility can be represented by protocol membership. Ordinary method typing is outside the formalization. |
| Dynamic/static Finish | `run_finish`, `clear_refs`, `type_finish`, `all_complete_spec`, `runtime_exit_check` | One bulk step clears all bindings while preserving objects and histories. The raw rule is unguarded; the monitor checks every allocated object. The static rule checks each current qualifier and returns the empty environment. |
| Skip | `Skip`, `type_skip`, `skip_terminal` | `Skip` preserves the static environment and has no runtime step. |
| Seq | `Seq`, `type_seq`, `step_seq`, `step_skip`, `execution` | Checking composes through one intermediate environment. Only the left statement reduces; once it is `Skip`, the right statement becomes active. |
| Program and exit insertion | `finish_free`, `instrument`, `check_program_spec`, `check_program_with_copy_spec`, `source_execution_iff` | Both checkers and execution helpers take source programs, reject source-level `Finish`, and insert `Seq s Finish`. Structural derivations start and end with the empty environment. The executable/source relationship includes `Skip`. |
| Fresh-history local/object invariants | `invariant`, `project_partition`, `tagged_shuffle_closed` | Retired epochs retain their histories. Every allocated location has at least one epoch. Composition therefore uses a positive finite set and does not require that empty histories be complete. |
| Inherited-view invariant | `copying_invariant`, `future_safe`, `future_safe_copy` | Hypothetical future tags must belong to the object's epochs (`supported`). Every epoch, including retired epochs, must have a completing view. Empty futures establish final object completion. |

The generic trace and client proofs use arbitrary event types and require no
finite alphabet. The regular-seed layer uses `finType`, and its indexed pumping
relation takes a default alphabet element. Consequently, the formal pipeline
covers inhabited finite alphabets. The mathematical empty-alphabet case has
only the empty word and no pumping steps. It is not an instance of a theorem
requiring `d0 : char`. The regular-language compiler uses Boolean seed predicates. The general
`seed_shuffle_coveredP` theorem separately quantifies over arbitrary
Prop-valued seed languages using `covered_by`. It needs no seed-membership
decision procedure. `base_shuffle_coveredP` supplies the Boolean-language
connection to inductively defined `pumping_closure`.

## Trust and non-vacuity

[audit.v](audit.v) lists the principal `Print Assumptions` queries. Run
`make assumptions` to reproduce their output and `make check` to rebuild, scan
sources for proof holes/new global assumptions, and independently check compiled
proofs with `coqchk`. The principal construction, certificate, bridge, and
client-soundness results report **`Closed under the global context`**. The
optional minimal-corpus theory in `pumping.v` uses standard classical logic.
Those results are outside the dependency closure of the principal audits.
The kernel and the adequacy of the definitions remain trusted.
Examples using `vm_compute` are included in the independent `coqchk` check
and introduce no additional axioms. No `native_compute` proof is used.

Generalized premises such as `certified P`, `certified_modes`, and
`completion_persists` are not discharged by printing assumptions. They are
explicit mathematical inputs. The regular integration proves certification
from Boolean checks. The accumulation integration derives it from its stated
semantic laws.

The protocol-pattern families also discharge their hypotheses constructively.
Prerequisite specifications carry a satisfying witness; threshold protocols
accept a threshold-sized increment prefix followed by a use; capacity protocols
accept an addition followed by a use of the supplied identity. The milestone and
service machines constructively complete every state with `tir` and `twcq`,
respectively. Their exact
viability proofs and explicit aliasing executions are linked in the
[protocol-pattern table](#protocol-pattern-families). The finite frontier tables
are data checked by Rocq, so their Python generation adds no trusted proof step.

The hypotheses are inhabited by kernel-checked positive clients in
[examples.v](examples.v), [copying_examples.v](copying_examples.v), and
[accumulation_examples.v](accumulation_examples.v), including allocation,
nested sequencing, aliasing, fields, overwrites, and incomplete inherited progress.
`aliases_terminates` and `inherited_progress_terminates` give explicit full
executions for accepted clients. `noncanonical_surface_execution` chooses fresh
locations 37 and 5, and `noncanonical_surface_equipped` constructs its matching
ghost run; clearing references retains both allocated objects. Their history lemmas compute four and three
actual events respectively. `abandoned_object_complete` applies the headline
theorem to an object proved unreachable in the final machine.
`raw_invalid_call_executes` proves that the raw semantics can execute an invalid
event and reach a nonviable history. The separate
`separating_copy_unsound_without_residual_certificate` witness proves that
ordinary shuffle certification alone can admit the paper's unsafe `acb` history
when used with inherited histories. The required residual certificate excludes
that protocol. Negative checker examples reject missing
completion and unsupported events. Soundness remains conditional
on an executable prefix/full execution. It is not an initialization-progress
or termination theorem. An empty protocol may pass the shuffle certificate,
but its failed initial-viability query prevents allocation by the checker.

## Remaining scope and release issues

These are open proof extensions or submission tasks, **not discovered false
Rocq theorems**. They should remain explicit in the artifact and manuscript.
Baseline necessity is mechanized in `necessity.v`. The optional copying
theorem states a sufficient condition. A general converse for that mode is
not a paper claim. Its concrete unsafe client shows that ordinary shuffle
closure alone cannot replace the residual certificate in general.

| Issue | Present status | What would close it |
| --- | --- | --- |
| Optional converse for arbitrary copying modes | UNMECHANIZED optional strengthening. Not a missing claimed theorem | Prove or refute a general equivalence between copying_certified and completion soundness of all accepted mode-aware core programs. The paper claims sufficiency and an exact residual-language certificate. The concrete acb witness establishes the stronger condition's relevance for that example. |
| Empty alphabet | Explicitly restricted mechanized representation, disclosed in the paper | Prove a separate empty-alphabet case or retain the stated inhabitance restriction. Arbitrary Prop-valued seeds are already covered by seed_shuffle_coveredP. The remaining issue concerns only the alphabet edge case. |
| Ordinary initialization and method/field typing | Outside the core proof | Add an ordinary typing/initialization judgment and a progress or execution correspondence theorem. Current results intentionally quantify over executions that exist. |
| Runtime, full language, and API implementation | Outside the claims | Mechanize resource costs or implementation refinements only if adding claims about time bounds, full-language implementations, loops, exceptions, callbacks, concurrency, or library bodies. A DFA state count is not a runtime theorem. |
| License for project-authored sources | No project license is supplied | The rights holder must select and include redistribution/reuse terms. The restored [RegLang license](RegLang/LICENSE) covers the bundled library. It does not license this project's own files. |
| Archival artifact link | Not supplied in the current manuscript/guide | Deposit the final source package and record its persistent identifier before archival submission. |
| Original revision of bundled RegLang | Unknown. The [provenance notice](RegLang/README.md) records exact matches and differences against upstream v1.2.2 | Recover the original revision if possible. Retain the documented comparison and upstream license meanwhile. The bundled sources are rebuilt and their imported proofs independently checked. |
| Installation on a fresh operating system | Not exercised | Test dependency installation in a clean environment. Source-only rebuilds and the pinned-dependency dry run passed with the installed toolchains. No container image is claimed. |

## Verbatim declaration index

The signatures below are copied from source without changing their hypotheses.
The source links identify the declarations. Proof bodies remain in their modules.
Read the following section contexts with those signatures:

- `pumping.v`: `char : finType`, `d0 : char`. Local `word`, `dlang`, `lang`,
  and `regexp` abbreviations use this alphabet. `dlang` is Boolean-valued.
- `coverage.v` and `coverage_simulation.v`: `A : finType`. Singleton pumping
  equivalence also takes `default : A`. The simulator itself does not need it.
- `certification.v`, `regular_protocols.v`: `A : finType`, with a default
  element generalized into those results that mention indexed pumping.
- `invariants.v`, `soundness.v`: `A : Type`, `P : protocol_family A`, and
  `FT : class -> field -> class`.
- `necessity.v`: `A : Type`, `P : protocol_family A`, and `FT` are
  quantified in the baseline converse. Its soundness premise quantifies over
  every statement, completed raw execution, and allocated location.
- `exact_protocols.v`: `A : finType`; the exact adapters require no default
  symbol and do not invoke pumping. `exact_protocol_examples.v` uses Boolean
  events, with `u = false` and `b = true`.
- `regular_soundness.v`: `A : finType`, `default : A`,
  `specifications : list (regexp A)`, and `FT`. Classes beyond the list use
  `Void`, so allocation of such a class cannot pass initial viability.
- `copying_soundness.v`: `A`, `P`, `FT`, `copy_history : class -> bool`, and
  **`certified_modes : copying_certified P copy_history`**. This section
  hypothesis is generalized into preservation and soundness theorems even
  when not repeated textually in their declaration headers.
- `copying_regular_soundness.v`: the regular table parameters above, plus
  `copying_flags : list bool`. Missing flags default to `false`.
- `residual_certification.v`: `A : finType`, `D : dfa A` for the generic
  certificate. The regex wrapper instantiates the compiled DFA.
- `kellogg_separation.v`: the concrete alphabet is `option bool`, with
  `a = None`, `b = Some false`, and `c = Some true`. `separating_family` is
  the compiled six-seed protocol. `separating_fields` returns the receiver
  class. The copying counterexample intentionally bypasses residual certification.
- `accumulation_integration.v`, client section: `A`, `P`, `FT`, and
  `copy_history`, plus **`errors_accumulate : forall c,
  kellogg_error_closed (prefix_language (protocol P c))`** and
  **`completion_persists : forall c, completion_stable (protocol P c)`**.
  The two soundness headers must be read with both generalized premises.


### Definition `protocol_family`

[protocols.v:7](protocols.v#L7)

```coq
Record protocol_family (A : Type) := {
  accepts : nat -> list A -> bool;
  viable : nat -> list A -> bool;
  viable_spec : forall c u, viable c u = true <->
    exists v, accepts c (u ++ v) = true
}.
```

### Definition `residual_shuffle_closed`

[copying_typestate.v:7](copying_typestate.v#L7)

```coq
Definition residual_shuffle_closed {A} (K : language A) :=
  forall p, shuffle_closed (residual K p).
```

### Definition `copying_certified`

[copying_typestate.v:9](copying_typestate.v#L9)

```coq
Definition copying_certified {A} (P : protocol_family A) (copy_history : class -> bool) :=
  certified P /\ forall c, copy_history c = true -> residual_shuffle_closed (protocol P c).
```

### Definition `future_safe`

[copying_languages.v:11](copying_languages.v#L11)

```coq
Definition future_safe (K : language A) (I : nat -> Prop)
    (V : nat -> list A) (w : list A) :=
  forall t, supported I t ->
    (forall e, I e -> K (V e ++ project e t)) -> K (w ++ erase_tags t).
```

### Definition `kellogg_error_closed`

[accumulation_bridge.v:57](accumulation_bridge.v#L57)

```coq
Definition kellogg_error_closed {A} (P : language A) :=
  forall u v a, trace_subsequence u v -> P v ->
    ~ P (v ++ [a]) -> ~ P (u ++ [a]).
```

### Definition `subsequence_safe_extension`

[accumulation_bridge.v:61](accumulation_bridge.v#L61)

```coq
Definition subsequence_safe_extension {A} (P : language A) :=
  forall u v a, trace_subsequence u v -> P v ->
    P (u ++ [a]) -> P (v ++ [a]).
```

### Definition `completion_stable`

[accumulation_bridge.v:82](accumulation_bridge.v#L82)

```coq
Definition completion_stable {A} (K : language A) :=
  forall u v, trace_subsequence u v -> K u ->
    prefix_language K v -> K v.
```

### Definition `accumulation_contract`

[accumulation_bridge.v:86](accumulation_bridge.v#L86)

```coq
Definition accumulation_contract {A} (K : language A) :=
  subsequence_safe_extension (prefix_language K) /\ completion_stable K.
```

<a id="declaration-typestate-prefix-sound"></a>

### `typestate_prefix_sound`

[soundness.v:74](soundness.v#L74)

```coq
Theorem typestate_prefix_sound s m : certified P -> check_program P FT s = true ->
  program_prefix s initial_machine m ->
  forall l, l < next_loc m -> prefix_language (protocol P (classes m l)) (object_history m l).
```

<a id="declaration-typestate-completion-sound"></a>

### `typestate_completion_sound`

[soundness.v:82](soundness.v#L82)

```coq
Theorem typestate_completion_sound s m : certified P -> check_program P FT s = true ->
  program_execution s initial_machine m ->
  forall l, l < next_loc m -> protocol P (classes m l) (object_history m l).
```

<a id="declaration-completion-sound-requires-certified"></a>

### `completion_sound_requires_certified`

[necessity.v:88](necessity.v#L88)

```coq
Theorem completion_sound_requires_certified :
  (forall s m, check_program P FT s = true ->
    program_execution s initial_machine m ->
    forall l, l < next_loc m ->
      protocol P (classes m l) (object_history m l)) -> certified P.
```

<a id="declaration-completion-sound-iff-certified"></a>

### `completion_sound_iff_certified`

[necessity.v:117](necessity.v#L117)

```coq
Theorem completion_sound_iff_certified :
  (forall s m, check_program P FT s = true ->
    program_execution s initial_machine m ->
    forall l, l < next_loc m ->
      protocol P (classes m l) (object_history m l)) <->
  certified P.
```

<a id="declaration-project-partition"></a>

### `project_partition`

[trace_languages.v:83](trace_languages.v#L83)

```coq
Lemma project_partition {A} e (t : list (nat * A)) :
  shuffle (project e t) (erase_tags (without_tag e t)) (erase_tags t).
```

<a id="declaration-tagged-shuffle-closed"></a>

### `tagged_shuffle_closed`

[trace_languages.v:102](trace_languages.v#L102)

```coq
Theorem tagged_shuffle_closed {A} (K : language A) ids t :
  shuffle_closed K -> NoDup ids -> ids <> [] ->
  (forall i a, In (i,a) t -> In i ids) ->
  (forall i, In i ids -> K (project i t)) -> K (erase_tags t).
```

<a id="declaration-invariant-object-language"></a>

### `invariant_object_language`

[soundness.v:27](soundness.v#L27)

```coq
Lemma invariant_object_language m g l (K : language A) :
  invariant P FT m g -> l < next_loc m -> shuffle_closed K ->
  (forall e, e < next_epoch m -> owners m e = l -> K (project e (events m))) ->
  K (object_history m l).
```

<a id="declaration-pumping-normalize-correct"></a>

### `pumping_normalize_correct`

[pumping.v:1324](pumping.v#L1324)

```coq
  Theorem pumping_normalize_correct r :
    closure_equiv r (pumping_normalize r).
```

<a id="declaration-closure-regex-correct"></a>

### `closure_regex_correct`

[regular_protocols.v:14](regular_protocols.v#L14)

```coq
Theorem closure_regex_correct r w :
  (w \in closure_regex r) <-> @pumping_closure A default (regex_lang A r) w.
```

<a id="declaration-certify-regex-spec"></a>

### `certify_regex_spec`

[certification.v:90](certification.v#L90)

```coq
Theorem certify_regex_spec r : certify_regex r = true <->
  @pumping.shuffle_closed A (@pumping_closure_lang A default (regex_lang A r)).
```

<a id="declaration-regex-counterexample-complete"></a>

### `regex_counterexample_complete`

[certification.v:160](certification.v#L160)

```coq
Theorem regex_counterexample_complete r : certify_regex r = false ->
  exists u v w, regex_counterexample r = Some (u,v,w).
```

<a id="declaration-regex-counterexample-none"></a>

### `regex_counterexample_none`

[certification.v:156](certification.v#L156)

```coq
Theorem regex_counterexample_none r :
  regex_counterexample r = None <-> certify_regex r = true.
```

<a id="declaration-regex-counterexample-sound"></a>

### `regex_counterexample_sound`

[certification.v:169](certification.v#L169)

```coq
Theorem regex_counterexample_sound r u v w : regex_counterexample r = Some (u,v,w) ->
  @pumping_closure A default (regex_lang A r) u /\
  @pumping_closure A default (regex_lang A r) v /\
  @interleaving A u v w /\
  ~ @pumping_closure A default (regex_lang A r) w.
```

<a id="declaration-kellogg-error-closed-iff-residual-prefix-shuffle-closed"></a>

### `kellogg_error_closed_iff_residual_prefix_shuffle_closed`

[accumulation_bridge.v:192](accumulation_bridge.v#L192)

```coq
Theorem kellogg_error_closed_iff_residual_prefix_shuffle_closed
    {A} (K : language A) :
  (forall w, {prefix_language K w} + {~ prefix_language K w}) ->
  (kellogg_error_closed (prefix_language K) <->
    residual_shuffle_closed (prefix_language K)).
```

<a id="declaration-accumulation-contract-residual-shuffle-closed"></a>

### `accumulation_contract_residual_shuffle_closed`

[accumulation_bridge.v:234](accumulation_bridge.v#L234)

```coq
Theorem accumulation_contract_residual_shuffle_closed {A} (K : language A) :
  accumulation_contract K -> residual_shuffle_closed K.
```

<a id="declaration-separating-certified-not-kellogg"></a>

### `separating_certified_not_kellogg`

[kellogg_separation.v:90](kellogg_separation.v#L90)

```coq
Theorem separating_certified_not_kellogg :
  certified separating_family /\
  ~ kellogg_error_closed (prefix_language (protocol separating_family 0)).
```

<a id="declaration-regular-program-prefix-sound"></a>

### `regular_program_prefix_sound`

[regular_soundness.v:30](regular_soundness.v#L30)

```coq
Theorem regular_program_prefix_sound s m : check_regular_program s = true ->
  program_prefix s initial_machine m -> forall l, (l < next_loc m)%coq_nat ->
  exists suffix, @pumping_closure A default (regex_lang A (class_seed (classes m l)))
    (object_history m l ++ suffix).
```

<a id="declaration-regular-program-completion-sound"></a>

### `regular_program_completion_sound`

[regular_soundness.v:41](regular_soundness.v#L41)

```coq
Theorem regular_program_completion_sound s m : check_regular_program s = true ->
  program_execution s initial_machine m -> forall l, (l < next_loc m)%coq_nat ->
  @pumping_closure A default (regex_lang A (class_seed (classes m l))) (object_history m l).
```

<a id="declaration-copying-regular-program-prefix-sound"></a>

### `copying_regular_program_prefix_sound`

[copying_regular_soundness.v:37](copying_regular_soundness.v#L37)

```coq
Theorem copying_regular_program_prefix_sound s m : check_regular_program_with_copy s = true ->
  program_prefix s initial_machine m -> forall l, (l < next_loc m)%coq_nat ->
  exists suffix, @pumping_closure A default (regex_lang A (class_seed specifications (classes m l)))
    (object_history m l ++ suffix).
```

<a id="declaration-copying-regular-program-completion-sound"></a>

### `copying_regular_program_completion_sound`

[copying_regular_soundness.v:47](copying_regular_soundness.v#L47)

```coq
Theorem copying_regular_program_completion_sound s m : check_regular_program_with_copy s = true ->
  program_execution s initial_machine m -> forall l, (l < next_loc m)%coq_nat ->
  @pumping_closure A default (regex_lang A (class_seed specifications (classes m l))) (object_history m l).
```

<a id="declaration-check-step-sound"></a>

### `check_step_sound`

[typestate.v:69](typestate.v#L69)

```coq
Lemma check_step_sound i g g' : check_step i g = Some g' -> type_step g i g'.
```

<a id="declaration-check-step-complete"></a>

### `check_step_complete`

[typestate.v:87](typestate.v#L87)

```coq
Lemma check_step_complete g i g' : type_step g i g' -> check_step i g = Some g'.
```

<a id="declaration-check-stmt-spec"></a>

### `check_stmt_spec`

[typestate.v:111](typestate.v#L111)

```coq
Theorem check_stmt_spec s g g' : check_stmt s g = Some g' <-> typed_stmt g s g'.
```

<a id="declaration-pumping-closure-regular-regex"></a>

### `pumping_closure_regular_regex`

[pumping.v:1393](pumping.v#L1393)

```coq
  Theorem pumping_closure_regular_regex r :
    RegLang.dfa.regular
      (fun out : word =>
        @pumping_closure char d0 (regex_lang r) out).
```

<a id="declaration-copy-step-spec"></a>

### `copy_step_spec`

[copying_typestate.v:44](copying_typestate.v#L44)

```coq
Lemma copy_step_spec g x y g' :
  check_step_with_copy (Copy x y) g = Some g' <->
  exists c w, get g y = Some (c,w) /\ retirable P g x = true /\
    (if copy_history c then g' = put g x (Some (c,w))
     else viable P c [] = true /\ g' = put g x (Some (c,[]))).
```

<a id="declaration-copying-program-prefix-sound"></a>

### `copying_program_prefix_sound`

[copying_soundness.v:390](copying_soundness.v#L390)

```coq
Theorem copying_program_prefix_sound s m :
  check_program_with_copy P FT copy_history s = true -> program_prefix s initial_machine m ->
  forall l, l < next_loc m -> prefix_language (protocol P (classes m l)) (object_history m l).
```

<a id="declaration-copying-program-completion-sound"></a>

### `copying_program_completion_sound`

[copying_soundness.v:399](copying_soundness.v#L399)

```coq
Theorem copying_program_completion_sound s m :
  check_program_with_copy P FT copy_history s = true -> program_execution s initial_machine m ->
  forall l, l < next_loc m -> protocol P (classes m l) (object_history m l).
```

<a id="declaration-certify-copying-regex-spec"></a>

### `certify_copying_regex_spec`

[residual_certification.v:98](residual_certification.v#L98)

```coq
Theorem certify_copying_regex_spec (spec : nat -> regexp A) c :
  certify_copying_regex (spec c) = true <->
  residual_shuffle_closed (protocols.protocol (regular_family spec) c).
```

<a id="declaration-kellogg-regular-certificates"></a>

### `kellogg_regular_certificates`

[accumulation_integration.v:50](accumulation_integration.v#L50)

```coq
Theorem kellogg_regular_certificates c :
  kellogg_error_closed (prefix_language (protocol (regular_family spec) c)) ->
  completion_stable (protocol (regular_family spec) c) ->
  certify_regex (spec c) = true /\ certify_copying_regex (spec c) = true.
```

<a id="declaration-kellogg-protocol-copying-certified"></a>

### `kellogg_protocol_copying_certified`

[accumulation_bridge.v:275](accumulation_bridge.v#L275)

```coq
Theorem kellogg_protocol_copying_certified {A}
    (P : protocol_family A) copy_history :
  (forall c, kellogg_error_closed (prefix_language (protocol P c))) ->
  (forall c, completion_stable (protocol P c)) ->
  copying_certified P copy_history.
```

<a id="declaration-seed-shuffle-coveredP"></a>

### `seed_shuffle_coveredP`

[pumping.v:1763](pumping.v#L1763)

```coq
  Theorem seed_shuffle_coveredP (S : lang) :
    seed_shuffle_covered S <-> shuffle_closed (covered_by S).
```

<a id="declaration-base-shuffle-coveredP"></a>

### `base_shuffle_coveredP`

[pumping.v:1736](pumping.v#L1736)

```coq
  Theorem base_shuffle_coveredP (L : dlang) :
    base_shuffle_covered L <->
    shuffle_closed (pumping_closure_lang L).
```

<a id="declaration-kellogg-program-prefix-sound"></a>

### `kellogg_program_prefix_sound`

[accumulation_integration.v:77](accumulation_integration.v#L77)

```coq
Theorem kellogg_program_prefix_sound s m :
  check_program_with_copy P FT copy_history s = true ->
  program_prefix s initial_machine m ->
  forall l, (l < next_loc m)%coq_nat ->
  prefix_language (protocol P (classes m l)) (object_history m l).
```

<a id="declaration-kellogg-program-completion-sound"></a>

### `kellogg_program_completion_sound`

[accumulation_integration.v:87](accumulation_integration.v#L87)

```coq
Theorem kellogg_program_completion_sound s m :
  check_program_with_copy P FT copy_history s = true ->
  program_execution s initial_machine m ->
  forall l, (l < next_loc m)%coq_nat ->
  protocol P (classes m l) (object_history m l).
```

<a id="declaration-certify-residuals-spec"></a>

### `certify_residuals_spec`

[residual_certification.v:72](residual_certification.v#L72)

```coq
Theorem certify_residuals_spec : certify_residuals = true <->
  residual_shuffle_closed (fun w => w \in dfa_lang D).
```

<a id="declaration-pumping-closure-cat"></a>

### `pumping_closure_cat`

[pumping.v:636](pumping.v#L636)

```coq
  Lemma pumping_closure_cat
      (L1 L2 : dlang) (u v : word) :
    @pumping_closure char d0 L1 u ->
    @pumping_closure char d0 L2 v ->
    @pumping_closure char d0 (RegLang.languages.conc L1 L2) (u ++ v).
```

<a id="declaration-pumping-closure-singleton-correct"></a>

### `pumping_closure_singleton_correct`

[pumping.v:1331](pumping.v#L1331)

```coq
  Lemma pumping_closure_singleton_correct w out :
    @pumping_closure char d0 (pred1 w) out <->
    out \in pumping_singleton_re w.
```

<a id="declaration-pumping-closure-star-finite-basis"></a>

### `pumping_closure_star_finite_basis`

[pumping.v:1227](pumping.v#L1227)

```coq
  Theorem pumping_closure_star_finite_basis (r : regexp) :
    closure_equiv (Star r) (bounded_star_basis r).
```

<a id="declaration-eliminate-star-correct"></a>

### `eliminate_star_correct`

[pumping.v:1311](pumping.v#L1311)

```coq
  Theorem eliminate_star_correct r :
    closure_equiv r (eliminate_star r).
```

<a id="declaration-eliminate-star-star-free"></a>

### `eliminate_star_star_free`

[pumping.v:443](pumping.v#L443)

```coq
  Lemma eliminate_star_star_free r :
    star_free (eliminate_star r).
```

<a id="declaration-star-free-finite"></a>

### `star_free_finite`

[pumping.v:408](pumping.v#L408)

```coq
  Lemma star_free_finite (r : regexp) :
    star_free r -> finite_lang (regex_lang r).
```

<a id="declaration-words-of-star-free-correct"></a>

### `words_of_star_free_correct`

[pumping.v:366](pumping.v#L366)

```coq
  Lemma words_of_star_free_correct r :
    star_free r ->
    forall w, (w \in r) = (w \in words_of_star_free r).
```

<a id="declaration-pumping-interleaving-left"></a>

### `pumping_interleaving_left`

[pumping.v:1563](pumping.v#L1563)

```coq
  Lemma pumping_interleaving_left u u' v w' :
    @pumping char d0 u u' ->
    interleaving u' v w' ->
    exists w,
      interleaving u v w /\ @pumping char d0 w w'.
```

<a id="declaration-pumping-interleaving-right"></a>

### `pumping_interleaving_right`

[pumping.v:1598](pumping.v#L1598)

```coq
  Lemma pumping_interleaving_right u v v' w' :
    @pumping char d0 v v' ->
    interleaving u v' w' ->
    exists w,
      interleaving u v w /\ @pumping char d0 w w'.
```

<a id="declaration-seed-cover-interleaving-factor"></a>

### `seed_cover_interleaving_factor`

[pumping.v:1703](pumping.v#L1703)

```coq
  Lemma seed_cover_interleaving_factor su sv u v w :
    seed_covers su u ->
    seed_covers sv v ->
    interleaving u v w ->
    exists z,
      interleaving su sv z /\ seed_covers z w.
```

<a id="declaration-certify-seeds-spec"></a>

### `certify_seeds_spec`

[certification.v:57](certification.v#L57)

```coq
Theorem certify_seeds_spec seeds : certify_seeds seeds = true <->
  @pumping.shuffle_closed A (@pumping_closure_lang A default (seed_language seeds)).
```

<a id="declaration-prefix-shuffle-closed"></a>

### `prefix_shuffle_closed`

[trace_languages.v:33](trace_languages.v#L33)

```coq
Lemma prefix_shuffle_closed {A} (K : language A) :
  shuffle_closed K -> shuffle_closed (prefix_language K).
```

<a id="declaration-preservation"></a>

### `preservation`

[invariants.v:180](invariants.v#L180)

```coq
Lemma preservation m g i m' g' : invariant m g ->
  primitive_step i m m' -> type_step P FT g i g' -> invariant m' g'.
```

<a id="declaration-execution-preservation"></a>

### `execution_preservation`

[invariants.v:219](invariants.v#L219)

```coq
Theorem execution_preservation c d : execution c d ->
  forall g gf, invariant (fst c) g -> typed_stmt P FT g (snd c) gf ->
  exists g', invariant (fst d) g' /\ typed_stmt P FT g' (snd d) gf.
```

<a id="declaration-residual-snoc"></a>

### `residual_snoc`

[trace_languages.v:40](trace_languages.v#L40)

```coq
Lemma residual_snoc {A} (K : language A) u a v :
  residual K (u ++ [a]) v <-> residual K u (a :: v).
```

<a id="declaration-residual-nullable"></a>

### `residual_nullable`

[trace_languages.v:43](trace_languages.v#L43)

```coq
Lemma residual_nullable {A} (K : language A) u :
  residual K u [] <-> K u.
```

<a id="declaration-accumulation-contract-shuffle-closed"></a>

### `accumulation_contract_shuffle_closed`

[accumulation_bridge.v:246](accumulation_bridge.v#L246)

```coq
Theorem accumulation_contract_shuffle_closed {A} (K : language A) :
  accumulation_contract K -> shuffle_closed K.
```

<a id="declaration-covers-spec"></a>

### `covers_spec`

[coverage.v:65](coverage.v#L65)

```coq
Theorem covers_spec (default : A) seed out :
  covers seed out = true <-> @seed_covers A default seed out.
```

<a id="declaration-covers-simulation-correct"></a>

### `covers_simulation_correct`

[coverage_simulation.v:125](coverage_simulation.v#L125)

```coq
Theorem covers_simulation_correct seed out : covers_simulation seed out = covers A seed out.
```

<a id="declaration-simulation-state-bound"></a>

### `simulation_state_bound`

[coverage_simulation.v:176](coverage_simulation.v#L176)

```coq
Theorem simulation_state_bound seed out :
  size (run_states [:: ([::],seed)] out) <= (size seed).+1.
```

<a id="declaration-shuffles-spec"></a>

### `shuffles_spec`

[finite_shuffles.v:34](finite_shuffles.v#L34)

```coq
Theorem shuffles_spec {A} (u v w : list A) : In w (shuffles u v) <-> shuffle u v w.
```

<a id="declaration-counterexample-selection"></a>

### Definitions `shuffle_candidates`, `counterexample`, and `regex_counterexample`

[certification.v:100](certification.v#L100), [certification.v:155](certification.v#L155)

```coq
Definition shuffle_candidates (seeds : seq (seq A)) :=
  List.flat_map (fun u => List.flat_map (fun v =>
    List.map (fun w => (u,v,w)) (shuffles u v)) seeds) seeds.
Definition counterexample seeds :=
  List.find (fun t => negb (coveredb seeds (snd t))) (shuffle_candidates seeds).

Definition regex_counterexample (r : regexp A) := counterexample (normalized_seeds r).
```

For a returned triple, the standard-library lemma `List.find_some` gives
membership in `shuffle_candidates seeds`. The following proved lemma then
gives membership of both input histories in `seeds`, as well as their
interleaving. The proof of `counterexample_sound` performs precisely these
steps at [certification.v:127](certification.v#L127), but its exported signature
weakens input seed membership to pumping-closure membership. Applying the same
steps after unfolding `regex_counterexample` gives membership in
`normalized_seeds r`, the paper's $F(r)$; this consequence is not a separately
exported theorem.

<a id="declaration-shuffle-candidates-spec"></a>

### `shuffle_candidates_spec`

[certification.v:106](certification.v#L106)

```coq
Lemma shuffle_candidates_spec seeds u v w :
  List.In (u,v,w) (shuffle_candidates seeds) <->
  List.In u seeds /\ List.In v seeds /\ @interleaving A u v w.
```

<a id="declaration-counterexample-sound"></a>

### `counterexample_sound`

[certification.v:121](certification.v#L121)

```coq
Theorem counterexample_sound seeds u v w : counterexample seeds = Some (u,v,w) ->
  @pumping_closure A default (seed_language seeds) u /\
  @pumping_closure A default (seed_language seeds) v /\
  @interleaving A u v w /\
  ~ @pumping_closure A default (seed_language seeds) w.
```

<a id="declaration-counterexample-none"></a>

### `counterexample_none`

[certification.v:140](certification.v#L140)

```coq
Theorem counterexample_none seeds : counterexample seeds = None <-> certify_seeds seeds = true.
```

<a id="declaration-dfa-viable-spec"></a>

### `dfa_viable_spec`

[regular_protocols.v:37](regular_protocols.v#L37)

```coq
Lemma dfa_viable_spec (D : dfa A) u : dfa_viable D u = true <->
  exists v, (u ++ v \in dfa_lang D) = true.
```

<a id="declaration-regular-family-language"></a>

### `regular_family_language`

[regular_protocols.v:69](regular_protocols.v#L69)

```coq
Theorem regular_family_language spec c w :
  protocol (regular_family spec) c w <->
  @pumping_closure A default (regex_lang A (spec c)) w.
```

<a id="declaration-regular-family-certified"></a>

### `regular_family_certified`

[regular_protocols.v:77](regular_protocols.v#L77)

```coq
Theorem regular_family_certified spec :
  (forall c, certify_regex (spec c) = true) -> certified (regular_family spec).
```

<a id="declaration-fresh-program-unchanged"></a>

### `fresh_program_unchanged`

[copying_typestate.v:175](copying_typestate.v#L175)

```coq
Theorem fresh_program_unchanged {A} (P : protocol_family A) FT s :
  check_program_with_copy P FT (fun _ => false) s = check_program P FT s.
```

<a id="declaration-future-safe-copy"></a>

### `future_safe_copy`

[copying_languages.v:89](copying_languages.v#L89)

```coq
Lemma future_safe_copy K I V w n s : ~ I n -> I s ->
  shuffle_closed (residual K (V s)) -> future_safe K I V w ->
  future_safe K (fun e => e = n \/ I e) (update V n (V s)) w.
```

<a id="declaration-copying-preservation"></a>

### `copying_preservation`

[copying_soundness.v:275](copying_soundness.v#L275)

```coq
Theorem copying_preservation m g V i m' g' : copying_invariant m g V ->
  primitive_step i m m' -> check_step_with_copy P FT copy_history i g = Some g' ->
  exists V', copying_invariant m' g' V'.
```

<a id="declaration-kellogg-error-closed-iff-safe-extension"></a>

### `kellogg_error_closed_iff_safe_extension`

[accumulation_bridge.v:69](accumulation_bridge.v#L69)

```coq
Theorem kellogg_error_closed_iff_safe_extension {A} (P : language A) :
  (forall w, {P w} + {~ P w}) ->
  (kellogg_error_closed P <-> subsequence_safe_extension P).
```

<a id="declaration-subsequence-safe-extension-iff-residual-prefix-shuffle-closed"></a>

### `subsequence_safe_extension_iff_residual_prefix_shuffle_closed`

[accumulation_bridge.v:183](accumulation_bridge.v#L183)

```coq
Theorem subsequence_safe_extension_iff_residual_prefix_shuffle_closed
    {A} (K : language A) :
  subsequence_safe_extension (prefix_language K) <->
  residual_shuffle_closed (prefix_language K).
```

<a id="declaration-residual-shuffle-closed-kellogg-error-closed"></a>

### `residual_shuffle_closed_kellogg_error_closed`

[accumulation_bridge.v:226](accumulation_bridge.v#L226)

```coq
Theorem residual_shuffle_closed_kellogg_error_closed {A} (K : language A) :
  residual_shuffle_closed K -> kellogg_error_closed (prefix_language K).
```

<a id="declaration-observations-accumulate-iff-contract"></a>

### `observations_accumulate_iff_contract`

[accumulation_integration.v:33](accumulation_integration.v#L33)

```coq
Theorem observations_accumulate_iff_contract {A} (K : language A) :
  observations_accumulate K <-> accumulation_contract K.
```

<a id="declaration-aliases-accepted"></a>

### `aliases_accepted`

[examples.v:44](examples.v#L44)

```coq
Example aliases_accepted : check_program two_calls fields aliases = true.
```

<a id="declaration-aliases-terminates"></a>

### `aliases_terminates`

[examples.v:86](examples.v#L86)

```coq
Example aliases_terminates : program_execution aliases initial_machine aliases_final.
```

<a id="declaration-aliases-object-history"></a>

### `aliases_object_history`

[examples.v:92](examples.v#L92)

```coq
Example aliases_object_history : next_loc aliases_final = 1 /\
  object_history aliases_final 0 = [true; true; true; true].
```

<a id="declaration-inherited-progress-accepted"></a>

### `inherited_progress_accepted`

[copying_examples.v:28](copying_examples.v#L28)

```coq
Example inherited_progress_accepted :
  check_program_with_copy two_calls fields copy_all inherited_progress = true.
```

<a id="declaration-inherited-progress-terminates"></a>

### `inherited_progress_terminates`

[copying_examples.v:49](copying_examples.v#L49)

```coq
Example inherited_progress_terminates :
  program_execution inherited_progress initial_machine inherited_progress_final.
```

<a id="declaration-inherited-progress-object-history"></a>

### `inherited_progress_object_history`

[copying_examples.v:57](copying_examples.v#L57)

```coq
Example inherited_progress_object_history :
  next_loc inherited_progress_final = 1 /\
  object_history inherited_progress_final 0 = [true; true; true].
```

<a id="declaration-abandoned-object-accepted"></a>

### `abandoned_object_accepted`

[examples.v:109](examples.v#L109)

```coq
Example abandoned_object_accepted :
  check_program two_calls fields abandoned_object = true.
```

<a id="declaration-abandoned-object-terminates"></a>

### `abandoned_object_terminates`

[examples.v:112](examples.v#L112)

```coq
Example abandoned_object_terminates :
  program_execution abandoned_object initial_machine abandoned_object_final.
```

<a id="declaration-abandoned-object-unreachable"></a>

### `abandoned_object_unreachable`

[examples.v:119](examples.v#L119)

```coq
Example abandoned_object_unreachable :
  next_loc abandoned_object_final = 2 /\
  object_history abandoned_object_final 0 = [true; true] /\
  (forall x, reference abandoned_object_final x = None) /\
  (forall l f, heap abandoned_object_final l f = None).
```

<a id="declaration-abandoned-object-complete"></a>

### `abandoned_object_complete`

[examples.v:129](examples.v#L129)

```coq
Example abandoned_object_complete :
  protocol two_calls (classes abandoned_object_final 0)
    (object_history abandoned_object_final 0).
```

<a id="declaration-raw-invalid-call-executes"></a>

### `raw_invalid_call_executes`

[examples.v:142](examples.v#L142)

```coq
Example raw_invalid_call_executes :
  exists m, program_execution (block [New 0 0; Call 0 false]) initial_machine m /\
    next_loc m = 1 /\
    ~ prefix_language (protocol two_calls (classes m 0)) (object_history m 0).
```

<a id="declaration-two-calls-accumulation-contract"></a>

### `two_calls_accumulation_contract`

[accumulation_examples.v:46](accumulation_examples.v#L46)

```coq
Theorem two_calls_accumulation_contract c :
  accumulation_contract (protocol two_calls c).
```

<a id="declaration-inherited-progress-sound-via-accumulation"></a>

### `inherited_progress_sound_via_accumulation`

[accumulation_examples.v:66](accumulation_examples.v#L66)

```coq
Theorem inherited_progress_sound_via_accumulation m :
  program_execution inherited_progress initial_machine m ->
  forall l, l < next_loc m ->
    protocol two_calls (classes m l) (object_history m l).
```

<a id="declaration-odd-unary-not-shuffle-closed"></a>

### `odd_unary_not_shuffle_closed`

[accumulation_examples.v:96](accumulation_examples.v#L96)

```coq
Example odd_unary_not_shuffle_closed : ~ shuffle_closed odd_unary_completion.
```

<a id="declaration-gap-unary-residual-shuffle-closed"></a>

### `gap_unary_residual_shuffle_closed`

[accumulation_examples.v:127](accumulation_examples.v#L127)

```coq
Example gap_unary_residual_shuffle_closed :
  residual_shuffle_closed gap_unary_completion.
```

<a id="declaration-gap-unary-not-completion-stable"></a>

### `gap_unary_not_completion_stable`

[accumulation_examples.v:135](accumulation_examples.v#L135)

```coq
Example gap_unary_not_completion_stable : ~ completion_stable gap_unary_completion.
```

<a id="declaration-separating-copy-accepted-without-certificate"></a>

### `separating_copy_accepted_without_certificate`

[kellogg_separation.v:119](kellogg_separation.v#L119)

```coq
Example separating_copy_accepted_without_certificate :
  check_program_with_copy separating_family separating_fields (fun _ => true)
    separating_copy_program = true.
```

<a id="declaration-separating-copy-terminates"></a>

### `separating_copy_terminates`

[kellogg_separation.v:151](kellogg_separation.v#L151)

```coq
Example separating_copy_terminates :
  program_execution separating_copy_program initial_machine separating_copy_final.
```

<a id="declaration-separating-copy-actual-history"></a>

### `separating_copy_actual_history`

[kellogg_separation.v:160](kellogg_separation.v#L160)

```coq
Example separating_copy_actual_history :
  next_loc separating_copy_final = 1 /\ classes separating_copy_final 0 = 0 /\
  object_history separating_copy_final 0 = [::a;c;b].
```

<a id="declaration-separating-copy-actual-history-not-viable"></a>

### `separating_copy_actual_history_not_viable`

[kellogg_separation.v:165](kellogg_separation.v#L165)

```coq
Example separating_copy_actual_history_not_viable :
  ~ prefix_language (protocol separating_family (classes separating_copy_final 0))
    (object_history separating_copy_final 0).
```

<a id="declaration-separating-copy-unsound-without-residual-certificate"></a>

### `separating_copy_unsound_without_residual_certificate`

[kellogg_separation.v:173](kellogg_separation.v#L173)

```coq
Theorem separating_copy_unsound_without_residual_certificate :
  check_program_with_copy separating_family separating_fields (fun _ => true)
    separating_copy_program = true /\
  program_execution separating_copy_program initial_machine separating_copy_final /\
  (0 < next_loc separating_copy_final)%coq_nat /\
  ~ prefix_language (protocol separating_family (classes separating_copy_final 0))
    (object_history separating_copy_final 0).
```

<a id="declaration-separating-original-certificate"></a>

### `separating_original_certificate`

[residual_certification_examples.v:21](residual_certification_examples.v#L21)

```coq
Example separating_original_certificate : certify_regex separating_regex = true.
```

<a id="declaration-separating-residual-not-closed"></a>

### `separating_residual_not_closed`

[residual_certification_examples.v:29](residual_certification_examples.v#L29)

```coq
Lemma separating_residual_not_closed : ~ residual_shuffle_closed (protocol separating_family 0).
```

<a id="declaration-separating-acb-not-viable"></a>

### `separating_acb_not_viable`

[kellogg_separation.v:63](kellogg_separation.v#L63)

```coq
Lemma separating_acb_not_viable : viable separating_family 0 [:: a; c; b] = false.
```

## Runtime-monitor declaration index

All declarations below generalize the section parameters `A : Type` and
`P : protocol_family A`. Protocol families carry verified Boolean membership
and viability queries; no new global assumptions are introduced.

<a id="declaration-runtime-call-guard"></a>

### `runtime_call_guard`

[runtime_monitor.v:33](runtime_monitor.v#L33)

```coq
Lemma runtime_call_guard x a m m' l :
  primitive_step (Call x a) m m' -> reference m x = Some l ->
  runtime_guard (Call x a) m m' =
    viable P (classes m l) (object_history m l ++ [a]).
```

<a id="declaration-runtime-exit-check-spec"></a>

### `runtime_exit_check_spec`

[runtime_monitor.v:49](runtime_monitor.v#L49)

```coq
Lemma runtime_exit_check_spec m : runtime_exit_check m = true <->
  forall l, l < next_loc m -> protocol P (classes m l) (object_history m l).
```

<a id="declaration-runtime-exit-check-clear"></a>

### `runtime_exit_check_clear`

[runtime_monitor.v:47](runtime_monitor.v#L47)

```coq
Lemma runtime_exit_check_clear m : runtime_exit_check (clear_refs m) = runtime_exit_check m.
```

<a id="declaration-raw-contract-monitor-no-error"></a>

### `raw_contract_monitor_no_error`

[runtime_monitor.v:262](runtime_monitor.v#L262)

```coq
Theorem raw_contract_monitor_no_error s : raw_protocol_contract s ->
  ~ monitored_program s initial_machine ProtocolError.
```

<a id="declaration-raw-contract-monitor-equivalence"></a>

### `raw_contract_monitor_equivalence`

[runtime_monitor.v:277](runtime_monitor.v#L277)

```coq
Theorem raw_contract_monitor_equivalence s : raw_protocol_contract s -> forall m,
  monitored_program s initial_machine (RuntimeState (m,Skip)) <->
  program_execution s initial_machine m.
```

<a id="declaration-baseline-runtime-no-error"></a>

### `baseline_runtime_no_error`

[runtime_monitor.v:293](runtime_monitor.v#L293)

```coq
Theorem baseline_runtime_no_error FT s : certified P ->
  check_program P FT s = true -> ~ monitored_program s initial_machine ProtocolError.
```

<a id="declaration-baseline-runtime-equivalence"></a>

### `baseline_runtime_equivalence`

[runtime_monitor.v:300](runtime_monitor.v#L300)

```coq
Theorem baseline_runtime_equivalence FT s : certified P -> check_program P FT s = true ->
  forall m, monitored_program s initial_machine (RuntimeState (m,Skip)) <->
    program_execution s initial_machine m.
```

<a id="declaration-copying-runtime-no-error"></a>

### `copying_runtime_no_error`

[runtime_monitor.v:311](runtime_monitor.v#L311)

```coq
Theorem copying_runtime_no_error FT mode s : copying_certified P mode ->
  check_program_with_copy P FT mode s = true ->
  ~ monitored_program s initial_machine ProtocolError.
```

<a id="declaration-copying-runtime-equivalence"></a>

### `copying_runtime_equivalence`

[runtime_monitor.v:320](runtime_monitor.v#L320)

```coq
Theorem copying_runtime_equivalence FT mode s : copying_certified P mode ->
  check_program_with_copy P FT mode s = true -> forall m,
  monitored_program s initial_machine (RuntimeState (m,Skip)) <->
    program_execution s initial_machine m.
```


## Structural and representation declaration index

Both regex correspondences use `A : finType`, a protocol family `P`,
field types, and an initial expression for each class whose denotation equals
that class protocol. Each regular-seed instance proves that representation
premise. The optional relation takes a per-class `mode`; an enabled assignment
copies the source expression, while ordinary transfers reuse the baseline rules. Surface simulations use an injective location map on the allocated
domain and a well-formed ghost machine. Their results may extend this map
when allocating. Prefix/final property transfers start from the empty machines.

<a id="declaration-instrument-single-exit"></a>

### `instrument_single_exit`

[syntax.v:95](syntax.v#L95)

```coq
Theorem instrument_single_exit {A} (s : statement A) :
  finish_free s -> finish_count (instrument s) = 1.
```

<a id="declaration-instrument-not-source"></a>

### `instrument_not_source`

[syntax.v:98](syntax.v#L98)

```coq
Theorem instrument_not_source {A} (s : statement A) : ~ finish_free (instrument s).
```

<a id="declaration-source-execution-iff"></a>

### `source_execution_iff`

[semantics.v:165](semantics.v#L165)

```coq
Theorem source_execution_iff {A} (s : statement A) m m' :
  program_execution s m m' <-> finish_free s /\
    exists k, execution (m,s) (k,Skip) /\ m'=clear_refs k.
```

<a id="declaration-source-execution-no-early-exit"></a>

### `source_execution_no_early_exit`

[semantics.v:184](semantics.v#L184)

```coq
Theorem source_execution_no_early_exit {A} (c d : configuration A) :
  execution c d -> finish_free (snd c) -> finish_free (snd d).
```

<a id="declaration-raw-step-decompose"></a>

### `raw_step_decompose`

[semantics.v:132](semantics.v#L132)

```coq
Lemma raw_step_decompose {A} (m m' : machine A) s s' : raw_step (m,s) (m',s') ->
  (exists E i, s=plug E i /\ s'=plug E Skip /\ primitive_step i m m') \/
  (exists E t, s=plug E (Seq Skip t) /\ s'=plug E t /\ m'=m).
```

<a id="declaration-raw-step-context"></a>

### `raw_step_context`

[semantics.v:91](semantics.v#L91)

```coq
Lemma raw_step_context {A} (E : context A) m s m' s' :
  raw_step (m,s) (m',s') -> raw_step (m,plug E s) (m',plug E s').
```

<a id="declaration-execution-context"></a>

### `execution_context`

[semantics.v:94](semantics.v#L94)

```coq
Lemma execution_context {A} (E : context A) c d :
  execution c d -> execution (fst c,plug E (snd c)) (fst d,plug E (snd d)).
```

<a id="declaration-check-program-spec"></a>

### `check_program_spec`

[typestate.v:138](typestate.v#L138)

```coq
Theorem check_program_spec s : check_program s = true <->
  finish_free s /\ typed_stmt [] (instrument s) [].
```

<a id="declaration-all-complete-spec"></a>

### `all_complete_spec`

[typestate.v:21](typestate.v#L21)

```coq
Lemma all_complete_spec g : all_complete g = true <->
  forall x c w, get g x = Some (c,w) -> accepts P c w = true.
```

<a id="declaration-source-checker-instrument"></a>

### `source_checker_instrument`

[typestate.v:152](typestate.v#L152)

```coq
Theorem source_checker_instrument s : check_program s = true <->
  finish_free s /\ exists g, check_stmt s []=Some g /\ all_complete g=true.
```

<a id="declaration-invariant-clear-refs"></a>

### `invariant_clear_refs`

[invariants.v:161](invariants.v#L161)

```coq
Lemma invariant_clear_refs m g : invariant m g -> all_complete P g=true ->
  invariant (clear_refs m) [].
```

<a id="declaration-step-preservation"></a>

### `step_preservation`

[invariants.v:203](invariants.v#L203)

```coq
Theorem step_preservation m s m' s' : raw_step (m,s) (m',s') ->
  forall g gf, invariant m g -> typed_stmt P FT g s gf ->
  exists g', invariant m' g' /\ typed_stmt P FT g' s' gf.
```

<a id="declaration-context-preservation"></a>

### `context_preservation`

[invariants.v:227](invariants.v#L227)

```coq
Lemma context_preservation E m s m' s' g gf :
  invariant m g -> typed_stmt P FT g (plug E s) gf -> raw_step (m,s) (m',s') ->
  exists g', invariant m' g' /\ typed_stmt P FT g' (plug E s') gf.
```

<a id="declaration-check-stmt-with-copy-spec"></a>

### `check_stmt_with_copy_spec`

[copying_typestate.v:120](copying_typestate.v#L120)

```coq
Lemma check_stmt_with_copy_spec s g g' :
  check_stmt_with_copy s g = Some g' <-> typed_stmt_with_copy g s g'.
```

<a id="declaration-check-program-with-copy-spec"></a>

### `check_program_with_copy_spec`

[copying_typestate.v:152](copying_typestate.v#L152)

```coq
Lemma check_program_with_copy_spec s :
  check_program_with_copy s = true <->
  finish_free s /\ typed_stmt_with_copy [] (instrument s) [].
```

<a id="declaration-ci-clear-refs"></a>

### `ci_clear_refs`

[copying_soundness.v:245](copying_soundness.v#L245)

```coq
Lemma ci_clear_refs m g V : copying_invariant m g V ->
  all_complete P g = true -> copying_invariant (clear_refs m) [] V.
```

<a id="declaration-copying-step-preservation"></a>

### `copying_step_preservation`

[copying_soundness.v:314](copying_soundness.v#L314)

```coq
Theorem copying_step_preservation m s m' s' g V gf :
  raw_step (m,s) (m',s') -> copying_invariant m g V ->
  typed_stmt_with_copy P FT copy_history g s gf ->
  exists g' V', copying_invariant m' g' V' /\
    typed_stmt_with_copy P FT copy_history g' s' gf.
```

<a id="declaration-copying-context-preservation"></a>

### `copying_context_preservation`

[copying_soundness.v:339](copying_soundness.v#L339)

```coq
Corollary copying_context_preservation E m s m' s' g V gf :
  raw_step (m,s) (m',s') -> copying_invariant m g V ->
  typed_stmt_with_copy P FT copy_history g (plug E s) gf ->
  exists g' V', copying_invariant m' g' V' /\
    typed_stmt_with_copy P FT copy_history g' (plug E s') gf.
```

<a id="declaration-copying-execution-preservation"></a>

### `copying_execution_preservation`

[copying_soundness.v:351](copying_soundness.v#L351)

```coq
Theorem copying_execution_preservation c d g V gf :
  execution c d -> copying_invariant (fst c) g V ->
  typed_stmt_with_copy P FT copy_history g (snd c) gf ->
  exists g' V', copying_invariant (fst d) g' V' /\
    typed_stmt_with_copy P FT copy_history g' (snd d) gf.
```

<a id="declaration-residual-checker-correspondence"></a>

### `residual_checker_correspondence`

[residual_typestate.v:248](residual_typestate.v#L248)

```coq
Theorem residual_checker_correspondence g G s : environments_related g G ->
  ((exists g', check_stmt P field_type s g = Some g') <->
   exists G', regex_typed_stmt G s G').
```

<a id="declaration-residual-program-correspondence"></a>

### `residual_program_correspondence`

[residual_typestate.v:271](residual_typestate.v#L271)

```coq
Theorem residual_program_correspondence s :
  check_program P field_type s = true <->
  finish_free s /\ regex_typed_stmt [] (instrument s) [].
```

<a id="declaration-regular-residual-program-correspondence"></a>

### `regular_residual_program_correspondence`

[residual_typestate.v:300](residual_typestate.v#L300)

```coq
Theorem regular_residual_program_correspondence s :
  check_program (regular_family spec) field_type s = true <->
  finish_free s /\ regex_typed_stmt field_type (fun c => closure_regex (spec c))
    [] (instrument s) [].
```

<a id="declaration-ghost-surface-primitive"></a>

### `ghost_surface_primitive`

[surface_semantics.v:415](surface_semantics.v#L415)

```coq
Theorem ghost_surface_primitive {A} r i (m m' : machine A) M :
  ghost_well_formed m -> represents r m M -> primitive_step i m m' ->
  exists r' M', extends_on (next_loc m) r r' /\
    surface_primitive i M M' /\ represents r' m' M'.
```

<a id="declaration-surface-ghost-primitive"></a>

### `surface_ghost_primitive`

[surface_semantics.v:450](surface_semantics.v#L450)

```coq
Theorem surface_ghost_primitive {A} r i (m : machine A) M M' :
  ghost_well_formed m -> represents r m M -> surface_primitive i M M' ->
  exists r' m', extends_on (next_loc m) r r' /\
    primitive_step i m m' /\ represents r' m' M'.
```

<a id="declaration-ghost-surface-step"></a>

### `ghost_surface_step`

[surface_semantics.v:536](surface_semantics.v#L536)

```coq
Theorem ghost_surface_step {A} r (m m' : machine A) M s s' :
  ghost_well_formed m -> represents r m M -> raw_step (m,s) (m',s') ->
  exists r' M', extends_on (next_loc m) r r' /\
    surface_step (M,s) (M',s') /\ represents r' m' M'.
```

<a id="declaration-surface-ghost-step"></a>

### `surface_ghost_step`

[surface_semantics.v:550](surface_semantics.v#L550)

```coq
Theorem surface_ghost_step {A} r (m : machine A) M M' s s' :
  ghost_well_formed m -> represents r m M -> surface_step (M,s) (M',s') ->
  exists r' m', extends_on (next_loc m) r r' /\
    raw_step (m,s) (m',s') /\ represents r' m' M'.
```

<a id="declaration-ghost-surface-execution"></a>

### `ghost_surface_execution`

[surface_semantics.v:564](surface_semantics.v#L564)

```coq
Theorem ghost_surface_execution {A} (c d : configuration A) r M :
  ghost_well_formed (fst c) -> represents r (fst c) M -> execution c d ->
  exists r' M', extends_on (next_loc (fst c)) r r' /\
    surface_execution (M,snd c) (M',snd d) /\ represents r' (fst d) M'.
```

<a id="declaration-surface-ghost-execution"></a>

### `surface_ghost_execution`

[surface_semantics.v:581](surface_semantics.v#L581)

```coq
Theorem surface_ghost_execution {A} (c d : surface_configuration A) r m :
  ghost_well_formed m -> represents r m (fst c) -> surface_execution c d ->
  exists r' m', extends_on (next_loc m) r r' /\
    execution (m,snd c) (m',snd d) /\ represents r' m' (fst d).
```

<a id="declaration-represents-extensional"></a>

### `represents_extensional`

[surface_semantics.v:650](surface_semantics.v#L650)

```coq
Theorem represents_extensional {A} r (m : machine A) M N :
  represents r m M -> represents r m N -> surface_observationally_equal M N.
```

<a id="declaration-represented-classes-finite"></a>

### `represented_classes_finite`

[surface_semantics.v:676](surface_semantics.v#L676)

```coq
Theorem represented_classes_finite {A} r (m : machine A) M : represents r m M ->
  exists entries : list (loc * class), forall L c,
    surface_classes M L = Some c <-> In (L,c) entries.
```

<a id="declaration-ghost-surface-prefix-safety"></a>

### `ghost_surface_prefix_safety`

[surface_semantics.v:735](surface_semantics.v#L735)

```coq
Corollary ghost_surface_prefix_safety {A} (K : class -> language A) (s : statement A) :
  (forall m, program_prefix s initial_machine m ->
    forall l, l < next_loc m -> prefix_language (K (classes m l)) (object_history m l)) <->
  (forall M, surface_program_prefix s initial_surface M ->
    forall L c, surface_classes M L = Some c -> prefix_language (K c) (surface_history M L)).
```

<a id="declaration-ghost-surface-completion-safety"></a>

### `ghost_surface_completion_safety`

[surface_semantics.v:742](surface_semantics.v#L742)

```coq
Corollary ghost_surface_completion_safety {A} (K : class -> language A) (s : statement A) :
  (forall m, program_execution s initial_machine m ->
    forall l, l < next_loc m -> K (classes m l) (object_history m l)) <->
  (forall M, surface_program_execution s initial_surface M ->
    forall L c, surface_classes M L = Some c -> K c (surface_history M L)).
```

<a id="declaration-monitored-error-context"></a>

### `monitored_error_context`

[runtime_monitor.v:88](runtime_monitor.v#L88)

```coq
Lemma monitored_error_context E m s : monitored_step (m,s) ProtocolError ->
  monitored_step (m,plug E s) ProtocolError.
```

<a id="declaration-monitored-error-terminal"></a>

### `monitored_error_terminal`

[runtime_monitor.v:82](runtime_monitor.v#L82)

```coq
Lemma monitored_error_terminal out : monitored_execution ProtocolError out -> out = ProtocolError.
```

<a id="declaration-baseline-runtime-prefix-equivalence"></a>

### `baseline_runtime_prefix_equivalence`

[runtime_monitor.v:296](runtime_monitor.v#L296)

```coq
Theorem baseline_runtime_prefix_equivalence FT s : certified P -> check_program P FT s = true ->
  forall m t, monitored_prefix s initial_machine (RuntimeState (m,t)) <->
  finish_free s /\ execution (initial_machine,instrument s) (m,t).
```

<a id="declaration-copying-runtime-prefix-equivalence"></a>

### `copying_runtime_prefix_equivalence`

[runtime_monitor.v:315](runtime_monitor.v#L315)

```coq
Theorem copying_runtime_prefix_equivalence FT mode s : copying_certified P mode ->
  check_program_with_copy P FT mode s = true ->
  forall m t, monitored_prefix s initial_machine (RuntimeState (m,t)) <->
  finish_free s /\ execution (initial_machine,instrument s) (m,t).
```

<a id="declaration-copying-primitive-history-to-regex"></a>

### `copying_primitive_history_to_regex`

[copying_residual_typestate.v:56](copying_residual_typestate.v#L56)

```coq
Theorem copying_primitive_history_to_regex g i g' G :
  type_step_with_copy P FT mode g i g' -> environments_related P g G ->
  exists G', regex_copy_type_step G i G' /\ environments_related P g' G'.
```

<a id="declaration-copying-primitive-regex-to-history"></a>

### `copying_primitive_regex_to_history`

[copying_residual_typestate.v:77](copying_residual_typestate.v#L77)

```coq
Theorem copying_primitive_regex_to_history G i G' g :
  regex_copy_type_step G i G' -> environments_related P g G ->
  exists g', type_step_with_copy P FT mode g i g' /\ environments_related P g' G'.
```

<a id="declaration-copying-statement-history-to-regex"></a>

### `copying_statement_history_to_regex`

[copying_residual_typestate.v:95](copying_residual_typestate.v#L95)

```coq
Theorem copying_statement_history_to_regex g s g' G :
  typed_stmt_with_copy P FT mode g s g' -> environments_related P g G ->
  exists G', regex_copy_typed_stmt G s G' /\ environments_related P g' G'.
```

<a id="declaration-copying-statement-regex-to-history"></a>

### `copying_statement_regex_to_history`

[copying_residual_typestate.v:107](copying_residual_typestate.v#L107)

```coq
Theorem copying_statement_regex_to_history G s G' g :
  regex_copy_typed_stmt G s G' -> environments_related P g G ->
  exists g', typed_stmt_with_copy P FT mode g s g' /\ environments_related P g' G'.
```

<a id="declaration-copying-residual-checker-correspondence"></a>

### `copying_residual_checker_correspondence`

[copying_residual_typestate.v:119](copying_residual_typestate.v#L119)

```coq
Theorem copying_residual_checker_correspondence g G s : environments_related P g G ->
  ((exists g', check_stmt_with_copy P FT mode s g = Some g') <->
   exists G', regex_copy_typed_stmt G s G').
```

<a id="declaration-copying-residual-program-correspondence"></a>

### `copying_residual_program_correspondence`

[copying_residual_typestate.v:149](copying_residual_typestate.v#L149)

```coq
Theorem copying_residual_program_correspondence s :
  check_program_with_copy P FT mode s = true <->
  finish_free s /\ regex_copy_typed_stmt [] (instrument s) [].
```

<a id="declaration-copying-regular-residual-program-correspondence"></a>

### `copying_regular_residual_program_correspondence`

[copying_residual_typestate.v:170](copying_residual_typestate.v#L170)

```coq
Theorem copying_regular_residual_program_correspondence s :
  check_program_with_copy (regular_family spec) FT mode s = true <->
  finish_free s /\ regex_copy_typed_stmt FT (fun c => closure_regex (spec c)) mode
    [] (instrument s) [].
```

<a id="declaration-raw-step-iff-context"></a>

### `raw_step_iff_context`

[semantics.v:196](semantics.v#L196)

```coq
Theorem raw_step_iff_context {A} (m m' : machine A) s s' : raw_step (m,s) (m',s') <->
  (exists E i, s=plug E i /\ s'=plug E Skip /\ primitive_step i m m') \/
  (exists E t, s=plug E (Seq Skip t) /\ s'=plug E t /\ m'=m).
```

<a id="declaration-reachable-invariant"></a>

### `reachable_invariant`

[soundness.v:65](soundness.v#L65)

```coq
Theorem reachable_invariant s m u : check_program P FT s=true ->
  execution (initial_machine,instrument s) (m,u) ->
  exists g, invariant P FT m g /\ typed_stmt P FT g u [].
```

<a id="declaration-runtime-surface-guard"></a>

### `runtime_surface_guard`

[surface_monitor.v:22](surface_monitor.v#L22)

```coq
Lemma runtime_surface_guard {A} (P : protocol_family A) r s (m m' : machine A) M :
  ghost_well_formed m -> represents r m M -> primitive_step s m m' ->
  (runtime_guard P s m m' = true <-> surface_guard P s M).
```

<a id="declaration-ghost-surface-monitored-execution"></a>

### `ghost_surface_monitored_execution`

[surface_monitor.v:147](surface_monitor.v#L147)

```coq
Theorem ghost_surface_monitored_execution r m m' M s t :
  ghost_well_formed m -> represents r m M ->
  monitored_execution P (RuntimeState (m,s)) (RuntimeState (m',t)) ->
  exists r' M', extends_on (next_loc m) r r' /\
    surface_monitored_execution (SurfaceState (M,s)) (SurfaceState (M',t)) /\
    represents r' m' M'.
```

<a id="declaration-surface-ghost-monitored-execution"></a>

### `surface_ghost_monitored_execution`

[surface_monitor.v:170](surface_monitor.v#L170)

```coq
Theorem surface_ghost_monitored_execution r m M M' s t :
  ghost_well_formed m -> represents r m M ->
  surface_monitored_execution (SurfaceState (M,s)) (SurfaceState (M',t)) ->
  exists r' m', extends_on (next_loc m) r r' /\
    monitored_execution P (RuntimeState (m,s)) (RuntimeState (m',t)) /\
    represents r' m' M'.
```

<a id="declaration-ghost-surface-error-equivalence"></a>

### `ghost_surface_error_equivalence`

[surface_monitor.v:227](surface_monitor.v#L227)

```coq
Theorem ghost_surface_error_equivalence s :
  monitored_program P s initial_machine ProtocolError <->
  surface_monitored_program s initial_surface SurfaceProtocolError.
```

<a id="declaration-surface-typestate-prefix-sound"></a>

### `surface_typestate_prefix_sound`

[surface_monitor.v:311](surface_monitor.v#L311)

```coq
Theorem surface_typestate_prefix_sound FT s M : certified P -> check_program P FT s = true ->
  surface_program_prefix s initial_surface M ->
  forall l c, surface_classes M l = Some c -> prefix_language (protocol P c) (surface_history M l).
```

<a id="declaration-surface-typestate-completion-sound"></a>

### `surface_typestate_completion_sound`

[surface_monitor.v:319](surface_monitor.v#L319)

```coq
Theorem surface_typestate_completion_sound FT s M : certified P -> check_program P FT s = true ->
  surface_program_execution s initial_surface M ->
  forall l c, surface_classes M l = Some c -> protocol P c (surface_history M l).
```

<a id="declaration-surface-copying-prefix-sound"></a>

### `surface_copying_prefix_sound`

[surface_monitor.v:344](surface_monitor.v#L344)

```coq
Theorem surface_copying_prefix_sound FT mode s M :
  copying_certified P mode -> check_program_with_copy P FT mode s = true ->
  surface_program_prefix s initial_surface M ->
  forall l c, surface_classes M l = Some c -> prefix_language (protocol P c) (surface_history M l).
```

<a id="declaration-surface-copying-completion-sound"></a>

### `surface_copying_completion_sound`

[surface_monitor.v:353](surface_monitor.v#L353)

```coq
Theorem surface_copying_completion_sound FT mode s M :
  copying_certified P mode -> check_program_with_copy P FT mode s = true ->
  surface_program_execution s initial_surface M ->
  forall l c, surface_classes M l = Some c -> protocol P c (surface_history M l).
```

<a id="declaration-surface-runtime-prefix-equivalence"></a>

### `surface_runtime_prefix_equivalence`

[surface_monitor.v:327](surface_monitor.v#L327)

```coq
Theorem surface_runtime_prefix_equivalence FT s : certified P -> check_program P FT s = true ->
  forall M t, surface_monitored_prefix s initial_surface (SurfaceState (M,t)) <->
    finish_free s /\ surface_execution (initial_surface,instrument s) (M,t).
```

<a id="declaration-surface-runtime-equivalence"></a>

### `surface_runtime_equivalence`

[surface_monitor.v:332](surface_monitor.v#L332)

```coq
Theorem surface_runtime_equivalence FT s : certified P -> check_program P FT s = true ->
  forall M, surface_monitored_program s initial_surface (SurfaceState (M,Skip)) <->
    surface_program_execution s initial_surface M.
```

<a id="declaration-surface-runtime-no-error"></a>

### `surface_runtime_no_error`

[surface_monitor.v:337](surface_monitor.v#L337)

```coq
Theorem surface_runtime_no_error FT s : certified P -> check_program P FT s = true ->
  ~ surface_monitored_program s initial_surface SurfaceProtocolError.
```

<a id="declaration-surface-copying-runtime-prefix-equivalence"></a>

### `surface_copying_runtime_prefix_equivalence`

[surface_monitor.v:362](surface_monitor.v#L362)

```coq
Theorem surface_copying_runtime_prefix_equivalence FT mode s : copying_certified P mode ->
  check_program_with_copy P FT mode s = true ->
  forall M t, surface_monitored_prefix s initial_surface (SurfaceState (M,t)) <->
    finish_free s /\ surface_execution (initial_surface,instrument s) (M,t).
```

<a id="declaration-surface-copying-runtime-equivalence"></a>

### `surface_copying_runtime_equivalence`

[surface_monitor.v:368](surface_monitor.v#L368)

```coq
Theorem surface_copying_runtime_equivalence FT mode s : copying_certified P mode ->
  check_program_with_copy P FT mode s = true ->
  forall M, surface_monitored_program s initial_surface (SurfaceState (M,Skip)) <->
    surface_program_execution s initial_surface M.
```

<a id="declaration-surface-copying-runtime-no-error"></a>

### `surface_copying_runtime_no_error`

[surface_monitor.v:374](surface_monitor.v#L374)

```coq
Theorem surface_copying_runtime_no_error FT mode s : copying_certified P mode ->
  check_program_with_copy P FT mode s = true ->
  ~ surface_monitored_program s initial_surface SurfaceProtocolError.
```

<a id="declaration-surface-completion-sound-iff-certified"></a>

### `surface_completion_sound_iff_certified`

[surface_monitor.v:396](surface_monitor.v#L396)

```coq
Theorem surface_completion_sound_iff_certified FT :
  (forall s M, check_program P FT s = true ->
    surface_program_execution s initial_surface M ->
    forall l c, surface_classes M l = Some c -> protocol P c (surface_history M l)) <->
  certified P.
```

<a id="declaration-noncanonical-surface-execution"></a>

### `noncanonical_surface_execution`

[surface_monitor.v:414](surface_monitor.v#L414)

```coq
Example noncanonical_surface_execution {A} c d :
  surface_program_execution (@noncanonical_source A c d) initial_surface (noncanonical_final c d).
```

<a id="declaration-noncanonical-surface-equipped"></a>

### `noncanonical_surface_equipped`

[surface_monitor.v:435](surface_monitor.v#L435)

```coq
Example noncanonical_surface_equipped {A} c d :
  exists r m, program_execution (@noncanonical_source A c d) initial_machine m /\
    represents r m (noncanonical_final c d).
```

<a id="declaration-canonical-statement-typing"></a>

### `canonical_statement_typing`

[residual_invariants.v:89](residual_invariants.v#L89)

```coq
Theorem canonical_statement_typing g s g' : typed_stmt P FT g s g' ->
  regex_typed_stmt FT initial (canonical_env initial g) s (canonical_env initial g').
```

<a id="declaration-canonical-copying-statement-typing"></a>

### `canonical_copying_statement_typing`

[residual_invariants.v:166](residual_invariants.v#L166)

```coq
Theorem canonical_copying_statement_typing g s g' : typed_stmt_with_copy P FT mode g s g' ->
  regex_copy_typed_stmt FT initial mode (canonical_env initial g) s (canonical_env initial g').
```

<a id="declaration-reachable-residual-configuration"></a>

### `reachable_residual_configuration`

[residual_invariants.v:124](residual_invariants.v#L124)

```coq
Theorem reachable_residual_configuration s m t :
  check_program P FT s=true -> execution (initial_machine,instrument s) (m,t) ->
  exists G, regex_typed_stmt FT initial G t [] /\ residual_runtime_invariant m G.
```

<a id="declaration-copying-reachable-residual-configuration"></a>

### `copying_reachable_residual_configuration`

[residual_invariants.v:208](residual_invariants.v#L208)

```coq
Theorem copying_reachable_residual_configuration s m t : copying_certified P mode ->
  check_program_with_copy P FT mode s=true -> execution (initial_machine,instrument s) (m,t) ->
  exists G V, regex_copy_typed_stmt FT initial mode G t [] /\
    copying_residual_runtime_invariant m G V.
```

<a id="declaration-regular-reachable-residual-configuration"></a>

### `regular_reachable_residual_configuration`

[residual_invariants.v:226](residual_invariants.v#L226)

```coq
Theorem regular_reachable_residual_configuration s m t :
  check_program (regular_family spec) FT s=true ->
  execution (initial_machine,instrument s) (m,t) ->
  exists G, regex_typed_stmt FT (fun c => closure_regex (spec c)) G t [] /\
    residual_runtime_invariant (regular_family spec) m G.
```

<a id="declaration-copying-regular-reachable-residual-configuration"></a>

### `copying_regular_reachable_residual_configuration`

[residual_invariants.v:235](residual_invariants.v#L235)

```coq
Theorem copying_regular_reachable_residual_configuration mode s m t :
  copying_certified (regular_family spec) mode ->
  check_program_with_copy (regular_family spec) FT mode s=true ->
  execution (initial_machine,instrument s) (m,t) ->
  exists G V, regex_copy_typed_stmt FT (fun c => closure_regex (spec c)) mode G t [] /\
    copying_residual_runtime_invariant (regular_family spec) FT m G V.
```

## Exact-protocol declaration index

<a id="declaration-exact-dfa-family-language"></a>

### `exact_dfa_family_language`

Source: [exact_protocols.v:18](exact_protocols.v#L18).

```coq
Theorem exact_dfa_family_language spec c w :
  protocol (exact_dfa_family spec) c w <-> (w \in dfa_lang (spec c)) = true.
```

<a id="declaration-exact-dfa-family-viable"></a>

### `exact_dfa_family_viable`

Source: [exact_protocols.v:22](exact_protocols.v#L22).

```coq
Theorem exact_dfa_family_viable spec c w :
  viable (exact_dfa_family spec) c w = true <->
  exists v, (w ++ v \in dfa_lang (spec c)) = true.
```

<a id="declaration-certify-exact-dfa-spec"></a>

### `certify_exact_dfa_spec`

Source: [exact_protocols.v:33](exact_protocols.v#L33).

```coq
Theorem certify_exact_dfa_spec D : certify_exact_dfa D = true <->
  shuffle_closed (fun w => (w \in dfa_lang D) = true).
```

<a id="declaration-exact-regex-family-language"></a>

### `exact_regex_family_language`

Source: [exact_protocols.v:44](exact_protocols.v#L44).

```coq
Theorem exact_regex_family_language spec c w :
  protocol (exact_regex_family spec) c w <-> (w \in spec c) = true.
```

<a id="declaration-certify-exact-regex-spec"></a>

### `certify_exact_regex_spec`

Source: [exact_protocols.v:61](exact_protocols.v#L61).

```coq
Theorem certify_exact_regex_spec r : certify_exact_regex r = true <->
  shuffle_closed (fun w => (w \in r) = true).
```

<a id="declaration-exact-dfa-program-completion-sound"></a>

### `exact_dfa_program_completion_sound`

Source: [exact_protocols.v:78](exact_protocols.v#L78).

```coq
Theorem exact_dfa_program_completion_sound spec FT s m :
  (forall c, certify_exact_dfa (spec c) = true) ->
  check_program (exact_dfa_family spec) FT s = true ->
  program_execution s initial_machine m ->
  forall l, (l < next_loc m)%coq_nat ->
  (object_history m l \in dfa_lang (spec (classes m l))) = true.
```

<a id="declaration-k-last-exact-dfa-queries"></a>

### `k_last_exact_dfa_queries`

Source: [exact_protocol_examples.v:142](exact_protocol_examples.v#L142).

```coq
Theorem k_last_exact_dfa_queries c w :
  accepts k_last_family c w = accepts (exact_dfa_family (fun _ => k_last_dfa)) c w /\
  viable k_last_family c w = viable (exact_dfa_family (fun _ => k_last_dfa)) c w.
```

<a id="declaration-k-last-exact-language"></a>

### `k_last_exact_language`

Source: [exact_protocol_examples.v:154](exact_protocol_examples.v#L154).

```coq
Theorem k_last_exact_language c w : protocol k_last_family c w <-> k_last w.
```

<a id="declaration-k-last-shuffle-closed"></a>

### `k_last_shuffle_closed`

Source: [exact_protocol_examples.v:92](exact_protocol_examples.v#L92).

```coq
Theorem k_last_shuffle_closed : shuffle_closed k_last.
```

<a id="declaration-k-last-exact-certificate"></a>

### `k_last_exact_certificate`

Source: [exact_protocol_examples.v:158](exact_protocol_examples.v#L158).

```coq
Theorem k_last_exact_certificate : certify_exact_dfa k_last_dfa = true.
```

<a id="declaration-k-last-complete-client-accepted"></a>

### `k_last_complete_client_accepted`

Source: [exact_protocol_examples.v:184](exact_protocol_examples.v#L184).

```coq
Example k_last_complete_client_accepted :
  check_program k_last_family k_last_fields k_last_complete_client = true.
```

<a id="declaration-k-last-incomplete-client-rejected"></a>

### `k_last_incomplete_client_rejected`

Source: [exact_protocol_examples.v:187](exact_protocol_examples.v#L187).

```coq
Example k_last_incomplete_client_rejected :
  check_program k_last_family k_last_fields k_last_incomplete_client = false.
```

<a id="declaration-k-last-complete-client-terminates"></a>

### `k_last_complete_client_terminates`

Source: [exact_protocol_examples.v:196](exact_protocol_examples.v#L196).

```coq
Example k_last_complete_client_terminates :
  program_execution k_last_complete_client initial_machine k_last_complete_final.
```

<a id="declaration-k-last-client-completion-sound"></a>

### `k_last_client_completion_sound`

Source: [exact_protocol_examples.v:207](exact_protocol_examples.v#L207).

```coq
Theorem k_last_client_completion_sound m :
  program_execution k_last_complete_client initial_machine m ->
  forall l, (l < next_loc m)%coq_nat -> k_last (object_history m l).
```

<a id="declaration-ub-seed-accepts-ubu"></a>

### `ub_seed_accepts_ubu`

Source: [exact_protocol_examples.v:219](exact_protocol_examples.v#L219).

```coq
Example ub_seed_accepts_ubu : accepts ub_seed_family 0 [::false;true;false] = true.
```

<a id="declaration-k-last-not-pumping-closed"></a>

### `k_last_not_pumping_closed`

Source: [exact_protocol_examples.v:228](exact_protocol_examples.v#L228).

```coq
Example k_last_not_pumping_closed :
  k_last [::false;true] /\
  @pumping B false [::false;true] [::false;true;false] /\
  ~ k_last [::false;true;false].
```
