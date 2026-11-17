# Paper claims and Rocq theorems

This map expands the result index in [the artifact guide](../paper/ARTIFACT_README.md).
It distinguishes what the Rocq development proves from the paper's mathematical
arguments, presentation refinements, and implementation boundaries. The map is
about the current source declarations. Build and reproduction instructions are
in [README.md](README.md).

**The main result is an end-to-end trace guarantee.** Successful regular-seed
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
runs, whose exit guard enforces acceptance by definition. The new monitor proves
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

All formal signatures linked below are reproduced verbatim in the declaration
index. Section parameters are generalized theorem parameters, not extra axioms.
LaTeX labels identify paper results independently of their printed numbering.

## Claim extraction and traceability

### Runtime-monitor extension

These results formalize the runtime checks requested for Section 6, while
preserving the original raw theorems. Guards inspect aggregate object histories;
the static checker continues to track independent binding histories.

| Claim | Evidence | Verdict and boundary |
| --- | --- | --- |
| Allocation checks empty-history viability; calls check the updated receiver history, with explicit failure outcomes. | `runtime_guard`, `monitored_step`, [`runtime_call_guard`](#declaration-runtime-call-guard); `empty_protocol_allocation_errors`, `invalid_call_monitor_errors` | PROVEN for the core. Failed guards produce `ProtocolError`; undefined ordinary accesses retain the raw semantics' lack of a step. |
| Program exit checks completion for every allocated object, including unreachable objects. | [`runtime_exit_check_spec`](#declaration-runtime-exit-check-spec), `incomplete_retired_object_program_errors` | PROVEN. The final check occurs once at the selected path's end, not at each `Finish x`. |
| Individual retirement preserves the aggregate completion predicate. | [`runtime_exit_check_retire`](#declaration-runtime-exit-check-retire), `individual_finish_allows_other_incomplete_object` | PROVEN. Checking the final predicate before or after retirements gives the same Boolean result. This does not formalize full surface instrumentation. |
| Accepted baseline and inherited-history programs cannot signal protocol errors. | [`baseline_runtime_no_error`](#declaration-baseline-runtime-no-error), [`copying_runtime_no_error`](#declaration-copying-runtime-no-error) | PROVEN under ordinary shuffle certification or mode-aware certification respectively. Both rely on raw prefix/completion soundness rather than assuming the guards. |
| Adding the monitor preserves exactly the successful complete executions of accepted programs. | [`baseline_runtime_equivalence`](#declaration-baseline-runtime-equivalence), [`copying_runtime_equivalence`](#declaration-copying-runtime-equivalence) | PROVEN in both directions with identical final core machines. Explicit accepted monitored runs establish nonvacuity. Initialization progress and general termination remain outside the result. |

The paper's bulk `finish` and automatic insertion still require a separate
source-to-core translation. The monitor closes the explicit runtime-error gap
for the existing core; it does not claim to close the regex/environment-set or
bulk-instrumentation correspondence gaps listed below.

### Earlier language and checker results

The first table paraphrases the formal claims from the current abstract,
introduction, contribution list, and conclusion. Repeated claims remain visible
so that an abstract-level statement can be checked without inferring its intended
scope from the body. The next table covers every numbered lemma, proposition, and
theorem in the technical development. Paper links identify source files, with
section or result labels in the link text where available, rather than source
line numbers. The first table's paraphrases are not verbatim quotations.

| Claim and source | Current paper claim (paraphrased) | Evidence | Verdict | Exact scope or gap |
| --- | --- | --- | --- | --- |
| A1 [Abstract](../paper/abstract.tex) | Alias tracking can be omitted when operations through one reference preserve permissions established through other references to the same object. | [`typestate_prefix_sound`](#declaration-typestate-prefix-sound), [`typestate_completion_sound`](#declaration-typestate-completion-sound) | PROVEN, scoped | The formal result is for the specified independent-history checker and certified protocol family, not an arbitrary analysis satisfying an informal persistence description. |
| A2 [Abstract](../paper/abstract.tex) | The paper formalizes a checker that tracks references independently and gives a necessary and sufficient protocol condition for that checking discipline. | [`typestate_prefix_sound`](#declaration-typestate-prefix-sound), [`typestate_completion_sound`](#declaration-typestate-completion-sound), [`completion_sound_requires_certified`](#declaration-completion-sound-requires-certified), [`completion_sound_iff_certified`](#declaration-completion-sound-iff-certified) | PROVEN for the core | For this fixed baseline checker, raw all-object completion soundness holds exactly when every class protocol is shuffle closed. Paper-to-core surface correspondence remains separate. This does not characterize all analyses without aliases. |
| A3 [Abstract](../paper/abstract.tex) | Calls through aliases interleave into one object history. Every interleaving of permitted complete histories must therefore remain permitted. | [`project_partition`](#declaration-project-partition), [`tagged_shuffle_closed`](#declaration-tagged-shuffle-closed), [`invariant_object_language`](#declaration-invariant-object-language) | PROVEN | Fresh epoch histories partition actual calls. Inherited histories instead use completing continuations. They do not form this partition. |
| A4 [Abstract](../paper/abstract.tex) | Regular expressions describe representative histories from which candidate protocols are constructed. A decision procedure certifies shuffle closedness or returns a counterexample. | [`pumping_normalize_correct`](#declaration-pumping-normalize-correct), [`closure_regex_correct`](#declaration-closure-regex-correct), [`certify_regex_spec`](#declaration-certify-regex-spec), [`regex_counterexample_complete`](#declaration-regex-counterexample-complete), [`regex_counterexample_none`](#declaration-regex-counterexample-none), [`regex_counterexample_sound`](#declaration-regex-counterexample-sound) | PROVEN | Finite regular-expression input, finite inhabited alphabet for the pumping relation. Total Rocq definitions give termination. No practical runtime bound is claimed. |
| A5 [Abstract](../paper/abstract.tex) | The paper connects its condition to accumulation analysis and gives a supported protocol whose safe histories violate the accumulation condition. | [`kellogg_error_closed_iff_residual_prefix_shuffle_closed`](#declaration-kellogg-error-closed-iff-residual-prefix-shuffle-closed), [`accumulation_contract_residual_shuffle_closed`](#declaration-accumulation-contract-residual-shuffle-closed), [`separating_certified_not_kellogg`](#declaration-separating-certified-not-kellogg) | PROVEN, scoped | The bridge extracts a first-error trace law and interprets non-error as extendibility to completion. It does not formalize the other analysis or compare accepted client programs. |
| A6 [Abstract](../paper/abstract.tex) | For accepted programs, execution remains safe and every allocated object’s history is accepted at termination. | [`regular_program_prefix_sound`](#declaration-regular-program-prefix-sound), [`regular_program_completion_sound`](#declaration-regular-program-completion-sound), [`copying_regular_program_prefix_sound`](#declaration-copying-regular-program-prefix-sound), [`copying_regular_program_completion_sound`](#declaration-copying-regular-program-completion-sound) | PROVEN, scoped | Accepted instrumented core programs. Completed execution is a premise. Explicit Finish x and the model boundaries below apply. Initialization progress and termination are not conclusions. |
| A7 [Abstract](../paper/abstract.tex) | The Rocq development has approximately 5,700 lines of definitions and proofs and verifies the language constructions, certification procedures, and core checker soundness without additional axioms. | [audit.v](audit.v), `coqwc *.v`, [build instructions](README.md) | PROVEN for audited results / SOURCE/BUILD FACT for size | The line count is a reproducible size report, not a theorem. Principal theorem assumption reports establish the no-additional-axioms claim. Optional minimal-corpus results use classical logic. |
| I1 [Introduction, `sec:intro`](../paper/introduction.tex) | The sequential checker tracks each binding’s local history. Baseline assignment starts a fresh history, calls update only the receiver and require viability, and each binding must complete before it is discarded or the program exits. | [`check_step_sound`](#declaration-check-step-sound), [`check_step_complete`](#declaration-check-step-complete), [`check_trace_spec`](#declaration-check-trace-spec) | PROVEN | See the primitive-rule comparison below. Completion of a single alias does not discharge other bindings. |
| I2 [Introduction, `sec:intro`](../paper/introduction.tex) | For any nonempty regular shuffle-closed protocol, accepted programs are safe at every execution prefix, and all allocated objects have complete histories at termination, including unreachable objects. | [`typestate_prefix_sound`](#declaration-typestate-prefix-sound), [`typestate_completion_sound`](#declaration-typestate-completion-sound) | PROVEN, scoped | The quantified locations satisfy l < next_loc m, with no reachability restriction. |
| I3 [Introduction, `sec:intro`](../paper/introduction.tex) | Shuffle closedness is necessary for the stated discipline, which accepts every locally valid history. | [`completion_sound_requires_certified`](#declaration-completion-sound-requires-certified) | PROVEN, scoped | The converse constructs a baseline two-binding client for arbitrary complete histories and their chosen interleaving. It concerns this fixed checker, not every checker without alias information. |
| I4 [Introduction, `sec:intro`](../paper/introduction.tex) | Pumping closure preserves regularity for arbitrary regular seed languages. An exact condition on seeds yields a terminating certification procedure with counterexamples given by seed histories and their interleavings. | [`pumping_closure_regular_regex`](#declaration-pumping-closure-regular-regex), [`certify_regex_spec`](#declaration-certify-regex-spec), [`regex_counterexample_complete`](#declaration-regex-counterexample-complete), [`regex_counterexample_none`](#declaration-regex-counterexample-none), [`regex_counterexample_sound`](#declaration-regex-counterexample-sound) | PROVEN | Regular languages are given by expressions. The mechanized pumping representation uses a finite inhabited alphabet. The mathematical empty-alphabet case is discussed separately. |
| I5 [Introduction, `sec:intro`](../paper/introduction.tex) | For selected classes, assignment may inherit the source history under a stronger certificate for composing continuations. This optional rule preserves prefix safety and all-object completion. | [`copy_step_spec`](#declaration-copy-step-spec), [`copying_program_prefix_sound`](#declaration-copying-program-prefix-sound), [`copying_program_completion_sound`](#declaration-copying-program-completion-sound), [`certify_copying_regex_spec`](#declaration-certify-copying-regex-spec) | PROVEN, scoped | copying_certified requires ordinary shuffle closure for every class and residual shuffle closure for enabled classes. Allocation and field loading stay fresh. Target retirement is still required. |
| I6 [Introduction, `sec:intro`](../paper/introduction.tex) | Interpreting safe histories as extendible to completion connects accumulation to composition of continuations. The accumulation condition and a separate completion condition imply the certificates for both modes. A shuffle-closed protocol violates the accumulation condition, giving a language-level separation. | [`kellogg_error_closed_iff_residual_prefix_shuffle_closed`](#declaration-kellogg-error-closed-iff-residual-prefix-shuffle-closed), [`kellogg_regular_certificates`](#declaration-kellogg-regular-certificates), [`kellogg_protocol_copying_certified`](#declaration-kellogg-protocol-copying-certified), [`separating_certified_not_kellogg`](#declaration-separating-certified-not-kellogg) | PROVEN, scoped | Completion stability is a distinct sufficient premise. The safety equivalence concerns derivatives of prefix_language K, not derivatives of K. |
| I7 [Introduction, contribution 1, `sec:intro`](../paper/introduction.tex) | The first contribution is an independent-reference typestate system, its exact protocol condition, prefix-safety and completion guarantees, and an optional history-inheritance rule. | [`typestate_prefix_sound`](#declaration-typestate-prefix-sound), [`typestate_completion_sound`](#declaration-typestate-completion-sound), [`copying_program_prefix_sound`](#declaration-copying-program-prefix-sound), [`copying_program_completion_sound`](#declaration-copying-program-completion-sound) | WEAKER | The core guarantees and baseline necessity are proven. The paper-to-core instrumentation and residual-environment correspondence remain paper-level. |
| I8 [Introduction, contribution 2, `sec:intro`](../paper/introduction.tex) | The second contribution constructs certified protocols from regular seed specifications through regularity-preserving pumping closure and an exact, terminating seed criterion that returns counterexamples on failure. | [`pumping_normalize_correct`](#declaration-pumping-normalize-correct), [`pumping_closure_regular_regex`](#declaration-pumping-closure-regular-regex), [`seed_shuffle_coveredP`](#declaration-seed-shuffle-coveredP), [`base_shuffle_coveredP`](#declaration-base-shuffle-coveredP), [`certify_regex_spec`](#declaration-certify-regex-spec), [`regex_counterexample_complete`](#declaration-regex-counterexample-complete), [`regex_counterexample_none`](#declaration-regex-counterexample-none), [`regex_counterexample_sound`](#declaration-regex-counterexample-sound) | PROVEN | The signature restrictions on alphabets and seed predicates are listed below. |
| I9 [Introduction, contribution 3, `sec:intro`](../paper/introduction.tex) | The third contribution connects accumulation analysis to both checking modes through sufficient safety and completion conditions, and gives a certified protocol outside the accumulation condition. | [`kellogg_program_prefix_sound`](#declaration-kellogg-program-prefix-sound), [`kellogg_program_completion_sound`](#declaration-kellogg-program-completion-sound), [`separating_certified_not_kellogg`](#declaration-separating-certified-not-kellogg) | PROVEN, scoped | The connection is semantic, under the extracted first-error interpretation and separate completion premise. |
| I10 [Introduction, contribution 4, `sec:intro`](../paper/introduction.tex) | The fourth contribution mechanizes the language constructions, certificates, accumulation connection, and core checker soundness in Rocq. | [`pumping_normalize_correct`](#declaration-pumping-normalize-correct), [`certify_regex_spec`](#declaration-certify-regex-spec), [`kellogg_regular_certificates`](#declaration-kellogg-regular-certificates), [`regular_program_completion_sound`](#declaration-regular-program-completion-sound) | PROVEN | The cited Rocq modules implement this chain. |
| I11 [Introduction, `sec:intro`](../paper/introduction.tex) | The principal Rocq theorems connect successful certification to prefix safety and completion in the core calculus without additional axioms. | [`regular_program_prefix_sound`](#declaration-regular-program-prefix-sound), [`regular_program_completion_sound`](#declaration-regular-program-completion-sound), [`copying_regular_program_prefix_sound`](#declaration-copying-regular-program-prefix-sound), [`copying_regular_program_completion_sound`](#declaration-copying-regular-program-completion-sound) | PROVEN | See audit.v and the trust boundary below. Generalized protocol/certification hypotheses remain explicit inputs. |
| I12 [Introduction, `sec:intro`](../paper/introduction.tex) | The Rocq development has approximately 5,700 project definition and proof lines, excluding bundled RegLang, and builds on Mathematical Components. | `coqwc *.v`, [build instructions](README.md) | SOURCE/BUILD FACT | The approximate count concerns project definitions and proofs, excluding bundled RegLang. It is not a mechanized mathematical claim. |
| C1 [Conclusion, `sec:conclusion`](../paper/body.tex) | Pumping closure constructs regular protocols from regular seed specifications. A finite seed criterion decides shuffle closedness of the result. | [`pumping_closure_regular_regex`](#declaration-pumping-closure-regular-regex), [`certify_regex_spec`](#declaration-certify-regex-spec) | PROVEN | Same regular-language and alphabet scope as A4. |
| C2 [Conclusion, `sec:conclusion`](../paper/body.tex) | Shuffle closedness characterizes sound composition for the baseline checker. Accepted programs preserve viable object histories at every prefix and complete every allocated object at termination. | [`typestate_prefix_sound`](#declaration-typestate-prefix-sound), [`typestate_completion_sound`](#declaration-typestate-completion-sound), [`completion_sound_iff_certified`](#declaration-completion-sound-iff-certified) | PROVEN for the core | Checker environments store class/history pairs. The equivalence is specific to the baseline checker. Paper-to-core correspondence remains separate. |
| C3 [Conclusion, `sec:conclusion`](../paper/body.tex) | An optional stronger certificate allows assignment to inherit source histories while completion checks remain independent. Every reachable derivative must be shuffle closed. | [`certify_residuals_spec`](#declaration-certify-residuals-spec), [`copying_program_prefix_sound`](#declaration-copying-program-prefix-sound), [`copying_program_completion_sound`](#declaration-copying-program-completion-sound) | PROVEN | All prefixes induce reachable DFA states. The certificate includes the initial derivative. Empty derivatives satisfy closure vacuously. |
| C4 [Conclusion, `sec:conclusion`](../paper/body.tex) | The accumulation bridge supplies sufficient semantic premises for both checker modes. | [`kellogg_protocol_copying_certified`](#declaration-kellogg-protocol-copying-certified), [`kellogg_program_prefix_sound`](#declaration-kellogg-program-prefix-sound), [`kellogg_program_completion_sound`](#declaration-kellogg-program-completion-sound) | PROVEN | The bridge adds no executable decision procedure for its semantic premises. |

### Numbered formal results

Statements below reproduce the named results, omitting their labels and
normalizing line breaks for the table.

| Paper result and statement (LaTeX, with line breaks normalized) | Mechanized evidence | Verdict | Exact scope or gap |
| --- | --- | --- | --- |
| [lem:context](../paper/regularity.tex)<br>If $s\pumpsto^*u$ and $t\pumpsto^*v$, then $st\pumpsto^*uv$.<br>In particular, a pumping derivation remains valid after adding a common prefix or suffix on both sides. | [`pumping_closure_cat`](#declaration-pumping-closure-cat) | PROVEN | Concatenation is compatible with pumping. This does not assert distribution of pumping closure over concatenation. |
| [lem:singleton](../paper/regularity.tex)<br>For every seed $s$, $\denote{C(s)}=\pc{\set{s}}$. | [`pumping_closure_singleton_correct`](#declaration-pumping-closure-singleton-correct) | PROVEN | Repeated seed milestones remain distinct occurrences. The formal representation takes char:finType and d0:char. |
| [lem:star-basis](../paper/regularity.tex)<br>For every regular expression $r$ over $\Sigma$, with $k=&#124;\Sigma&#124;$, $\pc{\denote{r^*}}=\pc{\denote{B_k(r)}}$. | [`pumping_closure_star_finite_basis`](#declaration-pumping-closure-star-finite-basis) | PROVEN | bounded_star_basis uses the alphabet cardinality, bounding factor count rather than factor lengths. |
| [thm:normalization](../paper/regularity.tex)<br>For every regular expression $r$, $F(r)$ is finite and<br>\[<br>\pc{\denote{r}}=\pc{F(r)}.<br>\] | [`eliminate_star_correct`](#declaration-eliminate-star-correct), [`eliminate_star_star_free`](#declaration-eliminate-star-star-free), [`star_free_finite`](#declaration-star-free-finite), [`words_of_star_free_correct`](#declaration-words-of-star-free-correct), [`pumping_normalize_correct`](#declaration-pumping-normalize-correct) | PROVEN | F(r) is represented by words_of_star_free (eliminate_star r). Closure equality, not equality of original seed languages or minimality, is proved. |
| [thm:regularity](../paper/regularity.tex)<br>Algorithm~\ref{alg:construct} terminates on every regular expression $r$ and returns a finite set $F$ and a regular expression $P$ such that<br>\[<br>F=F(r),\qquad \denote{P}=\pc{F}=\pc{\denote{r}}.<br>\]<br>Consequently, pumping closure preserves regularity. | [`pumping_closure_regular_regex`](#declaration-pumping-closure-regular-regex), [`closure_regex_correct`](#declaration-closure-regex-correct), [`pumping_normalize_correct`](#declaration-pumping-normalize-correct) | PROVEN | Total enumeration and closure_regex provide the finite witness and expression. The regularity theorem alone states existence of a recognizing automaton. Empty alphabet remains a paper-level edge case of the default-symbol representation. |
| [lem:pump-shuffle](../paper/shuffle.tex)<br>If $u\pumpsto u'$ and $\interleave{u'}{v}{w'}$, there exists $w$ such that $\interleave{u}{v}{w}$ and $w\pumpsto w'$.<br>The symmetric statement holds for a step in the right input. | [`pumping_interleaving_left`](#declaration-pumping-interleaving-left), [`pumping_interleaving_right`](#declaration-pumping-interleaving-right) | PROVEN | The removed occurrence retains an earlier source occurrence, not merely the same symbol somewhere in the word. |
| [lem:factorization](../paper/shuffle.tex)<br>If $s\pumpsto^*u$, $t\pumpsto^*v$, and $\interleave{u}{v}{w}$, then<br>\[<br>\exists z.\ \interleave{s}{t}{z}\ \land\ z\pumpsto^*w.<br>\] | [`seed_cover_interleaving_factor`](#declaration-seed-cover-interleaving-factor) | PROVEN | The output interleaving of originating seeds pumps to the full output. Original milestones are not discarded. |
| [thm:seed-criterion](../paper/shuffle.tex)<br>For every seed language $S$,<br>\[<br>\text{$S$ satisfies the seed-shuffle condition}<br>\quad\Longleftrightarrow\quad<br>\text{$\pc{S}$ is shuffle closed}.<br>\] | [`seed_shuffle_coveredP`](#declaration-seed-shuffle-coveredP), [`base_shuffle_coveredP`](#declaration-base-shuffle-coveredP) | PROVEN, scoped | seed_shuffle_coveredP covers arbitrary Prop-valued seed languages via covered_by. base_shuffle_coveredP connects Boolean seed predicates to the inductive pumping closure. Both use the inhabited finite alphabet disclosed in the paper. The empty-alphabet case is paper-level. |
| [thm:decision](../paper/shuffle.tex)<br>Applied to $F(r)$, Algorithm~\ref{alg:certify} terminates and accepts exactly when $\pc{\denote{r}}$ is shuffle closed.<br>On rejection, its result $(u,v,z)$ satisfies<br>\[<br>u,v\in\pc{\denote{r}},\qquad<br>\interleave{u}{v}{z},\qquad z\notin\pc{\denote{r}}.<br>\] | [`certify_seeds_spec`](#declaration-certify-seeds-spec), [`certify_regex_spec`](#declaration-certify-regex-spec), [`regex_counterexample_complete`](#declaration-regex-counterexample-complete), [`regex_counterexample_none`](#declaration-regex-counterexample-none), [`regex_counterexample_sound`](#declaration-regex-counterexample-sound) | PROVEN | certify_regex is Boolean. Regex_counterexample is its separate total diagnostic function. regex_counterexample_none equates witness absence with success. Regex_counterexample_complete proves a witness exists on rejection. |
| [lem:prefix-shuffle](../paper/typestate.tex)<br>If $K$ is shuffle closed, then $\pref{K}$ is shuffle closed. | [`prefix_shuffle_closed`](#declaration-prefix-shuffle-closed), [`tagged_shuffle_closed`](#declaration-tagged-shuffle-closed) | PROVEN | Finite composition requires a nonempty set of component histories, so no premise K [] is needed. |
| [lem:local](../paper/typestate.tex)<br>Let $s$ be an ordinarily well-typed, initialized program satisfying $\vdash_{\mathrm{prog}}s$.<br>At each execution prefix of $s$ with the protocol checks erased, one of its static environments corresponds to the execution and satisfies:<br>\begin{enumerate}<br>\item If $x$ is live in epoch $e$, $\rho(x)=\lambda(e)$ and $\Gamma(x)=(\kappa(\lambda(e)),R)$ with $\denote{R}=t_e^{-1}K_{\kappa(\lambda(e))}\neq\emptyset$.<br>\item Every retired epoch $e$ has $t_e\in K_{\kappa(\lambda(e))}$.<br>\end{enumerate} | [`preservation`](#declaration-preservation), [`trace_preservation`](#declaration-trace-preservation), [`residual_snoc`](#declaration-residual-snoc), [`residual_nullable`](#declaration-residual-nullable) | PROVEN for the core invariant | The core invariant stores class agreement, heap typing for defined fields, viable live histories, and completed retired histories. Initialization safety is a separate assumption. Matching the paper regex environments, environment sets, and bulk exit requires the unmechanized refinement below. |
| [lem:object-shuffle](../paper/typestate.tex)<br>With the protocol checks erased, at every runtime prefix and allocated location $\ell$, its history $h(\ell)$ is an interleaving of the histories of all epochs $e$ such that $\lambda(e)=\ell$, including retired epochs. | [`project_partition`](#declaration-project-partition), [`tagged_shuffle_closed`](#declaration-tagged-shuffle-closed), [`invariant_object_language`](#declaration-invariant-object-language) | PROVEN for fresh histories | object_history is the erasure of the relevant tagged events. Every allocated location has an epoch, including after bindings disappear. There is no separate n-ary shuffle relation. The projection theorem supplies the exact composition fact. |
| [thm:typestate](../paper/typestate.tex)<br>Let every class protocol $K_C$ be regular and shuffle closed.<br>If an ordinarily well-typed, initialized, closed source program $s$ satisfies $\vdash_{\mathrm{prog}}s$, then, with the runtime protocol checks erased:<br>\begin{enumerate}<br>\item At every execution prefix and allocated location $\ell$, $h(\ell)\in\pref{K_{\kappa(\ell)}}$.<br>\item On normal termination, every allocated object has a complete history: $h(\ell)\in K_{\kappa(\ell)}$, including objects no longer reachable from variables or fields.<br>\end{enumerate}<br>Restoring the checks preserves exactly the completed executions, and no monitored execution reaches $\mathsf{error}$.<br>Executions include the automatically inserted exit operation.<br>The static checker maintains no alias relation. | [`typestate_prefix_sound`](#declaration-typestate-prefix-sound), [`typestate_completion_sound`](#declaration-typestate-completion-sound), [`baseline_runtime_no_error`](#declaration-baseline-runtime-no-error), [`baseline_runtime_equivalence`](#declaration-baseline-runtime-equivalence) | WEAKER as a source-language theorem | The complete conclusion is proven for the semantic core under certified P and acceptance by the core checker. Nonemptiness is checked when a binding starts, rather than assumed for every class. Bulk finish, automatic exit insertion, and correspondence with regex-valued environment sets remain unmechanized. The core theorems do not establish initialization safety. |
| [prop:necessary](../paper/typestate.tex)<br>If arbitrary pairs of complete local histories from $K$ must combine into a complete object history under every interleaving, then $K$ must be shuffle closed. | [`completion_sound_requires_certified`](#declaration-completion-sound-requires-certified), [`completion_sound_iff_certified`](#declaration-completion-sound-iff-certified) | PROVEN for the baseline core | The formal converse turns raw completion soundness for every accepted baseline core program and execution into certified P. Its proof builds the two-binding client for arbitrary complete histories and a chosen interleaving. No converse for other analyses or the optional copying mode is asserted. |
| [cor:certified-typestate](../paper/typestate.tex)<br>If Algorithms~\ref{alg:construct} and~\ref{alg:certify} construct and certify every class protocol, an ordinarily well-typed, initialized, closed source program accepted by Algorithm~\ref{alg:client} has the guarantees of Theorem~\ref{thm:typestate}. | [`regular_family_certified`](#declaration-regular-family-certified), [`regular_program_prefix_sound`](#declaration-regular-program-prefix-sound), [`regular_program_completion_sound`](#declaration-regular-program-completion-sound) | WEAKER as a source-language corollary | The compiled regular-seed family is certified and composed with the core checker in regular_soundness.v over a finite inhabited alphabet. Certification supplies shuffle closedness, not nonemptiness, which remains a binding check. The paper-level Algorithm 3 and its automatic bulk finish have no mechanized implementation correspondence. |
| [thm:copying-soundness](../paper/typestate.tex)<br>Assume every class protocol is regular and shuffle closed, and every opted-in class satisfies Equation~\eqref{eq:residual-shuffle}.<br>An ordinarily well-typed, initialized, closed source program satisfying the program judgment with the optional assignment rule has all guarantees of Theorem~\ref{thm:typestate}, including safety with protocol checks erased and absence of runtime protocol errors. | [`copying_program_prefix_sound`](#declaration-copying-program-prefix-sound), [`copying_program_completion_sound`](#declaration-copying-program-completion-sound), [`copying_regular_program_prefix_sound`](#declaration-copying-regular-program-prefix-sound), [`copying_regular_program_completion_sound`](#declaration-copying-regular-program-completion-sound), [`copying_runtime_no_error`](#declaration-copying-runtime-no-error), [`copying_runtime_equivalence`](#declaration-copying-runtime-equivalence) | WEAKER as a source-language theorem | The core result is complete under copying_certified, including nested and mixed copying. Classes using fresh histories require semantic shuffle closedness, while opted-in classes additionally require residual shuffle closedness. It inherits the same paper-to-core correspondence and initialization boundary as thm:typestate. |
| [thm:accumulation-prefix](../paper/typestate.tex)<br>Suppose $P=\pref{K}$ is decidable.<br>Equation~\eqref{eq:accumulation-error} holds if and only if every derivative $p^{-1}P$ is shuffle closed. | [`kellogg_error_closed_iff_residual_prefix_shuffle_closed`](#declaration-kellogg-error-closed-iff-residual-prefix-shuffle-closed) | PROVEN | K is arbitrary Prop-valued language over any Type. Decidability of prefix_language K is an explicit hypothesis. No classical axiom supplies it. |
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

## Interfaces and supporting results from the artifact guide

These results support the headline chain or clarify examples and implementation
choices. They are not substitutes for the whole-object soundness theorems.

| Interface or claim | Declarations | What the proof establishes |
| --- | --- | --- |
| Exact coverage and the simulated frontier | [`covers_spec`](#declaration-covers-spec), [`covers_simulation_correct`](#declaration-covers-simulation-correct), [`simulation_state_bound`](#declaration-simulation-state-bound) | The direct predicate means singleton pumping reachability. The simulator returns the same result. Each frontier has at most length(seed)+1 states. No machine-time bound is proved. |
| Finite enumeration and diagnostic completeness | [`shuffles_spec`](#declaration-shuffles-spec), [`counterexample_sound`](#declaration-counterexample-sound), [`counterexample_none`](#declaration-counterexample-none), [`regex_counterexample_complete`](#declaration-regex-counterexample-complete), [`regex_counterexample_none`](#declaration-regex-counterexample-none) | Every interleaving is enumerated. Returned triples have accepted inputs and a rejected output. Witness absence agrees with successful certification. |
| Compiled protocol queries | [`closure_regex_correct`](#declaration-closure-regex-correct), [`dfa_viable_spec`](#declaration-dfa-viable-spec), [`regular_family_language`](#declaration-regular-family-language), [`regular_family_certified`](#declaration-regular-family-certified) | Membership agrees with the compiled pumping closure. Viability means existence of a completing suffix. Successful certificates yield protocol-family shuffle closure. |
| Exact baseline protocol condition | [`completion_sound_requires_certified`](#declaration-completion-sound-requires-certified), [`completion_sound_iff_certified`](#declaration-completion-sound-iff-certified) | For the existing baseline checker, all-object completion soundness is equivalent to certified P. This quantifies over all accepted core programs and their executions, rather than assuming the desired composition property as a premise. |
| Exact executable/declarative core checking | [`check_step_sound`](#declaration-check-step-sound), [`check_step_complete`](#declaration-check-step-complete), [`check_trace_spec`](#declaration-check-trace-spec) | Both directions connect the executable baseline checker to the core declarative relation. This is not a formal translation theorem for Algorithm alg:client. |
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
| Residual certification is essential for the exhibited copying client | [`separating_copy_accepted_without_certificate`](#declaration-separating-copy-accepted-without-certificate), [`separating_copy_terminates`](#declaration-separating-copy-terminates), [`separating_copy_actual_history`](#declaration-separating-copy-actual-history), [`separating_copy_actual_history_not_viable`](#declaration-separating-copy-actual-history-not-viable), [`separating_copy_unsound_without_residual_certificate`](#declaration-separating-copy-unsound-without-residual-certificate) | The concrete client allocates x, calls x.a, copies y := x, calls x.c and y.b, and retires both. Bypassing the required residual certificate makes the local copying checker accept, but the raw object history acb is nonviable. The residual certificate rejects this protocol. This is not a counterexample to the soundness theorem. |
| Baseline/copying and accumulation separation | [`separating_original_certificate`](#declaration-separating-original-certificate), [`separating_residual_not_closed`](#declaration-separating-residual-not-closed), [`separating_acb_not_viable`](#declaration-separating-acb-not-viable), [`separating_certified_not_kellogg`](#declaration-separating-certified-not-kellogg) | For the stated six-seed protocol, baseline certification succeeds, the residual at a is not shuffle closed, and the extracted error law fails. This is a language-level separation, not a comparison of implementations. |
| Strict hierarchy of regular protocol classes (end of §6) | [`accumulation_contract_residual_shuffle_closed`](#declaration-accumulation-contract-residual-shuffle-closed), [`gap_unary_residual_shuffle_closed`](#declaration-gap-unary-residual-shuffle-closed), [`gap_unary_not_completion_stable`](#declaration-gap-unary-not-completion-stable), [`separating_original_certificate`](#declaration-separating-original-certificate), [`separating_residual_not_closed`](#declaration-separating-residual-not-closed) | The paper combines these proven implications and witnesses: accumulation contracts are a proper subclass of residual shuffle-closed protocols, which are a proper subclass of shuffle-closed protocols. Regularity of the unary gap language is immediate from its displayed definition, and regularity of the six-seed closure follows from construction. This hierarchy concerns languages, not inclusion of accepted client programs. |

## Definitions, rules, and representation correspondence

The following comparison checks every primitive rule and the control-flow and
program rules in `paper/typestate.tex`. A representation difference is not a
false theorem. A missing correspondence proof matters when applying a core
result to the paper's surface algorithm.

| Paper rule or definition | Rocq representation | Checked premises and remaining boundary |
| --- | --- | --- |
| Pumping `w = pq`, `w′ = paq`, with `a` occurring in `p` | `pumping`, `pump_at`, `pumping_decompose`, `pumping_insert_char_after_prefix` in [pumping.v](pumping.v) | Indexed bounds ensure the copied event precedes the insertion. The default event is never read out of bounds by a successful step. The two decomposition/insertion lemmas connect the presentations. |
| Pumping closure and originating seeds | `pumping_closure`, `seed_covers`, `covered_by`, `pumping_closure_seed_corpus` | Closure is an inductive proposition, separate from the generated regex. Factorization does not assume the desired language equality. |
| Residual `u⁻¹K`, viability, nullability | `residual`, `prefix_language`, `qualifier_language`, `protocol_family.viable_spec` | A qualifier stores a class/history pair denoting an exact residual. Boolean acceptance is the definition of `protocol`. Viability is required to have a proof of its extension contract. |
| Dynamic New | `run_new`, `allocate`, `install` in [semantics.v](semantics.v); `runtime_guard`, `monitored_step` | The raw step is unguarded; its monitored version checks empty-history viability and signals `ProtocolError` on failure. Fresh locations and epochs are successive naturals. The paper permits any fresh location; a renaming/ghost-erasure correspondence is not a separate theorem. |
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
| Dynamic/static Finish | `run_finish`, `type_finish`, `check_step (Finish x)`, `runtime_exit_check` | Raw and monitored core `Finish x` retire one existing binding without a dynamic protocol guard; the static checker checks that binding's acceptance. The monitored program boundary separately checks all allocated object histories. Retirement preserves that check. Paper bulk `finish` retires all bindings at once; the complete source-to-core implementation correspondence is unmechanized. |
| Skip | `Skip`, `paths Skip = [[]]` | The empty trace leaves the environment and machine unchanged. |
| Seq | `paths`, `path_seq`, `typed_trace`, `execution` | Sequential paths are concatenated. Checking and execution compose along them. This represents finite branching syntax. |
| If | `Branch`, `path_left`, `path_right`, `paths_spec`, `forallb` in `check_program` | Both branch paths are checked universally. Boolean conditions are abstracted as nondeterministic choices. No feasible-path precision claim is made. The paper instead propagates sets of residual environments. |
| Program and exit insertion | `check_program`, `check_program_with_copy` | Every path starts with an empty environment and must end with no live binding. Explicit retirements are part of the supplied core syntax. Automatic exit insertion and equivalence to the paper's environment-set algorithm are not mechanized. A translation may need different retirements on different paths. |
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

The hypotheses are inhabited by kernel-checked positive clients in
[examples.v](examples.v), [copying_examples.v](copying_examples.v), and
[accumulation_examples.v](accumulation_examples.v), including allocation,
branching, aliasing, fields, overwrites, and incomplete inherited progress.
`aliases_terminates` and `inherited_progress_terminates` give explicit full
executions for accepted clients. Their history lemmas compute four and three
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

## Unresolved correspondence and scope issues

These are open proof extensions or submission tasks, **not discovered false
Rocq theorems**. They should remain explicit in the artifact and manuscript.
Baseline necessity is mechanized in `necessity.v`. The optional copying
theorem states a sufficient condition. A general converse for that mode is
not a paper claim. Its concrete unsafe client shows that ordinary shuffle
closure alone cannot replace the residual certificate in general.

| Issue | Present status | What would close it |
| --- | --- | --- |
| Bulk retirement and exit instrumentation | UNMECHANIZED. Disclosed in the paper and guide | Define a source-to-core translation and prove that inserted retirements empty each path's environment, preserve histories, and simulate bulk `finish`. Distinct exit environments can have different live variables, so a fixed retirement list is not sufficient in general. |
| Representations of residuals and control-flow alternatives | UNMECHANIZED implementation correspondence | Relate regex denotations to `qualifier_language` and environment alternatives to enumerated paths. Prove that the source checker/translation preserves acceptance and executions. |
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

[soundness.v:67](soundness.v#L67)

```coq
Theorem typestate_prefix_sound s m : certified P -> check_program P FT s = true ->
  program_prefix s initial_machine m ->
  forall l, l < next_loc m -> prefix_language (protocol P (classes m l)) (object_history m l).
```

<a id="declaration-typestate-completion-sound"></a>

### `typestate_completion_sound`

[soundness.v:78](soundness.v#L78)

```coq
Theorem typestate_completion_sound s m : certified P -> check_program P FT s = true ->
  program_execution s initial_machine m ->
  forall l, l < next_loc m -> protocol P (classes m l) (object_history m l).
```

<a id="declaration-completion-sound-requires-certified"></a>

### `completion_sound_requires_certified`

[necessity.v:111](necessity.v#L111)

```coq
Theorem completion_sound_requires_certified :
  (forall s m, check_program P FT s = true ->
    program_execution s initial_machine m ->
    forall l, l < next_loc m ->
      protocol P (classes m l) (object_history m l)) ->
  certified P.
```

<a id="declaration-completion-sound-iff-certified"></a>

### `completion_sound_iff_certified`

[necessity.v:145](necessity.v#L145)

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

[typestate.v:59](typestate.v#L59)

```coq
Lemma check_step_sound i g g' : check_step i g = Some g' -> type_step g i g'.
```

<a id="declaration-check-step-complete"></a>

### `check_step_complete`

[typestate.v:78](typestate.v#L78)

```coq
Lemma check_step_complete g i g' : type_step g i g' -> check_step i g = Some g'.
```

<a id="declaration-check-trace-spec"></a>

### `check_trace_spec`

[typestate.v:100](typestate.v#L100)

```coq
Lemma check_trace_spec is g g' : check_trace is g = Some g' <-> typed_trace g is g'.
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

[copying_typestate.v:39](copying_typestate.v#L39)

```coq
Lemma copy_step_spec g x y g' :
  check_step_with_copy (Copy x y) g = Some g' <->
  exists c w, get g y = Some (c,w) /\ retirable P g x = true /\
    (if copy_history c then g' = put g x (Some (c,w))
     else viable P c [] = true /\ g' = put g x (Some (c,[]))).
```

<a id="declaration-copying-program-prefix-sound"></a>

### `copying_program_prefix_sound`

[copying_soundness.v:345](copying_soundness.v#L345)

```coq
Theorem copying_program_prefix_sound s m :
  check_program_with_copy P FT copy_history s = true -> program_prefix s initial_machine m ->
  forall l, l < next_loc m -> prefix_language (protocol P (classes m l)) (object_history m l).
```

<a id="declaration-copying-program-completion-sound"></a>

### `copying_program_completion_sound`

[copying_soundness.v:356](copying_soundness.v#L356)

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

[invariants.v:190](invariants.v#L190)

```coq
Lemma preservation m g i m' g' : invariant m g ->
  raw_step i m m' -> type_step P FT g i g' -> invariant m' g'.
```

<a id="declaration-trace-preservation"></a>

### `trace_preservation`

[invariants.v:215](invariants.v#L215)

```coq
Lemma trace_preservation m g is m' g' : invariant m g ->
  execution is m m' -> typed_trace P FT g is g' -> invariant m' g'.
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

[copying_typestate.v:87](copying_typestate.v#L87)

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

[copying_soundness.v:274](copying_soundness.v#L274)

```coq
Theorem copying_preservation m g V i m' g' : copying_invariant m g V ->
  raw_step i m m' -> check_step_with_copy P FT copy_history i g = Some g' ->
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

[examples.v:54](examples.v#L54)

```coq
Example aliases_accepted : check_program two_calls fields aliases = true.
```

<a id="declaration-aliases-terminates"></a>

### `aliases_terminates`

[examples.v:108](examples.v#L108)

```coq
Example aliases_terminates : program_execution aliases initial_machine aliases_final.
```

<a id="declaration-aliases-object-history"></a>

### `aliases_object_history`

[examples.v:113](examples.v#L113)

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

[copying_examples.v:50](copying_examples.v#L50)

```coq
Example inherited_progress_terminates :
  program_execution inherited_progress initial_machine inherited_progress_final.
```

<a id="declaration-inherited-progress-object-history"></a>

### `inherited_progress_object_history`

[copying_examples.v:56](copying_examples.v#L56)

```coq
Example inherited_progress_object_history :
  next_loc inherited_progress_final = 1 /\
  object_history inherited_progress_final 0 = [true; true; true].
```

<a id="declaration-abandoned-object-accepted"></a>

### `abandoned_object_accepted`

[examples.v:130](examples.v#L130)

```coq
Example abandoned_object_accepted :
  check_program two_calls fields abandoned_object = true.
```

<a id="declaration-abandoned-object-terminates"></a>

### `abandoned_object_terminates`

[examples.v:133](examples.v#L133)

```coq
Example abandoned_object_terminates :
  program_execution abandoned_object initial_machine abandoned_object_final.
```

<a id="declaration-abandoned-object-unreachable"></a>

### `abandoned_object_unreachable`

[examples.v:139](examples.v#L139)

```coq
Example abandoned_object_unreachable :
  next_loc abandoned_object_final = 2 /\
  object_history abandoned_object_final 0 = [true; true] /\
  (forall x, reference abandoned_object_final x = None) /\
  (forall l f, heap abandoned_object_final l f = None).
```

<a id="declaration-abandoned-object-complete"></a>

### `abandoned_object_complete`

[examples.v:149](examples.v#L149)

```coq
Example abandoned_object_complete :
  protocol two_calls (classes abandoned_object_final 0)
    (object_history abandoned_object_final 0).
```

<a id="declaration-raw-invalid-call-executes"></a>

### `raw_invalid_call_executes`

[examples.v:162](examples.v#L162)

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

[kellogg_separation.v:129](kellogg_separation.v#L129)

```coq
Example separating_copy_accepted_without_certificate :
  check_program_with_copy separating_family separating_fields (fun _ => true)
    separating_copy_program = true.
```

<a id="declaration-separating-copy-terminates"></a>

### `separating_copy_terminates`

[kellogg_separation.v:166](kellogg_separation.v#L166)

```coq
Example separating_copy_terminates :
  program_execution separating_copy_program initial_machine separating_copy_final.
```

<a id="declaration-separating-copy-actual-history"></a>

### `separating_copy_actual_history`

[kellogg_separation.v:175](kellogg_separation.v#L175)

```coq
Example separating_copy_actual_history :
  next_loc separating_copy_final = 1 /\ classes separating_copy_final 0 = 0 /\
  object_history separating_copy_final 0 = [::a;c;b].
```

<a id="declaration-separating-copy-actual-history-not-viable"></a>

### `separating_copy_actual_history_not_viable`

[kellogg_separation.v:180](kellogg_separation.v#L180)

```coq
Example separating_copy_actual_history_not_viable :
  ~ prefix_language (protocol separating_family (classes separating_copy_final 0))
    (object_history separating_copy_final 0).
```

<a id="declaration-separating-copy-unsound-without-residual-certificate"></a>

### `separating_copy_unsound_without_residual_certificate`

[kellogg_separation.v:188](kellogg_separation.v#L188)

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

[runtime_monitor.v:35](runtime_monitor.v#L35)

```coq
Lemma runtime_call_guard x a m m' l :
  raw_step (Call x a) m m' -> reference m x = Some l ->
  runtime_guard (Call x a) m m' =
    viable P (classes m l) (object_history m l ++ [a]).
```

<a id="declaration-runtime-exit-check-spec"></a>

### `runtime_exit_check_spec`

[runtime_monitor.v:55](runtime_monitor.v#L55)

```coq
Lemma runtime_exit_check_spec m : runtime_exit_check m = true <->
  forall l, l < next_loc m -> protocol P (classes m l) (object_history m l).
```

<a id="declaration-runtime-exit-check-retire"></a>

### `runtime_exit_check_retire`

[runtime_monitor.v:52](runtime_monitor.v#L52)

```coq
Lemma runtime_exit_check_retire m x : runtime_exit_check (retire m x) = runtime_exit_check m.
```

<a id="declaration-raw-contract-monitor-no-error"></a>

### `raw_contract_monitor_no_error`

[runtime_monitor.v:169](runtime_monitor.v#L169)

```coq
Theorem raw_contract_monitor_no_error s : raw_protocol_contract s ->
  ~ monitored_program s initial_machine ProtocolError.
```

<a id="declaration-raw-contract-monitor-equivalence"></a>

### `raw_contract_monitor_equivalence`

[runtime_monitor.v:185](runtime_monitor.v#L185)

```coq
Theorem raw_contract_monitor_equivalence s : raw_protocol_contract s -> forall m,
  monitored_program s initial_machine (RuntimeState m) <->
  program_execution s initial_machine m.
```

<a id="declaration-baseline-runtime-no-error"></a>

### `baseline_runtime_no_error`

[runtime_monitor.v:205](runtime_monitor.v#L205)

```coq
Theorem baseline_runtime_no_error FT s : certified P ->
  check_program P FT s = true -> ~ monitored_program s initial_machine ProtocolError.
```

<a id="declaration-baseline-runtime-equivalence"></a>

### `baseline_runtime_equivalence`

[runtime_monitor.v:209](runtime_monitor.v#L209)

```coq
Theorem baseline_runtime_equivalence FT s : certified P -> check_program P FT s = true ->
  forall m, monitored_program s initial_machine (RuntimeState m) <->
    program_execution s initial_machine m.
```

<a id="declaration-copying-runtime-no-error"></a>

### `copying_runtime_no_error`

[runtime_monitor.v:222](runtime_monitor.v#L222)

```coq
Theorem copying_runtime_no_error FT mode s : copying_certified P mode ->
  check_program_with_copy P FT mode s = true ->
  ~ monitored_program s initial_machine ProtocolError.
```

<a id="declaration-copying-runtime-equivalence"></a>

### `copying_runtime_equivalence`

[runtime_monitor.v:227](runtime_monitor.v#L227)

```coq
Theorem copying_runtime_equivalence FT mode s : copying_certified P mode ->
  check_program_with_copy P FT mode s = true -> forall m,
  monitored_program s initial_machine (RuntimeState m) <->
    program_execution s initial_machine m.
```
