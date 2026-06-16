# Regularity Proof Construction Notes

Date: 2026-06-16

This file records a reconstructed history of the proof construction process for
the pumping-closure regularity work in `pumping.v`.

Important caveat: this is not a literal transcript of every failed Coq command.
The exact interactive proof states and error messages are not preserved here.
Instead, this summarizes the main attempts, the kind of obstacle each attempt
ran into, and the design change that resolved it.

## Final Destination

The final theorem is:

```coq
Theorem pumping_closure_regular_regex r :
  RegLang.dfa.regular
    (fun out : word =>
      @pumping_closure char d0 (regex_lang r) out).
```

The proof now works by:

1. reducing arbitrary regexes to a normalized finite union of strings;
2. proving singleton pumping closures are regular;
3. using finite union closure for the normalized language;
4. transferring regularity through pumping-closure equivalence.

## Attempt 1: Direct Denotational Semantics with a Global Collection

### Initial idea

Define a denotational semantics similar to:

```text
pumpsem a C
pumpsem (s1 | s2) C
pumpsem (s1 s2) C
pumpsem (s*) C
```

where `C` collected symbol sets from the left context.

The hope was that each regex constructor could be translated structurally into
a regex for its pumping closure.

### Problem encountered

Branching and concatenation did not interact cleanly.

Example:

```text
(a | b) a
```

A semantics that only carries one context collection through concatenation can
accidentally merge branch histories. But the two branches should be treated as:

```text
aa | ba
```

The second `a` should see different left contexts depending on whether the
first branch chose `a` or `b`.

### Fix

We stopped trying to make a single global collection semantics handle all regex
structure directly. Instead, we moved toward normalization:

```text
(a | b) a  ~~>  aa | ba
```

Then singleton words can be handled independently.

## Attempt 2: Branching Semantics Carrying Output Collections

### Initial idea

Introduce a richer semantic output that carries both:

- the generated language;
- the resulting symbol collections for later concatenation.

This was meant to solve the branch-context problem.

### Problem encountered

The semantic object became too heavy. For `Plus`, the resulting collection is a
set of possible branch contexts, and concatenation must feed each one forward.
This led toward a big-step semantics with complex bookkeeping.

The counterexamples were not that the semantics was false, but that proving
regularity through it looked much more expensive than the theorem needed.

### Fix

We abandoned the rich semantic-output design and separated the concerns:

- first normalize regex structure into a finite union of words;
- then prove singleton closure regularity once;
- then use finite union closure.

This removed branch bookkeeping from the core semantic proof.

## Attempt 3: A General Concatenation Congruence

### Initial idea

Try to prove a congruence principle:

```text
if Cl(r1) = Cl(s1) and Cl(r2) = Cl(s2),
then Cl(r1 r2) = Cl(s1 s2)
```

This would let star elimination and normalization be proven compositionally.

### Problem encountered

Pumping is word-dependent and can cross the boundary between concatenated
pieces. Closure equivalence of the two sides independently is not enough to
guarantee closure equivalence after concatenation.

This was the key conceptual failure: pumping closure is not a clean congruence
for concatenation in the naive form.

### Fix

Instead of proving full congruence, we proved a more direct base-lifting
statement:

```coq
Lemma eliminate_star_base_closure r :
  [/\ (forall w,
        w \in r ->
        @pumping_closure char d0 (regex_lang (eliminate_star r)) w)
    & (forall w,
        w \in eliminate_star r ->
        @pumping_closure char d0 (regex_lang r) w)].
```

Then:

```coq
Theorem eliminate_star_correct r :
  closure_equiv r (eliminate_star r).
```

is obtained by lifting the base-language inclusion through pumping closure:

```coq
Lemma pumping_closure_base_lift ...
```

This avoided an invalid global congruence principle.

## Attempt 4: Handling Star as a Regex-Level Equation

### Initial idea

Replace `r*` with a finite expression such as a bounded union of powers:

```text
r^0 | r^1 | ... | r^#|char|
```

The rough intuition was that once all alphabet symbols have appeared, later
factors can be replayed by pumping.

### Problem encountered

The statement cannot simply be language equivalence:

```text
L(r*) = L(Union_{k <= #|char|} r^k)
```

That is false in general. The correct statement is only equivalence after
pumping closure:

```text
Cl(r*) = Cl(Union_{k <= #|char|} r^k)
```

### Fix

Define:

```coq
Fixpoint regexp_power (n : nat) (r : regexp) : regexp := ...

Definition bounded_star_basis (r : regexp) : regexp :=
  \big[@Plus char / @Void char]_(k : 'I_(#|char|).+1)
    (regexp_power k r).
```

Then prove:

```coq
Theorem pumping_closure_star_finite_basis (r : regexp) :
  closure_equiv (Star r) (bounded_star_basis r).
```

The core compression lemma is:

```coq
Lemma star_has_bounded_pumping_basis (r : regexp) (w : word) :
  w \in Star r ->
  exists u,
    [/\ u \in bounded_star_basis r
      & @pumping_closure char d0 (pred1 u) w].
```

## Attempt 5: Proving the Star Compression Bound

### Initial idea

Given a star decomposition:

```coq
case/starP=> vv Hall ->.
```

try to select at most `#|char|` factors from `vv` and pump from those selected
factors to recover `flatten vv`.

### Problem encountered

The proof needed a precise selection algorithm, not just an existential
pigeonhole argument. Coq needed an actual finite basis word and a proof that
the rest of the factors could be replayed by pumping.

### Fix

Introduce a deterministic selection function:

```coq
Fixpoint factor_basis (p : word) (vv : seq word) : seq word :=
  if vv is v :: vs then
    if word_symbols v \subset word_symbols p then factor_basis p vs
    else v :: factor_basis (p ++ v) vs
  else [::].
```

Meaning:

- `p` is the accumulated prefix/context;
- keep factor `v` only if it introduces a new symbol;
- otherwise omit it, because all its letters already occur in `p` and can be
  recreated by pumping.

The proof then split into small facts:

```coq
Lemma factor_basis_replay ...
Lemma factor_basis_all ...
Lemma factor_basis_size ...
Lemma regexp_power_flatten ...
```

The key size argument used finite-set cardinality:

```coq
word_symbols p \proper word_symbols p :|: word_symbols v
```

so every kept factor strictly increases the set of seen symbols, and there can
be at most `#|char|` such increases.

## Attempt 6: Normalizing Star-Free Regexes by Distribution

### Initial idea

Normalize regexes by repeatedly applying algebraic distribution laws:

```text
(r1 | r2) s  ~~>  r1 s | r2 s
r (s1 | s2)  ~~>  r s1 | r s2
```

This looks close to the paper-pencil normalization.

### Problem encountered

Regex-level rewriting requires proving or managing many equivalence lemmas,
associativity choices, and repeated distribution bookkeeping. It also risks
reintroducing the concatenation congruence issue at the pumping-closure level.

### Fix

Normalize semantically into a list of concrete words:

```coq
Fixpoint words_of_star_free (r : regexp) : seq word := ...

Definition union_strings (ws : seq word) : regexp :=
  \big[@Plus char / @Void char]_(w <- ws)
    (String w).
```

Then prove:

```coq
Lemma words_of_star_free_correct r :
  star_free r ->
  forall w, (w \in r) = (w \in words_of_star_free r).
```

This turned normalization into sequence computation rather than symbolic regex
rewriting.

## Attempt 7: Singleton Regularity via Regex Directly

### Initial idea

For a concrete word:

```text
a1 a2 ... an
```

build a regex:

```text
a1 (X1)* a2 (X2)* ... an (Xn)*
```

where each `Xi` contains the letters available from the prefix.

### Problem encountered

The hard direction was:

```text
if out is in the pumping closure of singleton w,
then out is accepted by the constructed singleton regex.
```

The proof must show that one more pumping step preserves the block structure.
Naively, after inserting a symbol into `out`, it is not obvious which block it
belongs to.

### Fix

Define an operational invariant:

```coq
Inductive pump_semantic : {set char} -> word -> word -> Prop := ...
```

Then prove:

```coq
Lemma pump_semantic_insert_at X s out k c :
  pump_semantic X s out ->
  k < size out ->
  (c \in X) || (c \in take k.+1 out) ->
  pump_semantic X s (insert_after out k c).
```

This is the important invariant:

> The inserted character is either already in the incoming context `X`, or it
> appears in the prefix before the insertion point, hence it belongs to the
> block/context governing that position.

Then the pumping step closes the semantics:

```coq
Lemma pump_semantic_closed X s out out' :
  pump_semantic X s out ->
  @pumping char d0 out out' ->
  pump_semantic X s out'.
```

Finally:

```coq
Lemma pump_semanticP X s out :
  pump_semantic X s out <-> out \in pumping_singleton_re_from X s.
```

connects the invariant back to an actual regex.

## Attempt 8: Proving Singleton Semantics Implies Pumping Closure

### Initial idea

Once `pump_semantic` was defined, show every semantic output is reachable from
the original singleton word by pumping.

### Problem encountered

The semantic rule emits an arbitrary block after each symbol:

```coq
a :: block ++ out
```

but the pumping relation only inserts one character at a time after an existing
prefix position. So arbitrary blocks must be generated by repeated one-step
pumps.

### Fix

Prove block insertion lemmas:

```coq
Lemma pumping_insert_char_after_prefix ...
Lemma pumping_insert_block_after_prefix ...
```

Then generalize the semantic-to-closure proof with an explicit prefix:

```coq
Lemma pump_semantic_to_closure_from p s out :
  pump_semantic (word_symbols p) s out ->
  @pumping_closure char d0 (pred1 (p ++ s)) (p ++ out).
```

The empty-prefix version becomes:

```coq
Lemma pump_semantic_to_closure w out :
  pump_semantic set0 w out ->
  @pumping_closure char d0 (pred1 w) out.
```

This prefix generalization was the proof-strengthening step that made
induction go through.

## Attempt 9: Final Regularity for Normalized Languages

### Initial idea

After normalization:

```coq
pumping_normalize r = union_strings ws
```

prove directly that its pumping closure is regular.

### Problem encountered

The target language is not just membership in `union_strings ws`; it is the
pumping closure of that language. We needed to express it as a finite union of
singleton pumping closures.

### Fix

Prove:

```coq
Lemma pumping_closure_union_stringsP ws out :
  @pumping_closure char d0 (regex_lang (union_strings ws)) out <->
  exists2 w, w \in ws & @pumping_closure char d0 (pred1 w) out.
```

Then use:

```coq
RegLang.dfa.regular_bigU
```

with:

```coq
pumping_closure_singleton_regular
```

This converted the final regularity proof into a finite union of already-proven
regular singleton closures.

## Repeated Micro-Pattern: Strengthen the Lemma

Many failures were fixed by strengthening the statement rather than by forcing
the current goal harder.

Examples:

- Instead of proving singleton semantics only from `set0`, prove
  `pump_semanticP X s out` for arbitrary `X`.
- Instead of proving semantic-to-closure only for the original word, prove
  `pump_semantic_to_closure_from p s out` for arbitrary prefix `p`.
- Instead of proving `r*` language equivalence with a finite basis, prove
  pumping-closure equivalence.
- Instead of proving normalized regularity directly, prove the characterization
  `pumping_closure_union_stringsP`.

This was probably the main proof-engineering pattern of the session:

> when induction gets stuck, expose the missing context as a parameter.

## Repeated Micro-Pattern: Convert Boolean Membership to Data

Another recurring pattern was introducing reflection lemmas:

```coq
Lemma bounded_star_basisP ...
Lemma concat_word_listsP ...
Lemma union_stringsP ...
Lemma re_of_setP ...
```

These turn boolean membership goals into ordinary witnesses:

- which branch of a union;
- which word in a finite list;
- which character in a finite set;
- which bounded power of a regex.

Once the witness exists explicitly, the proof can proceed by ordinary
destructuring instead of rewriting opaque boolean membership.

## Repeated Micro-Pattern: Use Computation for Syntax, Proofs for Semantics

The successful architecture separates two jobs:

### Computation

Functions such as:

```coq
eliminate_star
words_of_star_free
union_strings
pumping_normalize
factor_basis
```

compute concrete syntax or finite witnesses.

### Proof

Lemmas such as:

```coq
eliminate_star_correct
words_of_star_free_correct
pumping_closure_singleton_correct
pumping_closure_union_stringsP
```

show that the computed syntax has the intended semantic meaning.

This separation made the final theorem short.

## Things That Were Deliberately Not Pursued

### A general theorem for arbitrary `lang`

We discussed a possible wrapper:

```text
if L is regular, then Cl(L) is regular
```

But since the development is regex-centered and regexes characterize regular
languages, the theorem over arbitrary regexes is the useful form here.

### A global denotational semantics for all regexes

The original denotational idea was helpful conceptually, but a direct global
semantics carried too much branch/context bookkeeping. The final proof uses a
singleton semantics only, after normalization has removed branching.

### A concatenation congruence rule

This was avoided because pumping closure does not respect concatenation in the
simple congruence form we first wanted.

## Useful Lessons for Future Proofs

- Test the desired theorem shape on small regexes like `(a | b) a` before
  investing in a global semantics.
- If branch history matters, normalize to explicit branches before proving
  per-branch facts.
- Be suspicious of congruence principles for closure operators whose steps can
  inspect or modify whole words.
- For finite-alphabet arguments, prefer an executable selector like
  `factor_basis` over a pure existence argument.
- When a regex proof becomes symbolic-rewrite heavy, consider normalizing to a
  data structure such as `seq word`.
- For MathComp proofs, write small `reflect` lemmas early. They are cheap and
  make later proof states much less cryptic.
