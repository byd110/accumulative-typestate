# Permutation-Extended Closedness Proof Notes

Date: 2026-06-16

This note records the Rocq preparation for the permutation-extended pumping
closure theorem.

## Paper Argument Reviewed

The paper proof splits the theorem into cases:

1. both shuffled words come from permutations of the same prefix;
2. they come from permutations of different prefixes;
3. both come from `perm(s) . {t}`;
4. one comes from the prefix-permutation part and the other from the suffix part.

The proof idea is to scan the shuffled output and collect enough required
occurrences to form a new seed permutation. Skipped letters are justified because
they must have already appeared earlier and can therefore be produced by pumping.

## Mechanized Definitions Added

The Rocq file now contains these static predicates:

```text
perm_word s u
permall_seed s u
perm_suffix_seed s t u
permutation_extended L s t
```

`perm_word` uses MathComp's `perm_eq`, so repeated letters are handled by
counts/multisets rather than by an explicit bijection.

The theorem family is represented extensionally:

```text
permutation_extended L s t :=
  forall u,
    L u <->
      permall_seed s u \/ perm_suffix_seed s t u
```

This avoids needing to enumerate all permutations as a boolean language.

## Mechanized Lemmas Added

The following reusable facts are now proven:

```text
interleaving_size
interleaving_count_mem
perm_word_count
permall_seed_count_le
pump_semantic_count_ge
pumping_closure_singleton_count_ge
```

These prove the multiset/count side of the paper argument:

- interleaving adds lengths;
- interleaving adds per-letter counts;
- `perm_eq` preserves per-letter counts;
- a permutation of a prefix cannot use more of any letter than the original word;
- singleton pumping closure never decreases any per-letter count.

## Remaining Constructive Lemma

The full theorem still needs a constructive seed-extraction lemma.

For the same-prefix case, the expected shape is:

```text
perm_word s seed1 ->
perm_word s seed2 ->
pumping_closure {seed1} out1 ->
pumping_closure {seed2} out2 ->
interleaving out1 out2 out ->
exists seed,
  perm_word s seed /\ pumping_closure {seed} out
```

The paper proof describes the seed construction by scanning `out`, maintaining a
multiset of still-needed letters from `s`, and collecting a letter whenever it is
still needed. This must be made explicit in Rocq.

The key missing construction is a greedy selector:

```text
select_seed needed out = (seed, residue/evidence)
```

with proofs that:

1. `seed` is a permutation of the requested multiset;
2. every skipped letter was already selected earlier;
3. therefore `out` is in the singleton pumping closure of `seed`.

This construction is also needed for different-prefix and suffix cases, with the
requested multiset changing from `s` to the larger prefix or to `s ++ t`.

## Adjustment From Paper Proof

The paper proof phrases the construction procedurally and says skipped letters
"have occurred before." In Rocq, that statement must be represented as an
invariant of the scan:

```text
all skipped letters belong to the support of the selected prefix so far
```

or, equivalently, the output seen so far is covered by the selected seed prefix.

Without that invariant, the count lemmas alone are insufficient: counts can prove
that enough letters exist somewhere in the shuffle, but they do not prove that
the chosen seed appears early enough to generate the skipped letters by pumping.

## Suggested Next Step

Define and prove the greedy selector for a finite multiset represented by a word
`need`:

```text
select_seed need out
```

The selector should scan `out`, take a character when `need` still contains a
remaining occurrence of that character, and skip it otherwise. Once this selector
is proven correct, the same-prefix permutation case should become the first
closedness theorem to finish.
