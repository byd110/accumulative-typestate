# Minimal Corpus Closedness Notes

Date: 2026-07-10

This note records the current state of the attempted theorem:

```text
canonical_shuffle_stable (minimal_seed_corpus L) ->
shuffle_closed (pumping_closure L)
```

## What Was Added

The Rocq development now has basic algebra for the coverage preorder:

```text
seed_covers_trans
cover_le_refl
cover_le_trans
seed_covers_size_ge
seed_covers_same_size
```

These are needed for reasoning about minimal representatives under `cover_le`.

## Remaining Compatibility Lemma

The theorem still needs a lemma connecting pumped descendants back to seed-level
interleavings:

```text
minimal_seed_corpus L s1 ->
minimal_seed_corpus L s2 ->
seed_covers s1 u ->
seed_covers s2 v ->
interleaving u v w ->
exists sw,
  interleaving s1 s2 sw /\
  canonical_seed sw = canonical_seed w
```

Once this is available, `canonical_shuffle_stable` gives:

```text
minimal_seed_corpus L (canonical_seed sw)
```

and the equality gives:

```text
minimal_seed_corpus L (canonical_seed w)
```

Then `canonical_seed_covers w` and membership of the canonical seed in `L`
finish the closedness proof.

## Another Needed Ingredient

To apply the compatibility lemma to arbitrary words in `pumping_closure L`, we
also need to show that every base seed in `L` is covered by some minimal seed:

```text
L s ->
exists m,
  minimal_seed_corpus L m /\ seed_covers m s
```

Mathematically this follows by descending along strict coverage, because strict
coverage decreases word length. Constructively, the proof needs either:

1. a decidable search over smaller seeds in `L`, or
2. a classical minimal-element argument.

The current development avoids importing classical axioms, so this remains an
explicit proof obligation.

## Current Status

The theorem appears semantically plausible and bounded search found no small
counterexample. It is not yet proven in Rocq because the two constructive
ingredients above are still missing.
