# Canonical Corpus Closedness Counterexample

Date: 2026-07-09

The proposed theorem

```text
canonical_shuffle_stable (canonical_corpus L) ->
shuffle_closed (pumping_closure L)
```

is false as stated.

## Counterexample

Take alphabet `{a,b}` and base language:

```text
L = { ab, bba }
```

The canonical first-occurrence corpus is:

```text
canonical_corpus L = { ab, ba }
```

This corpus is stable under shuffling at the canonical level. Shuffling `ab` and
`ba` can only produce words whose first-occurrence canonical seed is either `ab`
or `ba`, both of which are in the corpus.

However, the pumping closure is not shuffle closed. Bounded search found:

```text
u = bbba      in pumping_closure L
v = aabb      in pumping_closure L
w = baabbbba  in u shuffle v
```

but:

```text
w notin pumping_closure L
```

Intuitively, the canonical corpus forgot a repeated milestone obligation from
the seed `bba`: words generated from `bba` must expose two distinguished `b`s
before the distinguished `a`. The shuffled word above has canonical seed `ba`,
but it does not satisfy the milestone shape of `bba`, and it is also not generated
from `ab`.

## Lesson

The canonical corpus is useful, but it is too coarse by itself. It remembers
first-occurrence order but forgets repeated required occurrences.

To get a sound general theorem, we need one of the following stronger
conditions:

1. Use the exact seed-cover corpus:

```text
seed_corpus (shuffle_lang (covered_by S) (covered_by S)) S
```

This is already enough but may be hard to check because `covered_by S` can be
infinite.

2. Define a finite milestone corpus rather than a first-occurrence corpus.

This corpus should keep enough repeated-letter obligations to decide whether a
word is covered by a seed. It would be closer to a minimal basis under the
coverage preorder:

```text
s <= t iff covered_by {t} subset covered_by {s}
```

3. Strengthen canonical stability with a dominance condition.

For every canonical seed produced by shuffling corpus seeds, the base language
must contain a representative whose milestone obligations are weak enough to
cover all such shuffles.

The current exact `seed_corpus` theorem in `pumping.v` remains correct; the
failed theorem only shows that replacing exact seed cover with first-occurrence
canonicalization loses too much information.
