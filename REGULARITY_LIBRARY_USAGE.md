# MathComp and RegLang Usage Notes

Date: 2026-06-16

This note summarizes library idioms that came up while proving regularity of
the pumping closure in `pumping.v`, especially inside
`Section PumpingClosureRegularity`.

## RegLang Basics

RegLang represents words and languages as:

```coq
Definition word := seq char.
Definition lang := word -> Prop.
Definition dlang := pred word.
```

In our section we usually introduced local notations:

```coq
Notation word := (RegLang.languages.word char).
Notation lang := (RegLang.languages.lang char).
Notation dlang := (RegLang.languages.dlang char).
Notation regexp := (RegLang.regexp.regexp char).
```

The distinction matters:

- `lang` is propositional: `word -> Prop`.
- `dlang` is boolean/decidable: `pred word`.
- Regex membership `w \in r` is boolean because `regexp` has a canonical
  `PredType` instance via `re_lang`.

For pumping closure, the base language was a `dlang`, while regularity from
`RegLang.dfa` expects a `lang`. We often bridged this by writing:

```coq
fun w : word => is_true (w \in r)
```

or by defining:

```coq
Definition regex_lang (r : regexp) : dlang :=
  [pred w | w \in r].
```

## RegLang Regex Destructors

The most useful RegLang views were:

```coq
plusP : reflect (w \in r \/ w \in s) (w \in plus r s)

concP :
  reflect
    (exists w1 w2,
       w = w1 ++ w2 /\ w1 \in l1 /\ w2 \in l2)
    (w \in conc l1 l2)

starP :
  reflect
    (exists vv,
       all (fun v => (v != [::]) && (v \in l)) vv /\
       w = flatten vv)
    (w \in star l)
```

In proof scripts, these appear as:

```coq
case/plusP=> [Hw | Hw].
case/concP=> u [v [-> [Hu Hv]]].
case/starP=> vv Hall ->.
```

This style is the workhorse for regex induction cases:

- `Plus` becomes two branches.
- `Conc` produces a concrete split `u ++ v`.
- `Star` produces a list of factors `vv`, then the word is `flatten vv`.

## Regexes as Predicates

Because RegLang installs:

```coq
Canonical Structure regexp_predType (char: eqType) := PredType (@re_lang char).
```

we can write:

```coq
w \in r
```

directly for regex membership. This is why lemmas like the following are
pleasant to state:

```coq
Lemma regexp_power_in_star (r : regexp) n (w : word) :
  w \in regexp_power n r -> w \in Star r.
```

Internally, `rewrite unfold_in /atom`, `rewrite unfold_in /eps`, or
`rewrite /regex_lang inE` often exposes the underlying boolean predicate.

## Regularity API

RegLang defines DFA regularity as a sigma type:

```coq
Definition regular (L : lang char) :=
  { A : dfa | forall x, L x <-> x \in dfa_lang A }.
```

The key API points we used were:

```coq
RegLang.regexp.regularP
RegLang.dfa.regular_ext
RegLang.dfa.regular_bigU
```

### Turning a Regex into a Regular Language

The regular-expression theorem is exposed through a reflection-like statement:

```coq
Lemma regularP (char : finType) (L : lang char) :
  reflect (exists e : regexp char, L =i e) (regular L).
```

In our file we packaged it as:

```coq
Lemma regexp_language_regular (r : regexp) :
  RegLang.dfa.regular (fun w : word => is_true (w \in r)).
Proof.
  case: (@regularP char (fun w : word => is_true (w \in r)))
    => _ Hregular.
  apply: Hregular.
  by exists r.
Qed.
```

This pattern is slightly surprising the first time: the `case:` splits the
`reflect`, and the second constructor direction gives a way to prove regularity
from an existential regex witness.

### Changing the Language by Extensionality

We repeatedly used:

```coq
RegLang.dfa.regular_ext :
  regular L2 -> L1 =p L2 -> regular L1
```

The second argument is pointwise equivalence. In practice:

```coq
apply: (RegLang.dfa.regular_ext
  (L2 := fun out : word => is_true (out \in pumping_singleton_re w))).
- exact: regexp_language_regular.
- move=> out. exact: pumping_closure_singleton_correct.
```

This lets the proof use a regex language as the regular witness, then transfer
regularity to an equivalent semantic or closure language.

### Finite Union of Regular Languages

For normalized languages, the main closure property was:

```coq
RegLang.dfa.regular_bigU :
  (forall a, a \in s -> regular (L a)) ->
  regular (fun x => exists2 a, a \in s & L a x).
```

The proof pattern was:

```coq
apply: RegLang.dfa.regular_bigU => w _.
exact: pumping_closure_singleton_regular.
```

This was ideal once normalized regexes were represented as finite unions of
concrete strings.

## Big Operators for Regex Union

RegLang makes `Plus` and `Void` into a canonical big operator:

```coq
\big[@Plus char / @Void char]_(...)
```

We used this in several places:

```coq
Definition re_of_set (X : {set char}) : regexp :=
  \big[@Plus char / @Void char]_(c in X)
    (Atom c).

Definition union_strings (ws : seq word) : regexp :=
  \big[@Plus char / @Void char]_(w <- ws)
    (String w).

Definition bounded_star_basis (r : regexp) : regexp :=
  \big[@Plus char / @Void char]_(k : 'I_(#|char|).+1)
    (regexp_power k r).
```

Two RegLang views unpack these unions:

```coq
big_plusP :
  reflect (exists2 i, P i & w \in F i)
          (w \in \big[Plus/Void]_(i | P i) F i)

big_plus_seqP :
  reflect (exists2 x, x \in r & w \in F x)
          (w \in \big[Plus/Void]_(i <- r) F i)
```

The resulting proof shape is:

```coq
apply: (iffP (big_plusP _ _ _)) => [[c Hc Hw] | [c Hc ->]].
```

or:

```coq
apply: (iffP (big_plus_seqP _ _ _)) => [[u Hu] | [u Hu ->]].
```

## Finite Alphabets and Ordinals

The regularity proof relies on `char : finType`, not merely `eqType`, because
we need finite sets and a finite bound:

```coq
#|char|
```

The bounded star basis quantifies over:

```coq
k : 'I_(#|char|).+1
```

An element of `'I_n` is a natural number bundled with a proof that it is less
than `n`. Therefore `k : 'I_(#|char|).+1` ranges over:

```text
0, 1, ..., #|char|
```

To build such an index explicitly, we used:

```coq
exists (Ordinal Hsize).
```

where:

```coq
Hsize : size bs < (#|char|).+1
```

This is the standard MathComp way of turning a bounded natural number into a
finite ordinal.

## Finite Sets

MathComp finite sets showed up in the singleton pumping invariant:

```coq
{set char}
set0
[set a]
X :|: [set a]
word_symbols u \subset word_symbols v
```

Useful rewrite lemmas included:

```coq
set0U
setU0
setUA
inE
```

For subset assumptions:

```coq
word_symbols u \subset word_symbols v
```

we converted membership with:

```coq
subsetP Hsub
```

Example:

```coq
by rewrite -mem_word_symbols (subsetP Hsub) ?mem_word_symbols.
```

For proving a strict increase in the finite-basis argument, we used:

```coq
properUl
proper_card
max_card
```

The conceptual move was:

```coq
word_symbols p \proper word_symbols p :|: word_symbols v
```

so the cardinality of the symbol context strictly increases whenever a factor
introduces a genuinely new symbol.

## Boolean Reflection Patterns

The whole proof is written in the MathComp/Ssreflect style, so boolean
predicates and propositions are constantly bridged by views.

Common examples:

```coq
move/andP=> [H1 H2].
case/orP=> [H | H].
move/eqP=> ->.
apply/idP/idP.
apply/allP=> c Hc.
move/allP=> Hall.
```

For example:

```coq
Lemma all_take P (w : word) n :
  all P w -> all P (take n w).
Proof.
  move/allP=> Hall.
  apply/allP=> c Hc.
  exact: Hall c (mem_take Hc).
Qed.
```

This is a typical conversion between:

- boolean sequence predicate: `all P w`
- pointwise proposition over members: `forall c, c \in w -> P c`

## `exists2` and Flattened Conjunctions

MathComp often uses compact dependent existential syntax:

```coq
exists2 w, w \in ws & pumping_closure ... w ...
```

which means:

```coq
exists w, w \in ws /\ pumping_closure ... w ...
```

For conjunctions with more than two pieces, Ssreflect uses flattened syntax:

```coq
[/\ A, B & C]
```

This avoids right-nested goals like:

```coq
A /\ (B /\ C)
```

and gives cleaner destructuring:

```coq
case=> x [y [Hx Hy ->]].
case: H => [A B C].
```

For two components, both native Coq and Ssreflect styles are possible:

```coq
A /\ B
[/\ A & B]
```

The flattened style becomes more valuable once there are three or more
components.

## Sequence and Word Manipulation

Since words are sequences, much of the proof is sequence algebra:

```coq
take
drop
nth
size
cat
flatten
mem_cat
mem_take
mem_drop
mem_nth
cat_take_drop
take_size_cat
drop_size_cat
nth_cat
```

Examples of useful proof moves:

```coq
rewrite size_cat.
rewrite cat_take_drop.
rewrite take_size_cat // drop_size_cat //.
rewrite nth_cat Hi.
rewrite mem_cat Hc.
```

The singleton pumping proof also used custom sequence lemmas to keep this
manageable:

```coq
insert_after_cat_prefix
pump_at_cat_prefix
pump_at_cat_suffix
pumping_cat_prefix
pumping_cat_suffix
```

## Membership in Constructed Regexes

Two custom reflection lemmas were especially useful:

```coq
Lemma re_of_setP (X : {set char}) (w : word) :
  reflect (exists2 c, c \in X & w = [:: c]) (w \in re_of_set X).

Lemma union_stringsP ws w :
  reflect (exists2 u, u \in ws & w = u) (w \in union_strings ws).
```

These turn membership in generated regex unions into ordinary data:

- a character from a finite set;
- or a word from a finite list.

This is the bridge between the syntactic regex representation and the proof’s
semantic/operational argument.

## The `String` Regex

RegLang provides a regex constructor/function:

```coq
String w
```

for the singleton language containing exactly `w`. The key fact used was:

```coq
StringE
```

which lets membership reduce to equality:

```coq
rewrite StringE inE => /eqP ->.
```

This made `union_strings` the natural codomain for star-free normalization:

```coq
Definition union_strings (ws : seq word) : regexp :=
  \big[@Plus char / @Void char]_(w <- ws)
    (String w).
```

## Main Proof Pattern Worth Reusing

The final theorem follows a reusable pattern:

1. Build an explicit regex for the language you want.
2. Prove semantic equivalence pointwise.
3. Use `regexp_language_regular` to get regularity of the regex language.
4. Use `RegLang.dfa.regular_ext` to transfer regularity.
5. Use `regular_bigU` when the language is a finite union indexed by a list.

The final packaging was:

```coq
Theorem pumping_closure_regular_regex r :
  RegLang.dfa.regular
    (fun out : word =>
      @pumping_closure char d0 (regex_lang r) out).
```

Its proof is short because the heavy lifting has been staged into:

```coq
pumping_closure_singleton_correct
pumping_closure_union_strings_regular
pumping_closure_normalized_regular
pumping_normalize_correct
```

## Small Gotchas

- `regular_ext` wants pointwise equivalence of `lang`s, so the goal is often
  propositional even if the regex side is boolean. Returning an `<->` lemma is
  usually enough.
- `w \in r` works for regexes only because RegLang made regexes a `PredType`.
- Big regex unions over finite sets need `char : finType`; unions over lists
  only need the list index type to be an `eqType`.
- `case: (@regularP ...) => _ Hregular` is not obvious at first glance, but it
  is just extracting the useful direction of a `reflect`.
- When using `'I_n`, remember that the visible value is a natural number, but
  the term also carries a bound proof.
