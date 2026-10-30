# Rocq-to-Lean migration ledger

The source of truth is the current `pumping.v`. A declaration scan of this
checkout finds 149 named `Definition`, `Fixpoint`, `Inductive`, `Lemma`,
`Theorem`, and `Example` commands. This differs from the older 220-item count
in the planning notes: in particular, the known-false canonical-corpus result
has already been removed from this Rocq file. Every named declaration in the
current file is accounted for below.

Statuses are **ported**, **Mathlib**, **stronger**, **internal**, and **pending**.

## Basic pumping kernel

| Rocq declarations | Status / Lean replacement |
|---|---|
| `word_base`, `word` | **ported**: `Word` |
| `dlang_base`, `dlang` | **ported**: `DLanguage` |
| `lang` | **Mathlib**: `Language` |
| `only_a_dlang`, `aa_in_only_a_dlang`, `even_a_dlang` | **pending** examples |
| `pump_at` | **ported**: `pumpAt` |
| `pumping` | **ported**: `Pumps`; executable reflection is `pumpsB_iff` |
| `w_abcd`, `w_abcd_pumped`, `pumping_w_abcd_pumped` | **ported** as regression examples |
| `pumping_closure` | **ported**: `PumpingClosure` and language wrapper `pumpingClosure` |
| `pump_succs`, `pump_succs_sound`, `pump_succs_complete`, `pump_succsP` | **ported**: `pumpSuccs`, `mem_pumpSuccs_iff`, `pumpsB_iff` |
| `reachable`, `reachable_step` | **ported**: `Reachable`, `Reachable.appendStep` |
| `pumping_closure_singleton_dlang` | **ported**: `singletonClosureB` |
| `pumping_closure_to_reachable`, `reachable_closure`, `reachable_to_pumping_closure` | **ported** and consolidated in `pumpingClosure_singleton_iff`, `Reachable.toClosure`, `Reachable.liftClosure` |
| `pump_at_size`, `pumping_size`, `reachable_size` | **ported**: `length_pumpAt`, `Pumps.length_eq`, `Reachable.length_eq` |
| `pumping_closure_singleton_eq` | **ported**: `singletonClosureB_iff` |

Additional strengthened kernel results: `Pumps.fallback_irrel`,
`PumpingClosure.monotone`, `PumpingClosure.bind`, and
`pumpingClosure_idempotent`.

## Regex construction and normalization

| Rocq declarations | Status / Lean replacement |
|---|---|
| `re_of_set` | **ported**: `reOfFinset` |
| `pump_semantic` | **ported**: `PumpSemantic` |
| `pumping_singleton_re_from`, `pumping_singleton_re` | **ported**: `pumpingSingletonRegexFrom`, `pumpingSingletonRegex` |
| `regex_lang` | **internal**: use `RegularExpression.matches'` directly |
| `closure_equiv`, `closure_equiv_refl`, `closure_equiv_sym`, `closure_equiv_trans` | **pending** |
| `regexp_power` | **ported**: `regexPower` |
| `bounded_star_basis`, `bounded_star_basisP` | **ported**: `boundedStarBasis`, `mem_boundedStarBasis_iff` |
| `concat_word_lists`, `concat_word_listsP` | **ported**: `concatWordLists`, `mem_concatWordLists_iff` |
| `star_free`, `words_of_star_free` | **ported**: `starFree`, `wordsOfStarFree` |
| `union_strings`, `union_stringsP`, `union_strings_correct` | **ported**: `wordUnionRegex`, `mem_wordUnionRegex_iff` |
| `words_of_star_free_correct` | **ported**: `wordsOfStarFree_correct` |
| `normalize_star_free`, `normalize_star_free_correct` | **ported**: `normalizeStarFree`, `normalizeStarFree_correct` |
| `finite_lang`, `star_free_finite` | **subsumed** by `wordsOfStarFree_correct` and explicit enumeration |
| `eliminate_star`, `regexp_power_star_free`, `bounded_star_basis_star_free`, `eliminate_star_star_free` | **pending** |
| `pumping_normalize`, `pumping_normalize_is_union_strings` | **pending** |
| `regexp_language_regular`, `pumping_normalize_regular` | **stronger** target uses local regex witness; DFA bridge intentionally omitted |
| `pumping_closure_monotone` | **ported**: `PumpingClosure.monotone` |
| `language_equiv_closure_equiv`, `pumping_normalize_eliminate_star_equiv` | **pending** |
| `pumping_closure_lift_singleton`, `pumping_closure_lift_closure` | **ported/subsumed**: `PumpingClosure.bind`, `Reachable.liftClosure` |
| `pump_at_cat_suffix`, `pumping_cat_suffix`, `pump_at_cat_prefix`, `pumping_cat_prefix` | **pending** |
| `pumping_closure_cat_prefix`, `pumping_closure_cat`, `pumping_closure_base_lift` | **pending** |
| `pumping_closure_plusl`, `pumping_closure_plusr`, `pumping_closure_conc_regex` | **pending** |
| `regexp_power_in_star`, `bounded_star_basis_in_star` | **pending** |
| `word_symbols`, `mem_word_symbols` | **ported**: `wordSymbols`, `mem_wordSymbols` |
| `word_symbols_cat` | **ported**: `wordSymbols_append` |
| `re_of_setP`, `star_re_of_set_all`, `all_star_re_of_set` | **ported/consolidated**: `mem_reOfFinset_iff`, `mem_star_reOfFinset_iff` |
| `pump_semanticP` | **ported**: `pumpSemantic_iff_mem_regexFrom` |
| `pump_semantic_base` | **ported**: `PumpSemantic.base` |
| `insert_after` | **ported/subsumed** by `pumpAt` |
| `all_take`, `all_drop`, `all_insert_after` | **Mathlib/internal** list lemmas |
| `cat_cons_cat`, `cons_cat_snoc`, `insert_after_cat_prefix`, `mem_head_segment_allowed` | **pending/internal** |
| `pump_semantic_insert_at`, `nth_mem_take_prefix`, `pump_semantic_closed` | **pending** |
| `pumping_closure_singleton_to_semantic`, `pumping_closure_singleton_to_re` | **pending** |
| `subset_word_symbols_all` | **pending** |
| `pumping_insert_char_after_prefix`, `all_mem_catl`, `pumping_insert_block_after_prefix`, `all_word_symbols_mem` | **pending** |
| `pump_semantic_to_closure_from`, `pump_semantic_to_closure` | **pending** |
| `factor_basis`, `factor_basis_replay`, `regexp_power_flatten`, `factor_basis_all`, `factor_basis_size` | **pending** |
| `pumping_closure_bounded_star_basis_to_star`, `star_has_bounded_pumping_basis`, `pumping_closure_star_to_bounded_star_basis` | **pending** |
| `pumping_closure_star_finite_basis`, `pumping_closure_star_factors` | **pending** |
| `eliminate_star_base_closure`, `eliminate_star_correct`, `pumping_normalize_correct` | **pending** |
| `pumping_closure_singleton_correct` | **pending** headline singleton equality |
| `pumping_closure_singleton_regular` | **stronger** target is explicit `pumpingSingletonRegex_correct` |
| `pumping_closure_union_stringsP`, `pumping_closure_union_strings_regular`, `pumping_closure_normalized_regular` | **pending**, then subsumed by explicit compiler |
| `pumping_closure_regular_regex` | **stronger** target: `pumpingClosureRegex_correct` and `pumpingClosure_isRegexRegular` |

## Interleaving and seed corpora

| Rocq declarations | Status / Lean replacement |
|---|---|
| `pumping_closure_lang` | **ported**: `pumpingClosure` |
| `interleaving`, `interleaving_sym` | **ported**: `Interleaving`, `Interleaving.symm` |
| `interleaving_cat_pair`, `interleaving_mem_left`, `interleaving_split_left_prefix`, `interleaving_first_left` | **pending** |
| `pumping_decompose`, `pumping_interleaving_left`, `pumping_interleaving_right` | **pending** |
| `shuffle_closed`, `seed_covers`, `covered_by`, `seed_shuffle_covered`, `seed_corpus`, `shuffle_lang` | **pending** |
| `pumping_closure_seed_corpus`, `same_seed_corpus_shuffle_closed` | **pending** |
| `seed_covers_trans`, `seed_covers_interleaving_left`, `seed_covers_interleaving_right`, `seed_cover_interleaving_factor` | **pending** |
| `seed_corpus_shuffle_covered_closed`, `seed_shuffle_coveredP` | **pending** |
| `seed_covers_refl`, `seed_covers_size_ge`, `seed_covers_same_size`, `seed_covers_antisym`, `distinct_seed_covers_size_lt`, `seed_covers_principal_inclusion` | **pending** |
| `minimal_seed_corpus`, `minimal_seed_corpus_sub`, `minimal_seed_representative`, `minimal_seed_corpus_seed_corpus` | **pending** |
| `minimal_seed_shuffle_closed`, `minimal_seed_corpus_exact_shuffle_closed` | **pending** |
| `canonical_seed_from`, `canonical_seed`, `canonical_shuffle_stable` | **pending** |
| `cat_singler_cons`, `canonical_seed_from_cat`, `canonical_seed_from_all_mem`, `canonical_seed_from_all_seen`, `canonical_seed_cat_self` | **pending** |
| `canonical_seed_from_seen_mem`, `canonical_seed_from_insert_seen`, `pumping_canonical_seed`, `seed_covers_canonical_seed` | **pending** |
| `interleaving_cat`, `canonical_seed_from_closure`, `canonical_seed_covers`, `canonical_shuffle_stable_seed_shuffle_covered` | **pending** |
| `stable_minimal_seed_canonical`, `stable_pumping_closureP` | **pending** |
| `all_mem_cat_r`, `all_mem_rcons_seen`, `all_mem_rcons_cat`, `canonical_seed_from_absorb` | **pending** |
| `canonical_interleaving_factor_from`, `canonical_interleaving_factor`, `minimal_seed_corpus_shuffle_closed` | **pending** |
| four `interleaving_*` examples | **pending** |

## Prefix and permutation special cases

| Rocq declarations | Status / Lean replacement |
|---|---|
| `prefix_of`, `prefix_include` | **pending** (`List.IsPrefix` will replace `prefix_of`) |
| `perm_word`, `permutation_collection` | **pending** (`List.Perm` will replace `perm_word`) |
| `interleaving_count_mem` | **pending** |
| `prefix_of_mem`, `prefix_of_count_le`, `prefix_of_refl`, `prefix_of_trans`, `prefix_of_rcons`, `prefix_of_size`, `prefix_of_same_size` | **Mathlib/pending adapters** |
| `prefix_of_comparable_by_size`, `prefix_of_comparable`, `prefix_of_rcons_cases` | **pending** |
| `interleaving_r`, `interleaving_r_prepend_left`, `interleaving_r_prepend_right`, `interleaving_to_r` | **pending** |
| `pumping_preserves_mem`, `seed_covers_mem`, `seed_covers_append_seen`, `seed_covers_extend` | **pending** |
| `comparable_prefix_interleaving_r_cover`, `comparable_prefix_interleaving_cover` | **pending** |
| `prefix_include_seed_shuffle_covered`, `prefix_include_pumping_closure_shuffle_closed` | **pending** |
| `interleaving_mem`, `perm_word_mem`, `perm_word_count` | **pending** |
| `duplicate_decompose`, `count_strict_witness`, `multiset_seed_cover` | **pending** |
| `permutation_collection_seed_shuffle_covered`, `permutation_collection_pumping_closure_shuffle_closed` | **pending** |

No declaration is marked complete merely because a shell/API analogue exists: a
status becomes **ported** only after the Lean declaration type-checks in the
local verification environment.
