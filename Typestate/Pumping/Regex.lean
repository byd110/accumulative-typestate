import Typestate.Pumping.Basic
import Mathlib.Computability.RegularExpressions

namespace Typestate.Pumping

namespace Language

def IsRegexRegular (L : Language α) : Prop :=
  ∃ r : RegularExpression α, r.matches' = L

theorem IsRegexRegular.congr {L K : Language α}
    (hL : IsRegexRegular L) (h : L = K) : IsRegexRegular K := by
  rcases hL with ⟨r, hr⟩
  exact ⟨r, hr.trans h⟩

end Language

def unionRegex : List (RegularExpression α) → RegularExpression α
  | [] => 0
  | r :: rs => r + unionRegex rs

theorem mem_unionRegex_iff (rs : List (RegularExpression α)) (w : Word α) :
    w ∈ (unionRegex rs).matches' ↔ ∃ r ∈ rs, w ∈ r.matches' := by
  induction rs with
  | nil => simp [unionRegex]
  | cons r rs ih =>
      simp [unionRegex, RegularExpression.matches'_add, Language.mem_add, ih]

def regexWord : Word α → RegularExpression α
  | [] => 1
  | a :: w => RegularExpression.char a * regexWord w

theorem mem_regexWord_iff (s w : Word α) :
    w ∈ (regexWord s).matches' ↔ w = s := by
  induction s generalizing w with
  | nil => simp [regexWord, RegularExpression.matches'_epsilon, Language.mem_one]
  | cons a s ih =>
      constructor
      · intro hw
        rw [regexWord, RegularExpression.matches'_mul] at hw
        rcases Language.mem_mul.mp hw with ⟨x, hx, y, hy, hxy⟩
        simp only [RegularExpression.matches'_char] at hx
        have hy' : y = s := (ih y).mp hy
        subst x
        subst y
        simpa using hxy.symm
      · rintro rfl
        rw [regexWord, RegularExpression.matches'_mul]
        exact Language.mem_mul.mpr
          ⟨[a], by rfl, s, (ih s).mpr rfl, by rfl⟩

def wordUnionRegex (words : List (Word α)) : RegularExpression α :=
  unionRegex (words.map regexWord)

theorem mem_wordUnionRegex_iff [DecidableEq α] (words : List (Word α)) (w : Word α) :
    w ∈ (wordUnionRegex words).matches' ↔ w ∈ words := by
  rw [wordUnionRegex, mem_unionRegex_iff]
  constructor
  · rintro ⟨r, hr, hw⟩
    rcases List.mem_map.mp hr with ⟨s, hs, rfl⟩
    exact (mem_regexWord_iff s w).mp hw ▸ hs
  · intro hw
    exact ⟨regexWord w, List.mem_map.mpr ⟨w, hw, rfl⟩,
      (mem_regexWord_iff w w).mpr rfl⟩

noncomputable def reOfFinset [DecidableEq α] (symbols : Finset α) : RegularExpression α :=
  unionRegex (symbols.toList.map RegularExpression.char)

theorem mem_reOfFinset_iff [DecidableEq α] (symbols : Finset α) (w : Word α) :
    w ∈ (reOfFinset symbols).matches' ↔ ∃ a ∈ symbols, w = [a] := by
  rw [reOfFinset, mem_unionRegex_iff]
  constructor
  · rintro ⟨r, hr, hw⟩
    rcases List.mem_map.mp hr with ⟨a, ha, rfl⟩
    simp only [Finset.mem_toList] at ha
    simp only [RegularExpression.matches'_char] at hw
    exact ⟨a, ha, hw⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨RegularExpression.char a,
      List.mem_map.mpr ⟨a, by simpa using ha, rfl⟩, by rfl⟩

def regexPower (n : Nat) (r : RegularExpression α) : RegularExpression α := r ^ n

def boundedStarBasis [Fintype α] (r : RegularExpression α) : RegularExpression α :=
  unionRegex ((List.range (Fintype.card α + 1)).map fun n => regexPower n r)

theorem mem_boundedStarBasis_iff [Fintype α] (r : RegularExpression α) (w : Word α) :
    w ∈ (boundedStarBasis r).matches' ↔
      ∃ n ≤ Fintype.card α, w ∈ (regexPower n r).matches' := by
  rw [boundedStarBasis, mem_unionRegex_iff]
  constructor
  · rintro ⟨q, hq, hw⟩
    rcases List.mem_map.mp hq with ⟨n, hn, rfl⟩
    exact ⟨n, Nat.lt_succ_iff.mp (by simpa using hn), hw⟩
  · rintro ⟨n, hn, hw⟩
    exact ⟨regexPower n r,
      List.mem_map.mpr ⟨n, by simpa using Nat.lt_succ_iff.mpr hn, rfl⟩, hw⟩

def concatWordLists (xs ys : List (Word α)) : List (Word α) :=
  xs.flatMap fun x => ys.map fun y => x ++ y

theorem mem_concatWordLists_iff [DecidableEq α] (xs ys : List (Word α)) (w : Word α) :
    w ∈ concatWordLists xs ys ↔
      ∃ x ∈ xs, ∃ y ∈ ys, w = x ++ y := by
  simp [concatWordLists, eq_comm]

def starFree : RegularExpression α → Bool
  | .zero | .epsilon | .char _ => true
  | .star _ => false
  | .plus r s | .comp r s => starFree r && starFree s

def wordsOfStarFree : RegularExpression α → List (Word α)
  | .zero => []
  | .epsilon => [[]]
  | .char a => [[a]]
  | .star _ => []
  | .plus r s => wordsOfStarFree r ++ wordsOfStarFree s
  | .comp r s => concatWordLists (wordsOfStarFree r) (wordsOfStarFree s)

theorem wordsOfStarFree_correct [DecidableEq α] (r : RegularExpression α)
    (hr : starFree r = true) (w : Word α) :
    w ∈ r.matches' ↔ w ∈ wordsOfStarFree r := by
  induction r generalizing w with
  | zero => simp [wordsOfStarFree]
  | epsilon => simp [wordsOfStarFree, Language.mem_one]
  | char a =>
      rw [RegularExpression.matches'_char]
      constructor
      · intro h
        simpa [wordsOfStarFree] using h
      · intro h
        simpa [wordsOfStarFree] using h
  | star r => simp [starFree] at hr
  | plus r s ihr ihs =>
      simp only [starFree, Bool.and_eq_true] at hr
      rw [RegularExpression.plus_def, RegularExpression.matches'_add, Language.mem_add]
      simp only [wordsOfStarFree, List.mem_append]
      exact or_congr (ihr hr.1 w) (ihs hr.2 w)
  | comp r s ihr ihs =>
      simp only [starFree, Bool.and_eq_true] at hr
      rw [RegularExpression.comp_def, RegularExpression.matches'_mul, Language.mem_mul]
      change (∃ x ∈ r.matches', ∃ y ∈ s.matches', x ++ y = w) ↔
        w ∈ concatWordLists (wordsOfStarFree r) (wordsOfStarFree s)
      rw [mem_concatWordLists_iff]
      constructor
      · rintro ⟨x, hx, y, hy, hxy⟩
        exact ⟨x, (ihr hr.1 x).mp hx, y, (ihs hr.2 y).mp hy, hxy.symm⟩
      · rintro ⟨x, hx, y, hy, hxy⟩
        exact ⟨x, (ihr hr.1 x).mpr hx, y, (ihs hr.2 y).mpr hy, hxy.symm⟩

def normalizeStarFree (r : RegularExpression α) : RegularExpression α :=
  wordUnionRegex (wordsOfStarFree r)

theorem normalizeStarFree_correct [DecidableEq α] (r : RegularExpression α)
    (hr : starFree r = true) :
    (normalizeStarFree r).matches' = r.matches' := by
  apply Language.ext
  intro w
  rw [normalizeStarFree, mem_wordUnionRegex_iff, ← wordsOfStarFree_correct r hr]

def wordSymbols [DecidableEq α] (w : Word α) : Finset α :=
  w.toFinset

@[simp] theorem mem_wordSymbols [DecidableEq α] (a : α) (w : Word α) :
    a ∈ wordSymbols w ↔ a ∈ w := by
  simp [wordSymbols]

theorem wordSymbols_append [DecidableEq α] (u v : Word α) :
    wordSymbols (u ++ v) = wordSymbols u ∪ wordSymbols v := by
  ext a
  simp [wordSymbols]

inductive PumpSemantic [DecidableEq α] : Finset α → Word α → Word α → Prop
  | nil (seen) : PumpSemantic seen [] []
  | cons (seen) (a : α) (seed block out : Word α) :
      (∀ c ∈ block, c ∈ insert a seen) →
      PumpSemantic (insert a seen) seed out →
      PumpSemantic seen (a :: seed) (a :: (block ++ out))

theorem PumpSemantic.base [DecidableEq α] (seen : Finset α) (seed : Word α) :
    PumpSemantic seen seed seed := by
  induction seed generalizing seen with
  | nil => exact .nil seen
  | cons a seed ih =>
      simpa using PumpSemantic.cons seen a seed [] seed
        (by simp) (ih (insert a seen))

noncomputable def pumpingSingletonRegexFrom [DecidableEq α]
    (seen : Finset α) : Word α → RegularExpression α
  | [] => 1
  | a :: seed =>
      RegularExpression.char a *
        ((reOfFinset (insert a seen)).star *
          pumpingSingletonRegexFrom (insert a seen) seed)

noncomputable def pumpingSingletonRegex [DecidableEq α]
    (fallback : α) (seed : Word α) : RegularExpression α :=
  pumpingSingletonRegexFrom ∅ seed

theorem mem_star_reOfFinset_iff [DecidableEq α] (symbols : Finset α) (w : Word α) :
    w ∈ (reOfFinset symbols).star.matches' ↔ ∀ a ∈ w, a ∈ symbols := by
  rw [RegularExpression.matches'_star, Language.mem_kstar]
  constructor
  · rintro ⟨parts, rfl, hparts⟩ a ha
    rcases List.mem_flatten.mp ha with ⟨part, hpart, hapart⟩
    rcases (mem_reOfFinset_iff symbols part).mp (hparts part hpart) with
      ⟨b, hb, rfl⟩
    have hab : a = b := by simpa using hapart
    simpa [hab] using hb
  · intro hw
    refine ⟨w.map fun a => [a], ?_, ?_⟩
    · induction w with
      | nil => rfl
      | cons a w ih =>
          simp only [List.map_cons, List.flatten_cons, List.singleton_append]
          exact congrArg (a :: ·) (ih fun b hb => hw b (by simp [hb]))
    · intro part hpart
      rcases List.mem_map.mp hpart with ⟨a, ha, rfl⟩
      exact (mem_reOfFinset_iff symbols [a]).mpr ⟨a, hw a ha, rfl⟩

theorem pumpSemantic_iff_mem_regexFrom [DecidableEq α]
    (seen : Finset α) (seed out : Word α) :
    PumpSemantic seen seed out ↔
      out ∈ (pumpingSingletonRegexFrom seen seed).matches' := by
  induction seed generalizing seen out with
  | nil =>
      constructor
      · intro h
        cases h
        rfl
      · intro h
        have hout : out = [] := by
          simpa [pumpingSingletonRegexFrom, RegularExpression.matches'_epsilon,
            Language.mem_one] using h
        subst out
        exact .nil seen
  | cons a seed ih =>
      constructor
      · intro h
        cases h with
        | cons _ _ _ block tail hblock htail =>
            rw [pumpingSingletonRegexFrom, RegularExpression.matches'_mul]
            apply Language.mem_mul.mpr
            refine ⟨[a], by rfl, block ++ tail, ?_, by rfl⟩
            rw [RegularExpression.matches'_mul]
            apply Language.mem_mul.mpr
            exact ⟨block, (mem_star_reOfFinset_iff _ _).mpr hblock,
              tail, (ih _ _).mp htail, rfl⟩
      · intro h
        rw [pumpingSingletonRegexFrom, RegularExpression.matches'_mul] at h
        rcases Language.mem_mul.mp h with ⟨head, hhead, rest, hrest, hout⟩
        have hhead' : head = [a] := by simpa using hhead
        subst head
        rw [RegularExpression.matches'_mul] at hrest
        rcases Language.mem_mul.mp hrest with ⟨block, hblock, tail, htail, hrestEq⟩
        subst out
        have : rest = block ++ tail := hrestEq.symm
        subst rest
        exact PumpSemantic.cons seen a seed block tail
          ((mem_star_reOfFinset_iff _ _).mp hblock)
          ((ih _ _).mpr htail)

theorem pumpSemantic_empty_iff_mem_singletonRegex [DecidableEq α]
    (fallback : α) (seed out : Word α) :
    PumpSemantic ∅ seed out ↔ out ∈ (pumpingSingletonRegex fallback seed).matches' := by
  exact pumpSemantic_iff_mem_regexFrom ∅ seed out

end Typestate.Pumping
