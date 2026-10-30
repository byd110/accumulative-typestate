import Mathlib.Computability.Language
import Mathlib.Data.List.GetD

namespace Typestate.Pumping

abbrev Word (α : Type*) := List α
abbrev DLanguage (α : Type*) := Word α → Bool

def DLanguage.denote (L : DLanguage α) : Language α :=
  {w | L w = true}

def singletonLanguage (w : Word α) : Language α :=
  {w}

def pumpAt (fallback : α) (w : Word α) (k i : Nat) : Word α :=
  w.take (k + 1) ++ w.getD i fallback :: w.drop (k + 1)

def Pumps (fallback : α) (u v : Word α) : Prop :=
  ∃ k < u.length, ∃ i ≤ k, v = pumpAt fallback u k i

def pumpSuccs (fallback : α) (u : Word α) : List (Word α) :=
  (List.range u.length).flatMap fun k =>
    (List.range (k + 1)).map fun i => pumpAt fallback u k i

theorem mem_pumpSuccs_iff (fallback : α) (u v : Word α) :
    v ∈ pumpSuccs fallback u ↔ Pumps fallback u v := by
  simp only [pumpSuccs, List.mem_flatMap, List.mem_range, List.mem_map, Pumps]
  constructor
  · rintro ⟨k, hk, i, hi, rfl⟩
    exact ⟨k, hk, i, Nat.lt_succ_iff.mp hi, rfl⟩
  · rintro ⟨k, hk, i, hi, rfl⟩
    exact ⟨k, hk, i, Nat.lt_succ_iff.mpr hi, rfl⟩

def pumpsB [DecidableEq α] (fallback : α) (u v : Word α) : Bool :=
  (pumpSuccs fallback u).contains v

theorem pumpsB_iff [DecidableEq α] (fallback : α) (u v : Word α) :
    pumpsB fallback u v = true ↔ Pumps fallback u v := by
  simp [pumpsB, mem_pumpSuccs_iff]

inductive PumpingClosure (fallback : α) (L : Language α) : Word α → Prop
  | base {w} : w ∈ L → PumpingClosure fallback L w
  | step {u v} : PumpingClosure fallback L u → Pumps fallback u v →
      PumpingClosure fallback L v

@[simp] theorem length_pumpAt (fallback : α) (w : Word α) (k i : Nat)
    (hk : k < w.length) :
    (pumpAt fallback w k i).length = w.length + 1 := by
  simp [pumpAt, List.length_take, List.length_drop]
  omega

theorem Pumps.length_eq (h : Pumps fallback u v) :
    v.length = u.length + 1 := by
  rcases h with ⟨k, hk, i, hi, rfl⟩
  exact length_pumpAt fallback u k i hk

theorem Pumps.fallback_irrel {α : Type*} {fallback : α} {u v : Word α}
    (h : Pumps fallback u v) (other : α) :
    Pumps other u v := by
  rcases h with ⟨k, hk, i, hi, rfl⟩
  refine ⟨k, hk, i, hi, ?_⟩
  have hii : i < u.length := lt_of_le_of_lt hi hk
  simp only [pumpAt]
  rw [List.getD_eq_getElem u fallback hii, List.getD_eq_getElem u other hii]

inductive Reachable (fallback : α) : Nat → Word α → Word α → Prop
  | refl (u) : Reachable fallback 0 u u
  | step {n u mid v} : Pumps fallback u mid → Reachable fallback n mid v →
      Reachable fallback (n + 1) u v

def pumpingClosure (fallback : α) (L : Language α) : Language α :=
  {w | PumpingClosure fallback L w}

@[simp] theorem mem_pumpingClosure :
    w ∈ pumpingClosure fallback L ↔ PumpingClosure fallback L w :=
  Iff.rfl

theorem PumpingClosure.monotone (h : PumpingClosure fallback L w)
    (hLK : ∀ u, u ∈ L → u ∈ K) : PumpingClosure fallback K w := by
  induction h with
  | base hu => exact .base (hLK _ hu)
  | step _ hp ih => exact .step ih hp

theorem PumpingClosure.bind (h : PumpingClosure fallback L w)
    (hbase : ∀ u, u ∈ L → PumpingClosure fallback K u) :
    PumpingClosure fallback K w := by
  induction h with
  | base hu => exact hbase _ hu
  | step _ hp ih => exact .step ih hp

theorem pumpingClosure_idempotent :
    pumpingClosure fallback (pumpingClosure fallback L) = pumpingClosure fallback L := by
  apply Language.ext
  intro w
  constructor
  · intro h
    exact h.bind fun _ hu => hu
  · intro h
    exact .base h

def reachableB [DecidableEq α] (fallback : α) : Nat → Word α → Word α → Bool
  | 0, u, v => decide (u = v)
  | n + 1, u, v => (pumpSuccs fallback u).any fun mid => reachableB fallback n mid v

theorem reachableB_iff [DecidableEq α] (fallback : α) (n : Nat) (u v : Word α) :
    reachableB fallback n u v = true ↔ Reachable fallback n u v := by
  induction n generalizing u with
  | zero =>
      constructor
      · intro h
        have : u = v := by simpa [reachableB] using h
        subst v
        exact .refl u
      · intro h
        cases h
        simp [reachableB]
  | succ n ih =>
      simp only [reachableB, List.any_eq_true, ih, mem_pumpSuccs_iff]
      constructor
      · rintro ⟨mid, hp, hr⟩
        exact .step hp hr

      · intro h
        cases h with
        | step hp hr => exact ⟨_, hp, hr⟩

theorem Reachable.liftClosure (h : Reachable fallback n u v)
    (hu : PumpingClosure fallback L u) : PumpingClosure fallback L v := by
  induction h with
  | refl => exact hu
  | step hp _ ih => exact ih (.step hu hp)

theorem Reachable.toClosure (h : Reachable fallback n u v) :
    PumpingClosure fallback (singletonLanguage u) v := by
  apply h.liftClosure
  exact .base (by rfl)

theorem Reachable.length_eq (h : Reachable fallback n u v) :
    v.length = u.length + n := by
  induction h with
  | refl => simp
  | @step n u mid v hp _ ih =>
      rw [ih, hp.length_eq]
      omega

theorem Reachable.appendStep (h : Reachable fallback n u v)
    (hp : Pumps fallback v w) : Reachable fallback (n + 1) u w := by
  induction h with
  | refl => exact .step hp (.refl w)
  | @step n u mid v huv _ ih =>
      simpa [Nat.add_assoc] using Reachable.step huv (ih hp)

theorem pumpingClosure_singleton_iff :
    PumpingClosure fallback (singletonLanguage seed) w ↔
      ∃ n, Reachable fallback n seed w := by
  constructor
  · intro h
    induction h with
    | @base x hx =>
        have hx' : x = seed := by simpa [singletonLanguage] using hx
        subst x
        exact ⟨0, .refl seed⟩
    | step _ hp ih =>
        rcases ih with ⟨n, hn⟩
        exact ⟨n + 1, hn.appendStep hp⟩
  · rintro ⟨n, hn⟩
    exact hn.toClosure

def singletonClosureB [DecidableEq α] (fallback : α) (seed w : Word α) : Bool :=
  if seed.length ≤ w.length then
    reachableB fallback (w.length - seed.length) seed w
  else false

theorem singletonClosureB_iff [DecidableEq α] (fallback : α) (seed w : Word α) :
    singletonClosureB fallback seed w = true ↔
      PumpingClosure fallback (singletonLanguage seed) w := by
  rw [pumpingClosure_singleton_iff]
  constructor
  · intro h
    by_cases hle : seed.length ≤ w.length
    · simp only [singletonClosureB, if_pos hle] at h
      exact ⟨w.length - seed.length, (reachableB_iff fallback _ _ _).mp h⟩
    · simp [singletonClosureB, hle] at h
  · rintro ⟨n, hn⟩
    have hlen := hn.length_eq
    have hle : seed.length ≤ w.length := by omega
    have hn' : w.length - seed.length = n := by omega
    simp [singletonClosureB, hle, hn', reachableB_iff, hn]

end Typestate.Pumping
