import Typestate.Pumping.Regex

namespace Typestate.Pumping.Examples

inductive Symbol where
  | a | b | c | d
  deriving DecidableEq, Repr

open Symbol

example : pumpAt a [a, b, c, d] 2 0 = [a, b, c, a, d] := by
  rfl

example : pumpsB a [a, b, c, d] [a, b, c, a, d] = true := by
  native_decide

example : Pumps a [a, b] [a, a, b] := by
  exact ⟨0, by decide, 0, by decide, rfl⟩

example : singletonClosureB a [a, b] [a, a, b] = true := by
  native_decide

example :
    PumpingClosure a (singletonLanguage [a, b]) [a, a, b] := by
  exact (singletonClosureB_iff a [a, b] [a, a, b]).mp (by native_decide)

end Typestate.Pumping.Examples
