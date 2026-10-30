import Typestate.Pumping.Basic

namespace Typestate.Pumping

inductive Interleaving : Word α → Word α → Word α → Prop
  | nilLeft (v) : Interleaving [] v v
  | nilRight (u) : Interleaving u [] u
  | left (a) {u v w} : Interleaving u v w → Interleaving (a :: u) v (a :: w)
  | right (b) {u v w} : Interleaving u v w → Interleaving u (b :: v) (b :: w)

theorem Interleaving.symm (h : Interleaving u v w) : Interleaving v u w := by
  induction h with
  | nilLeft => exact .nilRight _
  | nilRight => exact .nilLeft _
  | left a _ ih => exact .right a ih
  | right b _ ih => exact .left b ih

end Typestate.Pumping
