import Mathlib

/-! # Open Subgroup Discrete -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.OpenSubgroupDiscrete

/-! Discreteness may be checked on an open subgroup. -/

open Set

theorem discreteTopology_of_open_subgroup {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (U : Subgroup H) (hU : IsOpen (U : Set H)) [DiscreteTopology U] :
    DiscreteTopology H := by
  apply discreteTopology_of_isOpen_singleton_one
  have h := hU.isOpenMap_subtype_val ({1} : Set U) (isOpen_discrete _)
  have he : Subtype.val '' ({1} : Set U) = ({1} : Set H) := by simp
  rw [← he]
  exact h

end OAI.NumberTheory.Quaternion.Arithmetic.OpenSubgroupDiscrete
