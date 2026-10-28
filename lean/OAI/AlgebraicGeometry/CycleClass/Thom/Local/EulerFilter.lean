import OAI.AlgebraicGeometry.CycleClass.Thom.Local.Euler

/-! # Euler Filter -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Local.EulerFilter.Constructions

noncomputable section

/-! Discarding finite cycle components away from the chosen point
preserves the actual local Euler functional. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.Local.Euler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.AtPoint.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem localCycleEuler_cycleAtPoint (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (x : V.carrier)
    (rs : List (V.carrier.presheaf.stalk x)) (d : ℕ) (c : Geometric.DimensionCycles.RationalDimensionCycle V p) :
    Euler.Constructions.localCycleEuler V p x rs d (Cycle.AtPoint.Constructions.cycleAtPoint V p x c) = Euler.Constructions.localCycleEuler V p x rs d c := by
  rw [Euler.Constructions.localCycleEuler_eq_sum, Euler.Constructions.localCycleEuler_eq_filter_sum V p x rs d c]
  change (∑ C ∈ (c.filter (fun C => x ∈ (C.val : Set V.carrier))).support,
    (c.filter (fun C => x ∈ (C.val : Set V.carrier))) C * Euler.Constructions.supportEuler V p x rs d C) = _
  rw [Finsupp.support_filter]
  apply Finset.sum_congr rfl
  intro C hC
  exact congrArg (fun a : ℚ => a * Euler.Constructions.supportEuler V p x rs d C)
    (Finsupp.filter_apply_pos (fun D : Geometric.DimensionCycles.DimensionCycleSupport V p => x ∈ (D.val : Set V.carrier))
      c (Finset.mem_filter.mp hC).2)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Local.EulerFilter.Constructions
