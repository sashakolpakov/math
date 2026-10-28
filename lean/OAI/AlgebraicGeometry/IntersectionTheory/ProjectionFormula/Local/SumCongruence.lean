import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

/-! # Sum Congruence -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.SumCongruence

noncomputable section

/-! An intersection coefficient only uses input coefficients on
supports containing its generic point. -/

open _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem sum_eq (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (A C : IrreducibleCloseds X.carrier) (a b : X.RationalDimensionCycle p)
    (h : ∀ D : X.DimensionCycleSupport p, CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (D.val : Set X.carrier) → a D = b D) :
    a.sum (fun D c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val A C) =
      b.sum (fun D c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val A C) := by
  let F := Finsupp.linearCombination ℚ (fun D : X.DimensionCycleSupport p => CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val A C)
  change F a = F b
  rw [← sub_eq_zero, ← map_sub]
  change ∑ D ∈ (a - b).support, (a - b) D * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val A C = 0
  apply Finset.sum_eq_zero
  intro D _
  by_cases hxD : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (D.val : Set X.carrier)
  · change (a - b) D * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val A C = 0
    rw [Finsupp.sub_apply, h D hxD, sub_self, zero_mul]
  · have hz : CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val A C = 0 := dite_eq_right (fun hx => hxD hx.1)
    change (a - b) D * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val A C = 0
    rw [hz, mul_zero]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.SumCongruence
