import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.DivisorIntersection
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RightZero
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowSymmetry

/-! # Divisor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.Divisor

noncomputable section

/-! Exact bilinear Chow intersection with a divisor in every dimension,
every codimension, and either order, including disconnected schemes. -/

open _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
  [SmoothOfRelativeDimension m X.structureMap]

include m in
theorem chowIntersection_map_exists (q : ℕ) :
    ∃ I : ProperCycleLinearity.ChowQ X 1 →ₗ[ℚ] ProperCycleLinearity.ChowQ X q →ₗ[ℚ] ProperCycleLinearity.ChowQ X (1 + q),
      ∀ a b, ProperCycleLinearity.chowIntersection X 1 q a b = {I a b} := by
  cases q with
  | zero => exact ⟨RightZero.chowIntersectionMap X m 1,
      RightZero.chowIntersection_eq_singleton X m 1⟩
  | succ k => exact DivisorIntersection.Positive.chowIntersection_map_exists X m k

include m in
theorem right_map_exists (p : ℕ) :
    ∃ I : ProperCycleLinearity.ChowQ X p →ₗ[ℚ] ProperCycleLinearity.ChowQ X 1 →ₗ[ℚ] ProperCycleLinearity.ChowQ X (p + 1),
      ∀ a b, ProperCycleLinearity.chowIntersection X p 1 a b = {I a b} := by
  obtain ⟨I, hI⟩ := chowIntersection_map_exists X m p
  exact ChowSymmetry.reverse_map_exists X 1 p I hI

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.Divisor
