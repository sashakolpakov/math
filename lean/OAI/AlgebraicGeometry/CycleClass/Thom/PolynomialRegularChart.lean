import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialEvaluation

/-! # Polynomial Regular Chart -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialRegularChart.Constructions

noncomputable section

/-! The actual polynomial-coordinate homeomorphism is a regular affine chart. -/

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold
open scoped ContDiff

theorem polynomial_chart_regular (n : ℕ) :
    (ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph (Fin n)).toOpenPartialHomeomorph ∈
      ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas (MvPolynomial (Fin n) ℂ) n := by
  constructor
  · intro p
    exact (ComplexPoints.Analytic.PolynomialImplicit.contDiff_polynomial_eval p ω).contDiffOn
  · refine ⟨1, ?_, ?_⟩
    · intro x _
      simp only [map_one, ne_eq, one_ne_zero, not_false_eq_true]
    · intro j
      refine ⟨MvPolynomial.X j, 0, ?_⟩
      intro x _
      simp only [pow_zero, div_one]
      rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialRegularChart.Constructions
