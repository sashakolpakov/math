import OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialEvaluation
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold

/-! # Polynomial Coordinate Chart -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PolynomialCoordinateChart.AnalyticLocal

noncomputable section

/-! The usual coordinate homeomorphism of affine polynomial points
is an actual regular chart in the native analytic atlas. -/

open Set
open scoped ContDiff

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold

def polynomialCoordinateChart (n : ℕ) :
    OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial (Fin n) ℂ)) (Fin n → ℂ) :=
  (ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph (Fin n)).toOpenPartialHomeomorph

theorem polynomialCoordinateChart_mem_atlas (n : ℕ) :
    polynomialCoordinateChart n ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas (MvPolynomial (Fin n) ℂ) n := by
  constructor
  · intro P
    exact (ComplexPoints.Analytic.PolynomialImplicit.contDiff_polynomial_eval P ω).contDiffOn
  · refine ⟨1, fun x _ => by rw [map_one]; exact one_ne_zero, ?_⟩
    intro i
    refine ⟨MvPolynomial.X i, 0, ?_⟩
    intro x _
    change x (MvPolynomial.X i) = x (MvPolynomial.X i) / (x 1) ^ 0
    rw [pow_zero, div_one]

theorem polynomialCoordinateChart_eval (n : ℕ)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial (Fin n) ℂ)) (P : MvPolynomial (Fin n) ℂ) :
    MvPolynomial.eval (polynomialCoordinateChart n x) P = x P := ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointEquiv_eval x P

end

end OAI.AlgebraicGeometry.Comparison.Betti.PolynomialCoordinateChart.AnalyticLocal
