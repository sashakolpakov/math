import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartLineFrames
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CoordinateLocalizationUnits

/-! # Chart Units -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartUnits

noncomputable section

/-! Standard projective-chart units are field scalars, and each
remaining coordinate ratio is prime in the chart ring. -/

open _root_.MvPolynomial

universe u
variable (K : Type u) [Field K] {n : ℕ} (i : Fin (n + 1))

theorem projectiveChart_unit_constant (z : (AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing K n i)ˣ) :
    ∃ c : Kˣ, (z : AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing K n i) = algebraMap K (AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing K n i) (c : K) := by
  let e := ChartPolynomialEquiv.projectiveChartPolynomialEquiv K i
  have hu : IsUnit (e (z : AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing K n i)) := z.isUnit.map e.toRingHom
  obtain ⟨r, hr, h⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
  obtain ⟨c, rfl⟩ := hr
  refine ⟨c, e.injective ?_⟩
  rw [e.commutes]
  exact h

theorem projectiveChart_coordinate_prime (j : Fin (n + 1)) (hji : j ≠ i) :
    Prime (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize (R := K) i (X j)) := by
  let e := ChartPolynomialEquiv.projectiveChartPolynomialEquiv K i
  have h : e (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j)) = X (⟨j, hji⟩ : ChartPolynomialEquiv.ProjectiveChartVariables i) := by
    change ChartPolynomialEquiv.projectiveChartToPolynomial K i (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j)) = _
    rw [ChartPolynomialEquiv.projectiveChartToPolynomial_coordinate, ChartPolynomialEquiv.normalizedChartVariable, dite_eq_right hji]
  have hp : Prime (e (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j))) := h.symm ▸ X_prime
  exact (MulEquiv.prime_iff e).mp hp

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartUnits
