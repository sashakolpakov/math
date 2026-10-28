import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartUnits

/-! # Double Chart Units -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.DoubleChartUnits

noncomputable section

/-! The actual homogeneous coordinate ring of a double projective
chart is a one-coordinate localization. Its units have scalar-power form. -/

open _root_.MvPolynomial _root_.HomogeneousLocalization

universe u
variable (K : Type u) [Field K] {n : ℕ} (i j : Fin (n + 1))

abbrev ProjectiveDoubleChartRing :=
  HomogeneousLocalization.Away (Hilbert.Polynomial.GradedHilbert.grading K n) (X i * X j)

def projectiveDoubleChartMap : AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing K n i →+* ProjectiveDoubleChartRing K i j :=
  HomogeneousLocalization.awayMap (Hilbert.Polynomial.GradedHilbert.grading K n) (isHomogeneous_X K j) rfl

instance projectiveDoubleChartAlgebra : Algebra (AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing K n i) (ProjectiveDoubleChartRing K i j) :=
  (projectiveDoubleChartMap K i j).toAlgebra

instance projectiveDoubleChart_isLocalization :
    IsLocalization.Away (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize (R := K) i (X j)) (ProjectiveDoubleChartRing K i j) := by
  have h := HomogeneousLocalization.Away.isLocalization_mul
    (𝒜 := Hilbert.Polynomial.GradedHilbert.grading K n) (isHomogeneous_X K i) (isHomogeneous_X K j)
    (show X i * X j = X i * X j from rfl) (show (1 : ℕ) ≠ 0 by decide)
  simpa only [Polynomial.Dehomogenization.PolynomialProjective.dehomogenize_X, Polynomial.Dehomogenization.PolynomialProjective.coordinateFraction, HomogeneousLocalization.Away.isLocalizationElem,
    pow_one, projectiveDoubleChartAlgebra, projectiveDoubleChartMap] using! h

def projectiveDoubleChartRatio : ProjectiveDoubleChartRing K i j :=
  projectiveDoubleChartMap K i j (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j))

def projectiveDoubleChartConstant (c : K) : ProjectiveDoubleChartRing K i j :=
  projectiveDoubleChartMap K i j (algebraMap K (AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing K n i) c)

theorem projectiveDoubleChart_unit_powers (hji : j ≠ i) (z : (ProjectiveDoubleChartRing K i j)ˣ) :
    ∃ (c : Kˣ) (a b : ℕ), (z : ProjectiveDoubleChartRing K i j) * projectiveDoubleChartRatio K i j ^ b =
      projectiveDoubleChartConstant K i j (c : K) * projectiveDoubleChartRatio K i j ^ a := by
  obtain ⟨c, a, b, h⟩ := PrimeLocalizationUnits.primeLocalization_unit_powers (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize (R := K) i (X j))
    (ChartUnits.projectiveChart_coordinate_prime K i j hji) z
  obtain ⟨d, hd⟩ := ChartUnits.projectiveChart_unit_constant K i c
  rw [hd] at h
  exact ⟨d, a, b, h⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.DoubleChartUnits
