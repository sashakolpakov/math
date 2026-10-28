import OAI.AlgebraicGeometry.HilbertScheme.Presentations.PrimeLocalizationUnitExponent
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.OverlapSectionUnits

/-! # Overlap Exponents -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.OverlapExponents

noncomputable section

/-! Actual double-chart units have canonical integer exponents, with
product and inverse laws and a value computable from any scalar-power formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (K : Type u) [Field K] {n : ℕ} (i j : Fin (n + 1)) (hji : j ≠ i)

def projectiveDoubleChartExponent (z : (DoubleChartUnits.ProjectiveDoubleChartRing K i j)ˣ) : ℤ :=
  PrimeLocalizationUnitExponent.primeLocalizationUnitExponent (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize (R := K) i (X j))
    (ChartUnits.projectiveChart_coordinate_prime K i j hji) z

theorem projectiveDoubleChartExponent_of_equation (z : (DoubleChartUnits.ProjectiveDoubleChartRing K i j)ˣ)
    (c : Kˣ) (a b : ℕ)
    (h : (z : DoubleChartUnits.ProjectiveDoubleChartRing K i j) * DoubleChartUnits.projectiveDoubleChartRatio K i j ^ b =
      DoubleChartUnits.projectiveDoubleChartConstant K i j (c : K) * DoubleChartUnits.projectiveDoubleChartRatio K i j ^ a) :
    projectiveDoubleChartExponent K i j hji z = (a : ℤ) - b :=
  PrimeLocalizationUnitExponent.primeLocalizationUnitExponent_of_equation (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize (R := K) i (X j))
    (ChartUnits.projectiveChart_coordinate_prime K i j hji) z
    (Units.map (algebraMap K (AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing K n i)).toMonoidHom c) a b h

theorem projectiveDoubleChartExponent_mul (z w : (DoubleChartUnits.ProjectiveDoubleChartRing K i j)ˣ) :
    projectiveDoubleChartExponent K i j hji (z * w) =
      projectiveDoubleChartExponent K i j hji z + projectiveDoubleChartExponent K i j hji w :=
  PrimeLocalizationUnitExponent.primeLocalizationUnitExponent_mul _ _ z w

def projectiveOverlapUnitExponent
    (z : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j)ˣ) : ℤ :=
  projectiveDoubleChartExponent K i j hji
    (Units.map (OverlapSectionUnits.projectiveDoubleSectionIso K i j).commRingCatIsoToRingEquiv.symm.toMonoidHom z)

theorem projectiveOverlapUnitExponent_of_equation
    (z : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j)ˣ)
    (c : Kˣ) (a b : ℕ)
    (h : (z : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j)) *
      OverlapSectionUnits.projectiveOverlapRatio K i j ^ b = OverlapSectionUnits.projectiveOverlapConstant K i j (c : K) *
        OverlapSectionUnits.projectiveOverlapRatio K i j ^ a) :
    projectiveOverlapUnitExponent K i j hji z = (a : ℤ) - b := by
  let e := (OverlapSectionUnits.projectiveDoubleSectionIso K i j).commRingCatIsoToRingEquiv
  apply projectiveDoubleChartExponent_of_equation K i j hji _ c a b
  have he := congrArg e.symm h
  rw [map_mul, map_pow, map_mul, map_pow] at he
  change e.symm (z : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j)) *
      e.symm (e (DoubleChartUnits.projectiveDoubleChartRatio K i j)) ^ b =
      e.symm (e (DoubleChartUnits.projectiveDoubleChartConstant K i j (c : K))) *
        e.symm (e (DoubleChartUnits.projectiveDoubleChartRatio K i j)) ^ a at he
  rw [e.symm_apply_apply, e.symm_apply_apply] at he
  exact he

theorem projectiveOverlapUnitExponent_mul
    (z w : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j)ˣ) :
    projectiveOverlapUnitExponent K i j hji (z * w) =
      projectiveOverlapUnitExponent K i j hji z + projectiveOverlapUnitExponent K i j hji w := by
  unfold projectiveOverlapUnitExponent
  rw [map_mul, projectiveDoubleChartExponent_mul]

theorem projectiveOverlapUnitExponent_inv
    (z : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j)ˣ) :
    projectiveOverlapUnitExponent K i j hji z⁻¹ = -projectiveOverlapUnitExponent K i j hji z := by
  unfold projectiveOverlapUnitExponent projectiveDoubleChartExponent
  rw [map_inv, PrimeLocalizationUnitExponent.primeLocalizationUnitExponent_inv]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.OverlapExponents
