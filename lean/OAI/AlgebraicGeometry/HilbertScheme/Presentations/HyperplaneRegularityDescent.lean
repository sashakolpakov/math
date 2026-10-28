import OAI.AlgebraicGeometry.HilbertScheme.Presentations.HyperplaneCechExactness
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.HyperplaneSaturationBound
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.CechExactness

/-! # Hyperplane Regularity Descent -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.HyperplaneRegularityDescent.GradedHilbert

noncomputable section

/-! Uniform Čech vanishing descends from the saturated regular hyperplane section. -/

open _root_.MvPolynomial

universe u

theorem coordinate_cech_exact_of_saturated_regular_hyperplane
    {K : Type u} [Field K] {n : ℕ}
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K (n + 1))) (hSat : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
    (hreg : ∀ f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K (n + 1), X 0 * f ∈ I.toIdeal → f ∈ I.toIdeal)
    (P : Polynomial ℚ) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P)
    (D : ℕ) (hhyper : ∀ d : ℤ, (D : ℤ) ≤ d → ∀ q : ℕ,
      Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1)) K
        (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ (Projective.Saturation.GradedHilbert.projectiveSaturation (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I)).toIdeal)
        (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I))) d q) :
    ∀ d : ℤ, (max D (HyperplaneSaturationBound.GradedHilbert.hyperplaneSaturationBound.{u} n P) : ℕ) ≤ d → ∀ q : ℕ,
      Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1 + 1)) K (Hilbert.Polynomial.GradedHilbert.CoordinateRing K (n + 1) ⧸ I.toIdeal)
        (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q := by
  apply Linear.FormQuotient.GradedHilbert.coordinate_cech_exact_of_regular_linearForm I (X 0) (isHomogeneous_X K 0) hreg
  intro d hd q
  have hnonneg : 0 ≤ d := (Int.natCast_nonneg _).trans hd
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hnonneg
  have hm : max D (HyperplaneSaturationBound.GradedHilbert.hyperplaneSaturationBound.{u} n P) ≤ m := by exact_mod_cast hd
  apply (HyperplaneCechExactness.GradedHilbert.coordinateHyperplane_moduleCechExactAt_iff I (m : ℤ) q).mpr
  apply (Saturation.CechExactness.GradedHilbert.saturation_moduleCechExactAt_iff (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I) m
    (HyperplaneSaturationBound.GradedHilbert.coordinateHyperplane_uniform_saturation I hSat hreg P hP m ((le_max_right _ _).trans hm)) q).mpr
  apply hhyper (m : ℤ)
  exact_mod_cast (le_max_left D (HyperplaneSaturationBound.GradedHilbert.hyperplaneSaturationBound.{u} n P)).trans hm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.HyperplaneRegularityDescent.GradedHilbert
