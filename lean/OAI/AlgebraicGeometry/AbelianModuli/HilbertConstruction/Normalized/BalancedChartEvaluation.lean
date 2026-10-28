import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.BalancedDenominatorUnit
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.AwayEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.ConfigurationChartEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.MapOverBase

/-! # Balanced Chart Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.BalancedChartEvaluation

noncomputable section

/-! Evaluation at the actual normalized coordinates extends to an
endomorphism of the balanced chart ring using the proved denominator unit. -/
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {r m : ℕ}
variable (i : Fin m) (σ : Fin r → Fin m) (e : Fin m) (c : Fin m → Fin r)
variable (a : (Fin r → Fin m) → ℕ) (C : Fin m → (Fin r → Fin m) → ℕ)
variable (ha : a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
variable (hC : ∀ z, C z + Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) = a)

def normalizedBalancedPolynomialEvaluation :
    Balanced.DeterminantAlgebra.balancedDeterminantAlgebra R r m →ₐ[R] Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i a ha :=
  (MvPolynomial.aeval (fun jk : Fin m × Fin r => Balanced.FrameChartNormalization.balancedFrameChartVectors R i σ e c a C ha hC jk.1 jk.2)).comp
    (Balanced.DeterminantAlgebra.balancedDeterminantAlgebra R r m).val

theorem normalizedBalancedPolynomialEvaluation_denominator :
    normalizedBalancedPolynomialEvaluation R i σ e c a C ha hC (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha) =
      Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ (Balanced.FrameChartNormalization.balancedFrameChartVectors R i σ e c a C ha hC)) a := by
  exact Balanced.ConfigurationChartEvaluation.balancedConfigurationPolynomialEvaluation_denominator (R := R)
    (Balanced.FrameChartNormalization.balancedFrameChartVectors R i σ e c a C ha hC) a ha

theorem normalizedBalancedPolynomialEvaluation_denominator_isUnit (hr : 0 < r)
    (hframe : Frame.ChartDenominators.frameDiscriminantExponent σ e ≤ a) :
    IsUnit (normalizedBalancedPolynomialEvaluation R i σ e c a C ha hC
      (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha)) := by
  rw [normalizedBalancedPolynomialEvaluation_denominator]
  exact BalancedDenominatorUnit.normalizedBalancedDenominator_isUnit R hr i σ e c a C ha hC hframe

def normalizedBalancedChartEndomorphism (hr : 0 < r) (hframe : Frame.ChartDenominators.frameDiscriminantExponent σ e ≤ a) :
    Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i a ha →+* Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i a ha :=
  Homogeneous.AwayEvaluation.homogeneousAwayEvaluation (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i)
    (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha)
    (normalizedBalancedPolynomialEvaluation R i σ e c a C ha hC).toRingHom
    (normalizedBalancedPolynomialEvaluation_denominator_isUnit R i σ e c a C ha hC hr hframe)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.BalancedChartEvaluation
