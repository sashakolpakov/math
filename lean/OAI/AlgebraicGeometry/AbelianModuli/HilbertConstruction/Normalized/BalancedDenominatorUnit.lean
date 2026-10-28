import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.MonomialChartFractions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FrameChartNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.BalancedDenominatorIdentity

/-! # Balanced Denominator Unit -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.BalancedDenominatorUnit

noncomputable section

/-! Evaluation at the normalized chart coordinates makes its defining
balanced denominator a unit in the chart ring itself. An explicit
balanced fraction supplies the inverse. -/
open scoped BigOperators Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {r m : ℕ}

theorem normalizedBalancedDenominator_isUnit (hr : 0 < r)
    (i : Fin m) (σ : Fin r → Fin m) (e : Fin m) (c : Fin m → Fin r)
    (a : (Fin r → Fin m) → ℕ) (C : Fin m → (Fin r → Fin m) → ℕ)
    (ha : a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hC : ∀ z, C z + Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) = a)
    (hframe : Frame.ChartDenominators.frameDiscriminantExponent σ e ≤ a) :
    IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ
      (Balanced.FrameChartNormalization.balancedFrameChartVectors R i σ e c a C ha hC)) a) := by
  let b := ((r - 1) * ∑ τ, a τ) • Frame.ChartDenominators.frameDiscriminantExponent σ e + a
  let d := (Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i) • Frame.NormalizationBlockDegrees.allFrameCoordinateExponent σ e c
  have hsupp (τ) (hτ : b τ ≠ 0) : 0 < a τ := by
    by_contra! hn
    have ha0 : a τ = 0 := Nat.eq_zero_of_le_zero hn
    have hδ0 : Frame.ChartDenominators.frameDiscriminantExponent σ e τ = 0 := Nat.eq_zero_of_le_zero (ha0 ▸ hframe τ)
    change ((r - 1) * ∑ τ, a τ) * Frame.ChartDenominators.frameDiscriminantExponent σ e τ + a τ ≠ 0 at hτ
    simp only [ha0, hδ0, mul_zero, zero_add, ne_eq, not_true_eq_false] at hτ
  have hd : ∀ j, Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight d j = Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight b j :=
    Frame.NormalizationBlockDegrees.normalizedDenominatorInverse_equal_degrees hr σ e c a ha i
  obtain ⟨F, hF⟩ := Balanced.MonomialChartFractions.supportedMonomial_exists_chart_fraction R i a ha b d hsupp hd
  let E : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i a ha →+* BalancedChart.AmbientFrame.balancedChartAmbientRing R a :=
    Homogeneous.SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding (Balanced.DeterminantAlgebra.balancedDeterminantAlgebra R r m)
    (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i) (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha)
  let v := BalancedChart.AmbientFrame.balancedChartAmbientVectors R a
  let u := Balanced.FrameChartNormalization.balancedFrameChartVectors R i σ e c a C ha hC
  let p := Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ u) a
  have hF' : E F * Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) b =
      Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) d := hF
  have hx (z k) : E (u z k) * Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v)
        (Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z)) =
      DeterminantFrameLinearMap.determinantFrameLinearMap (Pi.basisFun (BalancedChart.AmbientFrame.balancedChartAmbientRing R a) (Fin r))
        (fun j => v (σ j)) (v e) (v z) k := by
    exact (BalancedChart.AmbientFrame.balancedFrameChartCoordinate_ambient_crossMultiply R i σ e z (c z) k a (C z) ha (hC z)).trans
      (Frame.CoordinateMonomials.frameCoordinateExponent_linearMap σ v e z k)
  have hp : E p = Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ (fun z k => E (u z k))) a := by
    rw [MonomialExponentExtension.exponentMonomial_map]
    congr 1
    funext τ
    exact LabeledDeterminantPolynomials.labeledDeterminant_map E τ u
  have hid := BalancedDenominatorIdentity.normalizedBalancedDenominator_identity v (fun z k => E (u z k)) σ e c a ha i hx
  rw [← hp] at hid
  have hbunit : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) b) := by
    rw [Balanced.MonomialAlgebra.exponentMonomial_add, NonvanishingMonomialCompletion.exponentMonomial_nsmul, Frame.ChartDenominators.frameDiscriminantExponent_monomial]
    exact ((BalancedChart.AmbientFrame.balancedChartAmbientVectors_frame_isUnit R σ e a hframe).pow _).mul
      (BalancedChart.AmbientFrame.balancedChartAmbientVectors_denominator_isUnit R a)
  have hmul : p * F = 1 := by
    apply Homogeneous.SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding_injective (Balanced.DeterminantAlgebra.balancedDeterminantAlgebra R r m)
      (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i) (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha)
    change E (p * F) = E 1
    rw [map_mul, map_one]
    apply hbunit.mul_right_cancel
    calc
      (E p * E F) * Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) b =
          E p * (E F * Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) b) := mul_assoc _ _ _
      _ = E p * Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) d := by rw [hF']
      _ = Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) b := hid
      _ = 1 * Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) b := (one_mul _).symm
  exact ⟨⟨p, F, hmul, (mul_comm F p).trans hmul⟩, rfl⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.BalancedDenominatorUnit
