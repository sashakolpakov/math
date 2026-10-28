import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolevOperators
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothCoefficientDerivatives
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticDifferenceEstimate

/-! # Strong Coefficient Products -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCoefficientProducts.CM.Construction

noncomputable section

/-! Smooth coefficient multiplication preserves all orders of the actual
strong L2 derivatives. No complex-linearity of the coefficient is required. -/

open _root_.MeasureTheory Filter
open scoped ContDiff _root_.Topology

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fintype ι]

omit [Fintype ι] in
theorem coefficient_product_difference_tendsto (A : E → F →L[ℝ] F)
    (hA : ContDiff ℝ ∞ A) {L : NNReal} (hL : LipschitzWith L A)
    {C : ℝ} (hC : ∀ x, ‖A x‖ ≤ C) (m : E) (u du : Lp F 2 (volume : Measure E))
    (hdu : Tendsto (fun t : ℝ => DifferenceProduct.CM.Construction.realL2Difference m t u) (𝓝[≠] 0) (𝓝 du)) :
    let M := LpCoefficients.CM.Construction.boundedFieldLp (p := 2) A hA.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC)
    let N := LpCoefficients.CM.Construction.boundedFieldLp (p := 2) (CoefficientDerivative.CM.Construction.coefficientDerivative A m)
      (CoefficientDerivative.CM.Construction.coefficientDerivative_continuous A hA m).aestronglyMeasurable
      (Filter.Eventually.of_forall (CoefficientDerivative.CM.Construction.coefficientDerivative_bound A (hA.differentiable (by simp)) hL m))
    Tendsto (fun t : ℝ => DifferenceProduct.CM.Construction.realL2Difference m t (M u)) (𝓝[≠] 0) (𝓝 (M du + N u)) := by
  dsimp only
  have hT := CoefficientDerivative.CM.Construction.translatedCoefficientLp_tendsto_varying A hA.continuous hC m
    (fun t => DifferenceProduct.CM.Construction.realL2Difference m t u) du hdu
  have hR := CoefficientDerivative.CM.Construction.differenceCoefficientLp_tendsto A hA hL hC m u
  have h := hT.add hR
  exact h.congr' (Filter.Eventually.of_forall (fun t =>
    (DifferenceProduct.CM.Construction.realL2Difference_coefficient_product A hA.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hC) m t u).symm))

omit [Fintype ι] in
theorem coefficient_product_difference_bounded (A : E → F →L[ℝ] F)
    {L : NNReal} (hL : LipschitzWith L A) {C : ℝ} (hC : ∀ x, ‖A x‖ ≤ C)
    (m : E) (u : Lp F 2 (volume : Measure E))
    (hu : ∃ B : ℝ, ∀ t, ‖DifferenceProduct.CM.Construction.realL2Difference m t u‖ ≤ B) :
    ∃ B : ℝ, ∀ t, ‖DifferenceProduct.CM.Construction.realL2Difference m t (LpCoefficients.CM.Construction.boundedFieldLp A hL.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hC) u)‖ ≤ B := by
  obtain ⟨B, hB⟩ := hu
  have hC₀ : 0 ≤ C := (norm_nonneg (A 0)).trans (hC 0)
  let hAm := hL.continuous.aestronglyMeasurable (μ := (volume : Measure E))
  let hCm : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ C := Filter.Eventually.of_forall hC
  refine ⟨C * B + ((L : ℝ) * ‖m‖) * ‖u‖, fun t => ?_⟩
  rw [DifferenceProduct.CM.Construction.realL2Difference_coefficient_product]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (EllipticDifferenceEstimate.CM.Construction.boundedFieldLp_norm_le_other _ (DifferenceProduct.CM.Construction.translatedCoefficient_measurable A hAm (t • m))
      (DifferenceProduct.CM.Construction.translatedCoefficient_bound A hCm (t • m)) (DifferenceProduct.CM.Construction.translatedCoefficient_bound A hCm (t • m))
      (DifferenceProduct.CM.Construction.realL2Difference m t u)).trans (mul_le_mul_of_nonneg_left (hB t) hC₀)
  · exact EllipticDifferenceEstimate.CM.Construction.boundedFieldLp_norm_le_other _ (DifferenceProduct.CM.Construction.differenceCoefficient_measurable A hAm m t)
      (DifferenceProduct.CM.Construction.differenceCoefficient_bound A hCm m t)
      (Filter.Eventually.of_forall (fun x => DifferenceProduct.CM.Construction.differenceCoefficient_lipschitz_bound A hL m x t)) u

/-- A smooth real-linear coefficient field which is constant outside a compact
set preserves every order of strong Sobolev regularity of actual L2 fields. -/
theorem strongSobolev_coefficient_product (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (A : E → F →L[ℝ] F) (c : F →L[ℝ] F)
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hL : LipschitzWith L A) {C : ℝ} (hC : ∀ x, ‖A x‖ ≤ C)
    (u : Lp F 2 (volume : Measure E)) (hu : StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n u) :
    StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n (LpCoefficients.CM.Construction.boundedFieldLp A hA.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hC) u) := by
  induction n generalizing A c L C u with
  | zero => trivial
  | succ n ih =>
    refine ⟨ih A c hA hc hL hC u hu.1, fun i => ?_⟩
    obtain ⟨du, hdu, hBu, hduN⟩ := hu.2 i
    let M := LpCoefficients.CM.Construction.boundedFieldLp (p := 2) (μ := (volume : Measure E)) A
      hA.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC)
    let N := LpCoefficients.CM.Construction.boundedFieldLp (p := 2) (μ := (volume : Measure E)) (CoefficientDerivative.CM.Construction.coefficientDerivative A (b i))
      (CoefficientDerivative.CM.Construction.coefficientDerivative_continuous A hA (b i)).aestronglyMeasurable
      (Filter.Eventually.of_forall (CoefficientDerivative.CM.Construction.coefficientDerivative_bound A (hA.differentiable (by simp)) hL (b i)))
    refine ⟨M du + N u, coefficient_product_difference_tendsto A hA hL hC (b i) u du hdu,
      coefficient_product_difference_bounded A hL hC (b i) u hBu, ?_⟩
    apply StrongSobolev.CM.Construction.HasStrongSobolevDerivatives.add b n
    · exact ih A c hA hc hL hC du hduN
    · have hdA := SmoothCoefficientDerivatives.CM.Construction.coefficientDerivative_smooth A hA (b i)
      have hdAc : HasCompactSupport (fun x => CoefficientDerivative.CM.Construction.coefficientDerivative A (b i) x - 0) := by
        simpa only [sub_zero] using SmoothCoefficientDerivatives.CM.Construction.coefficientDerivative_compact_support A c hc (b i)
      obtain ⟨Ld, hLd⟩ := SmoothCoefficientDerivatives.CM.Construction.coefficientDerivative_lipschitz A c hA hc (b i)
      exact ih (CoefficientDerivative.CM.Construction.coefficientDerivative A (b i)) 0 hdA hdAc hLd
        (CoefficientDerivative.CM.Construction.coefficientDerivative_bound A (hA.differentiable (by simp)) hL (b i)) u hu.1

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCoefficientProducts.CM.Construction
