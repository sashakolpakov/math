import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferentiateFluxEquation
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferenceBounds
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothCoefficientDerivatives

/-! # Comparison Elliptic -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ComparisonElliptic.CM.Construction

noncomputable section

/-! A second regularity step for the actual weak equation: H1 forcing and
smooth coefficients with bounded first two derivatives give H3 solutions. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ContDiff LineDeriv

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

theorem h2_gradient_difference_bounded (b : OrthonormalBasis ι ℝ E)
    (u : Lp ℂ 2 (volume : Measure E))
    (hu : MemSobolev 2 2
      (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, ℂ))) (m : E) :
    ∃ B : ℝ, ∀ t, ‖DifferenceProduct.CM.Construction.realL2Difference m t (EuclideanGradient.CM.Construction.sobolevVectorGradient b u)‖ ≤ B := by
  obtain ⟨w, hw⟩ := (SobolevDerivativeCoordinates.CM.Construction.memSobolev_l2_iff_embedding_range (by norm_num : (0 : ℝ) ≤ 1) u).mp
    (SobolevDerivativeCoordinates.CM.Construction.h2_coordinate_is_h1 u hu)
  refine ⟨‖EuclideanGradient.CM.Construction.sobolevVectorGradient b‖ * ((2 * Real.pi * ‖m‖) * ‖w‖), fun t => ?_⟩
  rw [← EuclideanGradient.CM.Construction.sobolevVectorGradient_difference]
  apply ((EuclideanGradient.CM.Construction.sobolevVectorGradient b).le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [← hw]
  exact DifferenceBounds.CM.Construction.l2DifferenceQuotient_sobolev_bound m t w

theorem euclidean_elliptic_h3_regularity (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : ContDiff ℝ ∞ A) {L : NNReal} (hL : LipschitzWith L A)
    {C a : ℝ} (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hpos : ∀ x, ∀ w : EuclideanSpace ℂ ι, a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w)
    (hDA : ∀ i : ι, ∃ Lᵢ : NNReal, LipschitzWith Lᵢ (CoefficientDerivative.CM.Construction.coefficientDerivative A (b i)))
    (u f : Lp ℂ 2 (volume : Measure E)) (hsol : EllipticDifferenceEstimate.CM.Construction.IsEuclideanWeakMetricSolution b A u f)
    (hf : MemSobolev 1 2 (f : 𝓢'(E, ℂ))) :
    MemSobolev 3 2
      (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, ℂ)) := by
  have hu := Elliptic.CM.Construction.euclidean_elliptic_h2_regularity b A hL hC ha hpos u f hsol
  have hd (i : ι) : MemSobolev 2 2
      (∂_{b i} (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, ℂ))) := by
    obtain ⟨v, df, hv, _, hder⟩ := DifferentiateFluxEquation.CM.Construction.euclidean_weak_solution_derivative b A hA hL hC (b i) u f hsol hu hf
    rw [← SobolevDifferential.CM.Construction.sobolevL2Derivative_distribution, ← hv]
    apply Elliptic.CM.Construction.euclidean_elliptic_flux_h2_regularity b A hL hC ha hpos v df _ hder
    intro j
    obtain ⟨Lᵢ, hLᵢ⟩ := hDA i
    obtain ⟨B, hB⟩ := CutoffDifferenceBounds.CM.Construction.boundedField_difference_bounded (CoefficientDerivative.CM.Construction.coefficientDerivative A (b i)) hLᵢ
      (CoefficientDerivative.CM.Construction.coefficientDerivative_bound A (hA.differentiable (by simp)) hL (b i))
      (EuclideanGradient.CM.Construction.sobolevVectorGradient b u) (b j) (h2_gradient_difference_bounded b u hu (b j))
    refine ⟨B, fun t => ?_⟩
    rw [map_neg, norm_neg]
    exact hB t
  have h := (SobolevInv.CM.Construction.memSobolev_succ_iff_derivatives b 2
    (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, ℂ))).mpr ⟨hu, hd⟩
  norm_num only [show (2 : ℝ) + 1 = 3 by norm_num] at h
  exact h

theorem euclidean_compact_coefficient_h3_regularity (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : ContDiff ℝ ∞ A) {L : NNReal} (hL : LipschitzWith L A)
    {C a : ℝ} (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hpos : ∀ x, ∀ w : EuclideanSpace ℂ ι, a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w)
    (c : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hc : HasCompactSupport (fun x => A x - c))
    (u f : Lp ℂ 2 (volume : Measure E)) (hsol : EllipticDifferenceEstimate.CM.Construction.IsEuclideanWeakMetricSolution b A u f)
    (hf : MemSobolev 1 2 (f : 𝓢'(E, ℂ))) :
    MemSobolev 3 2
      (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, ℂ)) :=
  euclidean_elliptic_h3_regularity b A hA hL hC ha hpos
    (fun i => SmoothCoefficientDerivatives.CM.Construction.coefficientDerivative_lipschitz A c hA hc (b i)) u f hsol hf

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ComparisonElliptic.CM.Construction
