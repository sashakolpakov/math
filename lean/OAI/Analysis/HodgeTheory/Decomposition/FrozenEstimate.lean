import OAI.Analysis.HodgeTheory.Decomposition.FrozenEnergy
import OAI.Analysis.HodgeTheory.Decomposition.FourierMoment

/-! # Frozen Estimate -/

namespace OAI.Analysis.HodgeTheory.Decomposition.FrozenEstimate.Constructions

noncomputable section

/-! The actual frozen Hodge differential energy controls the first-order
Fourier moment, with a proved positive constant at each chart point. -/

open FourierTransform _root_.MeasureTheory
open scoped SchwartzMap

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)

theorem projectiveFrozen_firstOrder_estimate :
    ∃ c : ℝ, 0 < c ∧
      ∀ a : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)),
        c * (∫ ξ, ‖ξ‖ ^ 2 * ‖𝓕 a ξ‖ ^ 2) ≤
          (∫ x, (inner ℂ (PrincipalAdjoint.Constructions.projectiveComplexWeight V e (n + 1 + 1) z (FrozenFourier.Constructions.projectiveFrozenD V (n + 1) a x))
            (FrozenFourier.Constructions.projectiveFrozenD V (n + 1) a x)).re) +
          (∫ x, (inner ℂ (PrincipalAdjoint.Constructions.projectiveComplexWeight V e n z (FrozenFourier.Constructions.projectiveFrozenDelta V e n he z hz a x))
            (FrozenFourier.Constructions.projectiveFrozenDelta V e n he z hz a x)).re) := by
  obtain ⟨c₀, hc₀, hbound⟩ := SymbolEllipticity.Constructions.projectiveHodgeSymbolEnergy_coercive V e he n
    (K := {z}) (isCompact_singleton) (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact hz)
  let κ : ℂ := 2 * Real.pi * Complex.I
  have hκ : κ ≠ 0 := by
    dsimp only [κ]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  refine ⟨‖κ‖ ^ 2 * c₀, mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hκ)) hc₀, fun a => ?_⟩
  let D := FrozenFourier.Constructions.projectiveFrozenD V (n + 1) a
  let δ := FrozenFourier.Constructions.projectiveFrozenDelta V e n he z hz a
  let A := PrincipalAdjoint.Constructions.projectiveComplexWeight V e (n + 1 + 1) z
  let B := PrincipalAdjoint.Constructions.projectiveComplexWeight V e n z
  let q := fun ξ => (inner ℂ (A (𝓕 D ξ)) (𝓕 D ξ)).re + (inner ℂ (B (𝓕 δ ξ)) (𝓕 δ ξ)).re
  have hD : Integrable (fun ξ => (inner ℂ (A (𝓕 D ξ)) (𝓕 D ξ)).re) volume :=
    Complex.reCLM.integrable_comp (WeightedPlancherel.Constructions.schwartz_inner_integrable (SchwartzMap.postcompCLM A (𝓕 D)) (𝓕 D))
  have hδ : Integrable (fun ξ => (inner ℂ (B (𝓕 δ ξ)) (𝓕 δ ξ)).re) volume :=
    Complex.reCLM.integrable_comp (WeightedPlancherel.Constructions.schwartz_inner_integrable (SchwartzMap.postcompCLM B (𝓕 δ)) (𝓕 δ))
  have hq : Integrable q volume := hD.add hδ
  have hpoint (ξ : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
      q ξ = ‖κ‖ ^ 2 * SymbolEllipticity.Constructions.projectiveHodgeSymbolEnergy V e n (z, innerSL ℝ ξ, 𝓕 a ξ) := by
    dsimp only [q, D, δ, A, B, κ]
    rw [FrozenFourier.Constructions.projectiveFrozenD_fourier, FrozenFourier.Constructions.projectiveFrozenDelta_fourier,
      WeightedPlancherel.Constructions.complex_weighted_inner_smul, WeightedPlancherel.Constructions.complex_weighted_inner_smul, norm_neg,
      PrincipalAdjoint.Constructions.projectiveHodgeSymbolEnergy_complex V e n he z hz]
    ring
  have hpointbound (ξ : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
      (‖κ‖ ^ 2 * c₀) * (‖ξ‖ ^ 2 * ‖𝓕 a ξ‖ ^ 2) ≤ q ξ := by
    have h := hbound z (Set.mem_singleton z) (innerSL ℝ ξ) (𝓕 a ξ)
    rw [innerSL_apply_norm] at h
    rw [hpoint]
    have hh := mul_le_mul_of_nonneg_left h (sq_nonneg ‖κ‖)
    simpa only [mul_assoc] using hh
  have hInt := integral_mono ((FourierMoment.Constructions.schwartz_normsq_moment_integrable (𝓕 a)).const_mul (‖κ‖ ^ 2 * c₀)) hq hpointbound
  rw [integral_const_mul] at hInt
  have hqInt : (∫ ξ, q ξ) = ‖κ‖ ^ 2 * ∫ ξ, SymbolEllipticity.Constructions.projectiveHodgeSymbolEnergy V e n (z, innerSL ℝ ξ, 𝓕 a ξ) := by
    simp_rw [hpoint]
    exact integral_const_mul _ _
  rw [hqInt] at hInt
  exact hInt.trans_eq (FrozenEnergy.Constructions.projectiveFrozenEnergy_fourier V e n he z hz a).symm

end

end OAI.Analysis.HodgeTheory.Decomposition.FrozenEstimate.Constructions
