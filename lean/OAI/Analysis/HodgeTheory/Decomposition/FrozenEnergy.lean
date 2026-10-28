import OAI.Analysis.HodgeTheory.Decomposition.FrozenFourier
import OAI.Analysis.HodgeTheory.Decomposition.WeightedPlancherel

/-! # Frozen Energy -/

namespace OAI.Analysis.HodgeTheory.Decomposition.FrozenEnergy.Constructions

noncomputable section

/-! Exact frozen Hodge energy in Fourier space, using the genuine metric
symbols and the genuine differential normalization. -/

open FourierTransform _root_.MeasureTheory
open scoped SchwartzMap

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)

/-- Plancherel identifies the frozen differential energy with the proved metric symbol energy. -/
theorem projectiveFrozenEnergy_fourier
    (a : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) :
    (∫ x, (inner ℂ (PrincipalAdjoint.Constructions.projectiveComplexWeight V e (n + 1 + 1) z (FrozenFourier.Constructions.projectiveFrozenD V (n + 1) a x))
      (FrozenFourier.Constructions.projectiveFrozenD V (n + 1) a x)).re) +
    (∫ x, (inner ℂ (PrincipalAdjoint.Constructions.projectiveComplexWeight V e n z (FrozenFourier.Constructions.projectiveFrozenDelta V e n he z hz a x))
      (FrozenFourier.Constructions.projectiveFrozenDelta V e n he z hz a x)).re) =
    ‖2 * Real.pi * Complex.I‖ ^ 2 *
      ∫ ξ, SymbolEllipticity.Constructions.projectiveHodgeSymbolEnergy V e n (z, innerSL ℝ ξ, 𝓕 a ξ) := by
  let D := FrozenFourier.Constructions.projectiveFrozenD V (n + 1) a
  let δ := FrozenFourier.Constructions.projectiveFrozenDelta V e n he z hz a
  let A := PrincipalAdjoint.Constructions.projectiveComplexWeight V e (n + 1 + 1) z
  let B := PrincipalAdjoint.Constructions.projectiveComplexWeight V e n z
  have hD : Integrable (fun ξ => (inner ℂ (A (𝓕 D ξ)) (𝓕 D ξ)).re) volume := Complex.reCLM.integrable_comp
    (WeightedPlancherel.Constructions.schwartz_inner_integrable (SchwartzMap.postcompCLM A (𝓕 D)) (𝓕 D))
  have hδ : Integrable (fun ξ => (inner ℂ (B (𝓕 δ ξ)) (𝓕 δ ξ)).re) volume := Complex.reCLM.integrable_comp
    (WeightedPlancherel.Constructions.schwartz_inner_integrable (SchwartzMap.postcompCLM B (𝓕 δ)) (𝓕 δ))
  rw [WeightedPlancherel.Constructions.schwartz_weighted_plancherel_re A D, WeightedPlancherel.Constructions.schwartz_weighted_plancherel_re B δ]
  change (∫ ξ, (inner ℂ (A (𝓕 D ξ)) (𝓕 D ξ)).re) +
    (∫ ξ, (inner ℂ (B (𝓕 δ ξ)) (𝓕 δ ξ)).re) = _
  rw [← integral_add hD hδ, ← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ξ
  dsimp only [D, δ, A, B]
  rw [FrozenFourier.Constructions.projectiveFrozenD_fourier, FrozenFourier.Constructions.projectiveFrozenDelta_fourier,
    WeightedPlancherel.Constructions.complex_weighted_inner_smul, WeightedPlancherel.Constructions.complex_weighted_inner_smul, norm_neg,
    PrincipalAdjoint.Constructions.projectiveHodgeSymbolEnergy_complex V e n he z hz]
  ring

end

end OAI.Analysis.HodgeTheory.Decomposition.FrozenEnergy.Constructions
