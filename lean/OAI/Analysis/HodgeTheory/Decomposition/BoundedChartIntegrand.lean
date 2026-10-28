import OAI.Analysis.HodgeTheory.Decomposition.LocalEnergy
import OAI.Analysis.HodgeTheory.Decomposition.SchwartzGradientSupport
import OAI.Analysis.HodgeTheory.Decomposition.SchwartzEnergy
import OAI.Analysis.HodgeTheory.Decomposition.CoefficientHodge

/-! # Bounded Chart Integrand -/

namespace OAI.Analysis.HodgeTheory.Decomposition.BoundedChartIntegrand.Constructions

noncomputable section

/-! The bounded H¹ energy agrees with the actual Hodge coefficient
formula on compact chart tests wherever the extensions agree. -/

open _root_.MeasureTheory
open scoped SchwartzMap ContDiff

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (η : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η)
  (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
  (A : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → GradientCoefficient.Constructions.ProjectiveGradientValues V n →L[ℝ] GradientCoefficient.Constructions.ProjectiveGradientValues V n)
  (hAm : AEStronglyMeasurable A volume) {C : ℝ} (hAB : ∀ᵐ x ∂volume, ‖A x‖ ≤ C)

theorem projectiveBoundedChartEnergy_integrand
    (f g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))
    (hf : HasCompactSupport f) (hfs : tsupport f ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hηg : ∀ x ∈ tsupport g, η x = 1)
    (hAg : ∀ x ∈ tsupport g, A x = GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n x) :
    let p := VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
      (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f)
    let q := VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
      (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 g)
    let Bf := ProjectiveFluxSobolev.Constructions.projectiveHodgeFluxCutoffL2 V e n he η hη hηc hηU (f.toLp 2 volume)
    let Cp := ProjectiveLower.Constructions.projectiveHodgeValueGradientCutoffL2 V e n he η hη hηc hηU p
    let Ef := ProjectiveLower.Constructions.projectiveHodgeValueValueCutoffL2 V e n he η hη hηc hηU (f.toLp 2 volume)
    ∀ᵐ x ∂(volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
      inner ℝ (A x (p x)) (q x) + inner ℝ (Bf x) (q x) +
        inner ℝ (Cp x) (g.toLp 2 volume x) + inner ℝ (Ef x) (g.toLp 2 volume x) =
      inner ℝ (GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n x (p x)) (q x) +
        inner ℝ (GradientCoefficient.Constructions.projectiveHodgeFluxCoefficient V e n x (f x)) (q x) +
        inner ℝ (GradientCoefficient.Constructions.projectiveHodgeValueCoefficient V e n x (LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz V e n he f hf hfs x)) (g x) := by
  dsimp only
  let p := VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f)
  let q := VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 g)
  let Bf := ProjectiveFluxSobolev.Constructions.projectiveHodgeFluxCutoffL2 V e n he η hη hηc hηU (f.toLp 2 volume)
  let Cp := ProjectiveLower.Constructions.projectiveHodgeValueGradientCutoffL2 V e n he η hη hηc hηU p
  let Ef := ProjectiveLower.Constructions.projectiveHodgeValueValueCutoffL2 V e n he η hη hηc hηU (f.toLp 2 volume)
  filter_upwards [ProjectiveFluxSobolev.Constructions.projectiveHodgeFluxCutoffL2_coe V e n he η hη hηc hηU (f.toLp 2 volume),
    ProjectiveLower.Constructions.projectiveHodgeValueGradientCutoffL2_coe V e n he η hη hηc hηU p,
    ProjectiveLower.Constructions.projectiveHodgeValueValueCutoffL2_coe V e n he η hη hηc hηU (f.toLp 2 volume),
    f.coeFn_toLp 2 volume, g.coeFn_toLp 2 volume,
    SchwartzGradientSupport.Constructions.vectorSobolevGradient_schwartz_zero_off_support
      (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) g,
    SchwartzEnergy.Constructions.projectiveLocalDelta_normalizedGradient V e n he f hf hfs] with x hBf hCp hEf hfx hgx hq hδ
  change inner ℝ (A x (p x)) (q x) + inner ℝ (Bf x) (q x) +
    inner ℝ (Cp x) (g.toLp 2 volume x) + inner ℝ (Ef x) (g.toLp 2 volume x) =
    inner ℝ (GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n x (p x)) (q x) +
      inner ℝ (GradientCoefficient.Constructions.projectiveHodgeFluxCoefficient V e n x (f x)) (q x) +
      inner ℝ (GradientCoefficient.Constructions.projectiveHodgeValueCoefficient V e n x (LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz V e n he f hf hfs x)) (g x)
  change Bf x = _ at hBf
  change Cp x = _ at hCp
  change Ef x = _ at hEf
  rw [hBf, hCp, hEf, hfx, hgx]
  by_cases hx : x ∈ tsupport g
  · rw [hηg x hx, one_smul, one_smul, one_smul, hAg x hx]
    exact CoefficientHodge.Constructions.projectiveHodge_energy_lower_collect V e n x (p x) (q x) (f x) (g x) _ hδ
  · have hqx : q x = 0 := hq hx
    rw [hqx, image_eq_zero_of_notMem_tsupport hx]
    simp only [inner_zero_right, add_zero]

end

end OAI.Analysis.HodgeTheory.Decomposition.BoundedChartIntegrand.Constructions
