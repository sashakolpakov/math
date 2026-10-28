import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.BochnerFunctional
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.BochnerTestDensity

/-! # Bochner Integral -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.BochnerIntegral

noncomputable section

/-! On every original smooth form the continuous native H¹ functional is exactly the complete compact Bochner integral. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] EnergyContinuousExt.smoothCore_fullNormedSpace EnergyContinuousExt.smoothCore_fullInnerProductSpace
  EnergyContinuousExt.smoothCore_normedSpace EnergyContinuousExt.smoothCore_innerProductSpace

def HolomorphicH1BochnerTestFunctionalOnSmooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 : Prop :=
  ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (hq : HasCompactSupport q)
    (hsq : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1),
    BochnerFunctional.holomorphicMetricH1BochnerTestFunctional V h e he i f hf hsf q hq hsq (EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h a) =
      ∫ z, h.projectiveBochnerWeakPair V e i (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hsf a.val)
        (SchwartzCovectorField.schwartzCovectorField (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 q) z

theorem holomorphicMetricH1BochnerTestFunctional_on_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 :
    HolomorphicH1BochnerTestFunctionalOnSmooth V h := by
  intro e he i f hf hsf q hq hsq a
  let L := HolomorphicFrame.FrameLocalization.holomorphicMetricFrameH1Localization V h e he i f hf hsf (EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h a)
  let G := Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) L
  let J := ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) L
  let T := h.projectiveBochnerGradientSchwartzTest V e he i q hq hsq
  let S := h.projectiveBochnerValueSchwartzTest V e he i q hq hsq
  have hJ : J = HolomorphicFrame.CoordinatesLp.holomorphicLineFrameCoefficientsLp V e he i 1 f hf hsf a.val :=
    (congrArg (ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1))
      (HolomorphicFrame.FrameLocalization.holomorphicMetricFrameH1Localization_on_smooth V h e he i f hf hsf a)).trans
      ((Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange.Constructions.vectorSobolevL2Embedding_schwartz (by norm_num : (0 : ℝ) ≤ 1)
        (HolomorphicFrame.Schwartz.holomorphicLineFrameCoefficientsSchwartz V e he i 1 f hf hsf a.val)).trans
        (HolomorphicFrame.Schwartz.holomorphicLineFrameCoefficientsSchwartz_toLp V e he i 1 f hf hsf a.val))
  have hJa : ∀ᵐ z ∂(volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
      J z = HolomorphicFrame.CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i 1 f hf hsf a.val z :=
    (HolomorphicFrame.CoordinatesLp.holomorphicLineFrameCoefficients_memLp V e he i 1 f hf hsf a.val).coeFn_toLp.mono
      (fun z hz => (congrArg (fun v : Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 volume => v z) hJ).trans hz)
  have hsplit : inner ℝ G (T.toLp 2 volume) + inner ℝ J (S.toLp 2 volume) =
      ∫ z, inner ℝ (G z) (T.toLp 2 volume z) + inner ℝ (J z) (S.toLp 2 volume z) :=
    (congrArg₂ (fun x y : ℝ => x + y) (L2.inner_def G (T.toLp 2 volume))
      (L2.inner_def J (S.toLp 2 volume))).trans
      (integral_add (L2.integrable_inner (𝕜 := ℝ) G (T.toLp 2 volume))
        (L2.integrable_inner (𝕜 := ℝ) J (S.toLp 2 volume))).symm
  apply hsplit.trans
  apply integral_congr_ae
  apply Filter.Eventually.mono ((BochnerTestDensity.holomorphicMetricFrameH1_bochner_test_density V h e he i f hf hsf q hq hsq a).and
    (hJa.and ((T.coeFn_toLp 2 volume).and (S.coeFn_toLp 2 volume))))
  intro z hz
  exact (congrArg₂ (fun x y : ℝ => x + y)
    (congrArg (fun v => inner ℝ (G z) v) hz.2.2.1)
    (congrArg₂ (fun v w => inner ℝ v w) hz.2.1 hz.2.2.2)).trans hz.1.symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.BochnerIntegral
