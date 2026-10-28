import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveBochner.SchwartzTests
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Gradient

/-! # Bochner Functional -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The complete compact Bochner test pairing is a continuous functional of the original energy core through its actual H¹ localization. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochnerL2TestFunctional (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (hq : HasCompactSupport q)
    (hsq : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (w : Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) : ℝ :=
  inner ℝ (Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) w)
    ((h.projectiveBochnerGradientSchwartzTest V e he i q hq hsq).toLp 2 volume) +
  inner ℝ (ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) w)
    ((h.projectiveBochnerValueSchwartzTest V e he i q hq hsq).toLp 2 volume)

abbrev Holomorphic.BochnerFunctional.holomorphicMetricH1BochnerTestFunctional (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (hq : HasCompactSupport q)
    (hsq : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (v : Holomorphic.EnergyContinuousExt.HolomorphicSmoothOneEnergyWith V h) : ℝ :=
  h.projectiveBochnerL2TestFunctional V e he i q hq hsq
    (HolomorphicFrame.FrameLocalization.holomorphicMetricFrameH1Localization V h e he i f hf hsf v)

def Holomorphic.BochnerFunctional.HolomorphicH1BochnerTestFunctionalContinuous (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 : Prop :=
  ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (hq : HasCompactSupport q)
    (hsq : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)),
    Continuous (Holomorphic.BochnerFunctional.holomorphicMetricH1BochnerTestFunctional V h e he i f hf hsf q hq hsq)

theorem Holomorphic.BochnerFunctional.holomorphicMetricH1BochnerTestFunctional_continuous (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 :
    Holomorphic.BochnerFunctional.HolomorphicH1BochnerTestFunctionalContinuous V h := by
  intro e he i f hf hsf q hq hsq
  let L := HolomorphicFrame.FrameLocalization.holomorphicMetricFrameH1Localization V h e he i f hf hsf
  let G := Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)
  let J := ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
    (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (E := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
  have result := ((G.continuous.comp L.continuous).inner (𝕜 := ℝ)
    (continuous_const (y := (h.projectiveBochnerGradientSchwartzTest V e he i q hq hsq).toLp 2 volume))).add
      ((J.continuous.comp L.continuous).inner (𝕜 := ℝ)
        (continuous_const (y := (h.projectiveBochnerValueSchwartzTest V e he i q hq hsq).toLp 2 volume)))
  exact result

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
