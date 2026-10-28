import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LowerCoefficient
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Localization
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AntiOneSourcePair
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Schwartz
import OAI.AlgebraicGeometry.DivisorClass.Chern.SchwartzSobolevLp

/-! # Forcing Sobolev -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Every compact chart localization of original smooth antiholomorphic forcing has all Sobolev orders, before and after the actual forcing coefficient. -/

open _root_.TopologicalSpace _root_.MeasureTheory TemperedDistribution
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem Holomorphic.ForcingSobolev.holomorphicMetricFrameL2Localization_anti_schwartz (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace)) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    (HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i 1 f hf hsf) ((h.antiOneL2Submodule V).subtypeL (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a)) = (HolomorphicFrame.Schwartz.holomorphicLineFrameCoefficientsSchwartz V e he i 1 f hf hsf a.val).toLp 2 volume :=
  Eq.trans (congrArg (HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i 1 f hf hsf) (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion_val V h a))
    (Eq.trans (HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization_on_smooth V h e he i 1 f hf hsf a.val)
      (HolomorphicFrame.Schwartz.holomorphicLineFrameCoefficientsSchwartz_toLp V e he i 1 f hf hsf a.val).symm)

theorem Holomorphic.ForcingSobolev.holomorphicMetricFrameL2Localization_anti_memSobolev (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace)) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) (s : ℝ) :
    (MemSobolev s 2 ((HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i 1 f hf hsf) ((h.antiOneL2Submodule V).subtypeL (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a)) : 𝓢'(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))) :=
  Eq.mpr (congrArg (fun q : Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) => (MemSobolev s 2 (q : 𝓢'(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))))
    (Holomorphic.ForcingSobolev.holomorphicMetricFrameL2Localization_anti_schwartz V h e he i f hf hsf a))
    (SchwartzSobolevLp.schwartz_toLp_memSobolev s (HolomorphicFrame.Schwartz.holomorphicLineFrameCoefficientsSchwartz V e he i 1 f hf hsf a.val))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineForcingL2_smooth_source (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace)) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) (n : ℕ) :
    MemSobolev (n : ℝ) 2 ((h.projectiveLineForcingL2 V e he i η hη hηc hηU ((HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i 1 f hf hsf) ((h.antiOneL2Submodule V).subtypeL (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a)))) : 𝓢'(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)) :=
  h.projectiveLineForcingL2_memSobolev V e he i η hη hηc hηU n ((HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i 1 f hf hsf) ((h.antiOneL2Submodule V).subtypeL (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a)))
    (Holomorphic.ForcingSobolev.holomorphicMetricFrameL2Localization_anti_memSobolev V h e he i f hf hsf a (n : ℝ))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
