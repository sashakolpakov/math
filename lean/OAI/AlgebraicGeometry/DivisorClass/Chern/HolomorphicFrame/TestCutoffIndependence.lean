import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.CoefficientValue
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Localization
import OAI.AlgebraicGeometry.DivisorClass.Chern.LpTestSupport

/-! # Test Cutoff Independence -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.TestCutoffIndependence

noncomputable section

/-! Actual bounded frame localizations give the same L² test pairing whenever their cutoffs agree on the test support. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace) (n : ℕ)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
  (k : V.analyticSpace → ℂ) (hk : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ k)
  (hsk : tsupport k ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
  (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
  (hqs : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
  (heq : ∀ z ∈ tsupport q, f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) = k (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z))

include hqs heq in
theorem holomorphicLineFrameCoefficientsLp_pair_cutoffs (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    inner ℝ (CoordinatesLp.holomorphicLineFrameCoefficientsLp V e he i n f hf hsf a) (q.toLp 2 volume) =
      inner ℝ (CoordinatesLp.holomorphicLineFrameCoefficientsLp V e he i n k hk hsk a) (q.toLp 2 volume) := by
  apply LpTestSupport.memLp_real_inner_eq_on_test_support
    (CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i n f hf hsf a)
    (CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i n k hk hsk a) q
    (CoordinatesLp.holomorphicLineFrameCoefficients_memLp V e he i n f hf hsf a)
    (CoordinatesLp.holomorphicLineFrameCoefficients_memLp V e he i n k hk hsk a) (q.memLp 2 volume)
  intro z hz
  have htz := subset_tsupport q hz
  have hfv := CoefficientValue.holomorphicLineFrameCoefficient_inFrame V e i n f hf hsf a (hqs htz)
  have hkv := CoefficientValue.holomorphicLineFrameCoefficient_inFrame V e i n k hk hsk a (hqs htz)
  have hm := congrArg (fun r : ℂ => r •
    Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i).extension z)) (heq z htz)
  exact hfv.trans (hm.trans hkv.symm)

include hqs heq in
theorem holomorphicMetricFrameL2Localization_pair_cutoffs (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (v : Holomorphic.IntegralPairZero.HolomorphicFormL2With V h n) :
    inner ℝ (Localization.holomorphicMetricFrameL2Localization V h e he i n f hf hsf v) (q.toLp 2 volume) =
      inner ℝ (Localization.holomorphicMetricFrameL2Localization V h e he i n k hk hsk v) (q.toLp 2 volume) := by
  let F := Localization.holomorphicMetricFrameL2Localization V h e he i n f hf hsf
  let K := Localization.holomorphicMetricFrameL2Localization V h e he i n k hk hsk
  have hleft : Continuous (fun v : Holomorphic.IntegralPairZero.HolomorphicFormL2With V h n => inner ℝ (F v) (q.toLp 2 volume)) :=
    F.continuous.inner continuous_const
  have hright : Continuous (fun v : Holomorphic.IntegralPairZero.HolomorphicFormL2With V h n => inner ℝ (K v) (q.toLp 2 volume)) :=
    K.continuous.inner continuous_const
  have hpair := (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_dense V h n).equalizer hleft hright (by
    funext a
    have hF := Localization.holomorphicMetricFrameL2Localization_on_smooth V h e he i n f hf hsf a
    have hK := Localization.holomorphicMetricFrameL2Localization_on_smooth V h e he i n k hk hsk a
    have hI := holomorphicLineFrameCoefficientsLp_pair_cutoffs V e he i n f hf hsf k hk hsk q hqs heq a
    exact (congrArg (fun w => inner ℝ w (q.toLp 2 volume)) hF).trans
      (hI.trans (congrArg (fun w => inner ℝ w (q.toLp 2 volume)) hK).symm))
  exact congrFun hpair v

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.TestCutoffIndependence
