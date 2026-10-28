import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.BochnerFunctional
import OAI.AlgebraicGeometry.DivisorClass.Chern.SchwartzCutoffIdentity

/-! # Functional -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The complete native Bochner test functional on Euclidean H¹ coordinates, with exact separation of its four actual coefficient tests. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace) (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
  (hq : HasCompactSupport q)
  (hs : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))

def ProjectiveBochner.Functional.HolomorphicMetricH1BochnerTestFunctionalL2 : Prop :=
  ∀
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (v : Holomorphic.EnergyContinuousExt.HolomorphicSmoothOneEnergyWith V h),
    Holomorphic.BochnerFunctional.holomorphicMetricH1BochnerTestFunctional V h e he i f hf hsf q hq hs v =
      h.projectiveBochnerL2TestFunctional V e he i q hq hs (HolomorphicFrame.FrameLocalization.holomorphicMetricFrameH1Localization V h e he i f hf hsf v)

theorem ProjectiveBochner.Functional.holomorphicMetricH1BochnerTestFunctional_eq_L2 :
    ProjectiveBochner.Functional.HolomorphicMetricH1BochnerTestFunctionalL2 V h e he i q hq hs := by
  intro f hf hsf v
  exact rfl

def HolomorphicMetric.Data.HolomorphicLineMetricData.ProjectiveBochnerGradientSchwartzTestL2Pair : Prop :=
  ∀
    (a : Lp (GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))),
    inner ℝ a ((h.projectiveBochnerGradientSchwartzTest V e he i q hq hs).toLp 2 volume) =
      inner ℝ a ((Compact.Adjoint.compactAdjointSchwartz (h.projectiveLineSobolevCoefficient V e 1 i) (Compact.SchwartzGradient.compactSchwartzGradient (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq) (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen (h.projectiveLineSobolevCoefficient_smooth V e he 1 i) (Compact.SchwartzGradient.compactSchwartzGradient_compact (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq) ((Compact.SchwartzGradient.compactSchwartzGradient_tsupport (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq).trans hs)).toLp 2 volume) + inner ℝ a ((Compact.Adjoint.compactAdjointSchwartz (h.projectiveLineGradientValueCoefficient V e 1 i) q (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen (h.projectiveLineGradientValueCoefficient_smooth V e he 1 i) hq hs).toLp 2 volume)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochnerGradientSchwartzTest_L2_pair :
    h.ProjectiveBochnerGradientSchwartzTestL2Pair V e he i q hq hs := by
  intro a
  exact SchwartzCutoffIdentity.schwartzLp_inner_add a (Compact.Adjoint.compactAdjointSchwartz (h.projectiveLineSobolevCoefficient V e 1 i) (Compact.SchwartzGradient.compactSchwartzGradient (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq) (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen (h.projectiveLineSobolevCoefficient_smooth V e he 1 i) (Compact.SchwartzGradient.compactSchwartzGradient_compact (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq) ((Compact.SchwartzGradient.compactSchwartzGradient_tsupport (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq).trans hs)) (Compact.Adjoint.compactAdjointSchwartz (h.projectiveLineGradientValueCoefficient V e 1 i) q (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen (h.projectiveLineGradientValueCoefficient_smooth V e he 1 i) hq hs)

def HolomorphicMetric.Data.HolomorphicLineMetricData.ProjectiveBochnerValueSchwartzTestL2Pair : Prop :=
  ∀
    (a : Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))),
    inner ℝ a ((h.projectiveBochnerValueSchwartzTest V e he i q hq hs).toLp 2 volume) =
      inner ℝ a ((Compact.Adjoint.compactAdjointSchwartz (h.projectiveLineValueGradientCoefficient V e 1 i) (Compact.SchwartzGradient.compactSchwartzGradient (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq) (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen (h.projectiveLineValueGradientCoefficient_smooth V e he 1 i) (Compact.SchwartzGradient.compactSchwartzGradient_compact (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq) ((Compact.SchwartzGradient.compactSchwartzGradient_tsupport (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq).trans hs)).toLp 2 volume) + inner ℝ a ((Compact.Adjoint.compactAdjointSchwartz (h.projectiveLineWeakValueCoefficient V e i) q (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen (h.projectiveLineWeakValueCoefficient_smooth V e he i) hq hs).toLp 2 volume)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochnerValueSchwartzTest_L2_pair :
    h.ProjectiveBochnerValueSchwartzTestL2Pair V e he i q hq hs := by
  intro a
  exact SchwartzCutoffIdentity.schwartzLp_inner_add a (Compact.Adjoint.compactAdjointSchwartz (h.projectiveLineValueGradientCoefficient V e 1 i) (Compact.SchwartzGradient.compactSchwartzGradient (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq) (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen (h.projectiveLineValueGradientCoefficient_smooth V e he 1 i) (Compact.SchwartzGradient.compactSchwartzGradient_compact (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq) ((Compact.SchwartzGradient.compactSchwartzGradient_tsupport (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq).trans hs)) (Compact.Adjoint.compactAdjointSchwartz (h.projectiveLineWeakValueCoefficient V e i) q (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen (h.projectiveLineWeakValueCoefficient_smooth V e he i) hq hs)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
