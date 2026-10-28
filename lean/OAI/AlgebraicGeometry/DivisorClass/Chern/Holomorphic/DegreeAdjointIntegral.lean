import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DegreePointPairs
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AdjointIntegral
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FormCompletion

/-! # Degree Adjoint Integral -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DegreeAdjointIntegral

noncomputable section

/-! Integration by parts for the actual bundle Dolbeault operator and the
constructed smooth metric codifferential, with the original metric measure. -/

open _root_.MeasureTheory _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal
local instance degreeIntegral_realDimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    FiniteDimensional ℝ V.analyticModel := FiniteDimensional.trans ℝ ℂ V.analyticModel

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) (q : ℕ)

theorem holomorphicLineDegreeFrameAdjointPair_integral (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ q) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (q + 1)) :
    (∫ x, FormPartition.holomorphicLineComplexPartition u i x *
      FormIntegralPair.holomorphicLineGlobalFormPair V u (q + 1) b (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ q a).val x ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) =
        FormIntegralPair.holomorphicLineFormIntegralPair V u q (DegreeCodifferential.holomorphicLineDegreeFrameAdjoint V u q i b) a.val := by
  calc
    _ = ∫ x, Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V (q + 1) (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension u i (q + 1) b).val
        (Projective.DolbeaultAdjointDegrees.projectiveScalarDolbeaultDegree V q (DegreeTests.holomorphicLineDegreeFrameTest V u q i a.val)).val x ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => (DegreePointPairs.holomorphicLineDegreeFrameAdjointPair_left V u q i a b x).symm)
    _ = ∫ x, Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V q
        (Projective.DolbeaultAdjointDegrees.projectiveScalarDolbeaultDegreeAdjoint V q (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension u i (q + 1) b)).val
        (DegreeTests.holomorphicLineDegreeFrameTest V u q i a.val).val x ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V :=
      Projective.DolbeaultAdjointDegrees.projectiveScalarDolbeaultDegreeAdjoint_actualIntegral V q (DegreeTests.holomorphicLineDegreeFrameTest V u q i a.val)
        (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension u i (q + 1) b)
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (DegreePointPairs.holomorphicLineDegreeFrameAdjointPair_right V u q i a.val b))

theorem holomorphicLineDegreeFrameDerivativePair_integrable (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ q) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (q + 1)) :
    Integrable (fun x => FormPartition.holomorphicLineComplexPartition u i x *
      FormIntegralPair.holomorphicLineGlobalFormPair V u (q + 1) b (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ q a).val x) (ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) := by
  have h := Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveFormPointPair_integrable V (q + 1) (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension u i (q + 1) b)
    (Projective.DolbeaultAdjointDegrees.projectiveScalarDolbeaultDegree V q (DegreeTests.holomorphicLineDegreeFrameTest V u q i a.val))
  rw [Projective.MetricAdjoint.projectiveMetricVolume_eq_variety V] at h
  have he := funext (DegreePointPairs.holomorphicLineDegreeFrameAdjointPair_left V u q i a b)
  rw [he] at h
  exact h

theorem holomorphicLineDegreeCodifferential_apply (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (q + 1)) :
    DegreeCodifferential.holomorphicLineDegreeCodifferential V u q b = ∑ i, DegreeCodifferential.holomorphicLineDegreeFrameAdjoint V u q i b := by
  simp only [DegreeCodifferential.holomorphicLineDegreeCodifferential, LinearMap.sum_apply]

theorem holomorphicLinePartition_integral (f : V.analyticSpace → ℂ)
    (hf : ∀ i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u,
      Integrable (fun x => FormPartition.holomorphicLineComplexPartition u i x * f x) (ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)) :
    (∫ x, f x ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) =
      ∑ i, ∫ x, FormPartition.holomorphicLineComplexPartition u i x * f x ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V := by
  calc
    _ = ∫ x, ∑ i, FormPartition.holomorphicLineComplexPartition u i x * f x ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      change f x = ∑ i, FormPartition.holomorphicLineComplexPartition u i x * f x
      rw [← Finset.sum_mul, FormPartition.holomorphicLineComplexPartition_sum, one_mul]
    _ = _ := integral_finsetSum _ fun i _ => hf i

theorem holomorphicLineDegreeCodifferential_pair
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ q) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (q + 1)) :
    FormIntegralPair.holomorphicLineFormIntegralPair V u (q + 1) b (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ q a).val =
      FormIntegralPair.holomorphicLineFormIntegralPair V u q (DegreeCodifferential.holomorphicLineDegreeCodifferential V u q b) a.val := by
  have hp := holomorphicLinePartition_integral V u
    (FormIntegralPair.holomorphicLineGlobalFormPair V u (q + 1) b (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ q a).val)
    (fun i => holomorphicLineDegreeFrameDerivativePair_integrable V u q i a b)
  have hi : (∑ i, ∫ x, FormPartition.holomorphicLineComplexPartition u i x *
      FormIntegralPair.holomorphicLineGlobalFormPair V u (q + 1) b (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ q a).val x ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) =
      ∑ i, FormIntegralPair.holomorphicLineFormIntegralPair V u q (DegreeCodifferential.holomorphicLineDegreeFrameAdjoint V u q i b) a.val :=
    Finset.sum_congr rfl fun i _ => holomorphicLineDegreeFrameAdjointPair_integral V u q i a b
  have hs := AdjointIntegral.holomorphicLineFormIntegralPair_sum_left V u q
    (fun i => DegreeCodifferential.holomorphicLineDegreeFrameAdjoint V u q i b) a.val
  have hc := congrArg (fun c => FormIntegralPair.holomorphicLineFormIntegralPair V u q c a.val)
    (holomorphicLineDegreeCodifferential_apply V u q b)
  exact hp.trans (hi.trans (hs.symm.trans hc.symm))

theorem holomorphicLineDegreeCodifferential_pair_right
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ q) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (q + 1)) :
    FormIntegralPair.holomorphicLineFormIntegralPair V u (q + 1) (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ q a).val b =
      FormIntegralPair.holomorphicLineFormIntegralPair V u q a.val (DegreeCodifferential.holomorphicLineDegreeCodifferential V u q b) := by
  have h := congrArg (starRingEnd ℂ) (holomorphicLineDegreeCodifferential_pair V u q a b)
  rw [FormIntegralPair.holomorphicLineFormIntegralPair_conj, FormIntegralPair.holomorphicLineFormIntegralPair_conj] at h
  exact h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DegreeAdjointIntegral
