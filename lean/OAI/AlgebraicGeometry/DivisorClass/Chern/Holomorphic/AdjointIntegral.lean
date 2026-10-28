import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AdjointPointPairs
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FormCompletion

/-! # Adjoint Integral -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AdjointIntegral

noncomputable section

/-! Integration by parts for the actual bundle Dolbeault operator and the
constructed smooth metric codifferential, with the original metric measure. -/

open _root_.MeasureTheory _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal
local instance adjointIntegral_realDimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    FiniteDimensional ℝ V.analyticModel := FiniteDimensional.trans ℝ ℂ V.analyticModel

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)

theorem holomorphicLineFrameAdjointPair_integral (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) :
    (∫ x, FormPartition.holomorphicLineComplexPartition u i x *
      FormIntegralPair.holomorphicLineGlobalFormPair V u 1 b (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a) x ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) =
        FormIntegralPair.holomorphicLineFormIntegralPair V u 0 (HolomorphicMetric.Codifferential.holomorphicLineFrameAdjoint V u i b) a := by
  calc
    _ = ∫ x, Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 1 (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension u i 1 b).val
        (Projective.ScalarDolbeaultAdjoint.projectiveScalarDolbeaultZero V (HolomorphicFrame.Tests.holomorphicLineFrameTest V u i a)).val x ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => (AdjointPointPairs.holomorphicLineFrameAdjointPair_left V u i a b x).symm)
    _ = ∫ x, Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 0
        (Projective.ScalarDolbeaultAdjoint.projectiveScalarDolbeaultAdjoint V (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension u i 1 b)).val
        (HolomorphicFrame.Tests.holomorphicLineFrameTest V u i a).val x ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V :=
      Projective.ScalarDolbeaultAdjoint.projectiveScalarDolbeaultAdjoint_actualIntegral V (HolomorphicFrame.Tests.holomorphicLineFrameTest V u i a)
        (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension u i 1 b)
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (AdjointPointPairs.holomorphicLineFrameAdjointPair_right V u i a b))

theorem holomorphicLineFrameDerivativePair_integrable (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) :
    Integrable (fun x => FormPartition.holomorphicLineComplexPartition u i x *
      FormIntegralPair.holomorphicLineGlobalFormPair V u 1 b (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a) x) (ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) := by
  have h := Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveFormPointPair_integrable V 1 (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension u i 1 b)
    (Projective.ScalarDolbeaultAdjoint.projectiveScalarDolbeaultZero V (HolomorphicFrame.Tests.holomorphicLineFrameTest V u i a))
  rw [Projective.MetricAdjoint.projectiveMetricVolume_eq_variety V] at h
  have he := funext (AdjointPointPairs.holomorphicLineFrameAdjointPair_left V u i a b)
  rw [he] at h
  exact h

theorem holomorphicLineFormIntegralPair_sum_left {ι : Type*} [Fintype ι] (n : ℕ)
    (a : ι → HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    FormIntegralPair.holomorphicLineFormIntegralPair V u n (∑ i, a i) b = ∑ i, FormIntegralPair.holomorphicLineFormIntegralPair V u n (a i) b := by
  rw [← FormCompletion.holomorphicFormL2Inclusion_inner, map_sum, sum_inner]
  exact Finset.sum_congr rfl fun i _ => FormCompletion.holomorphicFormL2Inclusion_inner V u n (a i) b

theorem holomorphicLineMetricCodifferential_apply (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) :
    HolomorphicMetric.Codifferential.holomorphicLineMetricCodifferential V u b = ∑ i, HolomorphicMetric.Codifferential.holomorphicLineFrameAdjoint V u i b := by
  simp only [HolomorphicMetric.Codifferential.holomorphicLineMetricCodifferential, LinearMap.sum_apply]

theorem holomorphicLineMetricCodifferential_pair
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) :
    FormIntegralPair.holomorphicLineFormIntegralPair V u 1 b (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a) =
      FormIntegralPair.holomorphicLineFormIntegralPair V u 0 (HolomorphicMetric.Codifferential.holomorphicLineMetricCodifferential V u b) a := by
  calc
    _ = ∫ x, ∑ i, FormPartition.holomorphicLineComplexPartition u i x *
        FormIntegralPair.holomorphicLineGlobalFormPair V u 1 b (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a) x ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      change FormIntegralPair.holomorphicLineGlobalFormPair V u 1 b (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a) x =
        ∑ i, FormPartition.holomorphicLineComplexPartition u i x *
          FormIntegralPair.holomorphicLineGlobalFormPair V u 1 b (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a) x
      rw [← Finset.sum_mul, FormPartition.holomorphicLineComplexPartition_sum, one_mul]
    _ = ∑ i, ∫ x, FormPartition.holomorphicLineComplexPartition u i x *
        FormIntegralPair.holomorphicLineGlobalFormPair V u 1 b (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a) x ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V :=
      integral_finsetSum _ fun i _ => holomorphicLineFrameDerivativePair_integrable V u i a b
    _ = ∑ i, FormIntegralPair.holomorphicLineFormIntegralPair V u 0 (HolomorphicMetric.Codifferential.holomorphicLineFrameAdjoint V u i b) a :=
      Finset.sum_congr rfl fun i _ => holomorphicLineFrameAdjointPair_integral V u i a b
    _ = _ := by rw [← holomorphicLineFormIntegralPair_sum_left, ← holomorphicLineMetricCodifferential_apply]

theorem holomorphicLineMetricCodifferential_pair_right
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) :
    FormIntegralPair.holomorphicLineFormIntegralPair V u 1 (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a) b =
      FormIntegralPair.holomorphicLineFormIntegralPair V u 0 a (HolomorphicMetric.Codifferential.holomorphicLineMetricCodifferential V u b) := by
  have h := congrArg (starRingEnd ℂ) (holomorphicLineMetricCodifferential_pair V u a b)
  rw [FormIntegralPair.holomorphicLineFormIntegralPair_conj, FormIntegralPair.holomorphicLineFormIntegralPair_conj] at h
  exact h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AdjointIntegral
