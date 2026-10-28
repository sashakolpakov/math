import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Codifferential
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Tests
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FormIntegralPair

/-! # Adjoint Point Pairs -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AdjointPointPairs

noncomputable section

section

/-! Literal pointwise metric identities for the supported scalar adjoints. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff ComplexConjugate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal
local instance adjointPointPairs_realDimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    FiniteDimensional ℝ V.analyticModel := FiniteDimensional.trans ℝ ℂ V.analyticModel

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)

theorem projectiveTangentCovectorPair_zero_left (n : ℕ) (x : V.analyticSpace)
    (b : TangentSpace 𝓘(ℝ, V.analyticModel) x [⋀^Fin n]→L[ℝ] ℂ) :
    Projective.CovectorPair.projectiveTangentCovectorPair V n x 0 b = 0 := by
  have h := Projective.CovectorPair.projectiveTangentCovectorPair_smul_left V n x 0 b 0
  have hz : (0 : ℂ) • (0 : TangentSpace 𝓘(ℝ, V.analyticModel) x [⋀^Fin n]→L[ℝ] ℂ) = 0 := by
    ext v
    change (0 : ℂ) * 0 = 0
    ring
  rw [hz] at h
  simpa only [map_zero, zero_mul] using h

theorem holomorphicLineFrameAdjoint_zero (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) (j : V.analyticSpace)
    (x : ↥(⊤ ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j))
    (hx : x.val ∉ tsupport (FormPartition.holomorphicLineComplexPartition u i)) :
    (HolomorphicMetric.Codifferential.holomorphicLineFrameAdjoint V u i a).val j x = 0 := by
  by_cases hi : x.val ∈ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val
  · rw [HolomorphicMetric.Codifferential.holomorphicLineFrameAdjoint_apply_mem V u i a j x hi,
      HolomorphicMetric.Codifferential.holomorphicLineFrameAdjointForm_zero V u i a ⟨x, hi⟩ hx]
    ext v
    change FormPartition.holomorphicLineFrameCutoff u i x *
      ((CohomologyTransitions.holomorphicCohomologyTransition V.analyticModel V.analyticSpace u i.val j).val
        ⟨x, hi, x.property.2⟩ * 0) = 0
    ring
  · exact SupportedForms.holomorphicLineSupportedExtension_apply_zero u _ 0
      (FormPartition.holomorphicLineFrameCutoff u i) (FormPartition.holomorphicLineFrameCutoff_smooth u i)
      (FormPartition.holomorphicLineFrameCutoff_support u i) _ j x
      (fun h => hi (FormPartition.holomorphicLineFrameCutoff_support u i h))

theorem holomorphicLineFrameAdjointPair_left (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) (x : V.analyticSpace) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 1 (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension u i 1 b).val
      (Projective.ScalarDolbeaultAdjoint.projectiveScalarDolbeaultZero V (HolomorphicFrame.Tests.holomorphicLineFrameTest V u i a)).val x =
        FormPartition.holomorphicLineComplexPartition u i x *
          FormIntegralPair.holomorphicLineGlobalFormPair V u 1 b (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a) x := by
  by_cases hx : x ∈ tsupport (FormPartition.holomorphicLineComplexPartition u i)
  · have hi := FormPartition.holomorphicLineComplexPartition_support u i hx
    rw [Projective.CovectorPair.projectiveFormPointPair_eq_tangentPair,
      HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension_apply u i 1 b ⟨x, hi⟩,
      HolomorphicFrame.Tests.holomorphicLineFrameTest_dbar V u i a ⟨x, hi⟩ hx,
      Projective.CovectorPair.projectiveTangentCovectorPair_smul_left, FormIntegralPair.holomorphicLineGlobalFormPair_apply,
      HolomorphicLine.FormPair.holomorphicLineSmoothFormPair_inFrame V u 1 b (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a) i.val ⟨x, trivial⟩ hi]
    simp only [map_mul, FormPartition.holomorphicLineComplexPartition, Complex.conj_ofReal]
    ring
  · have hb := HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension_zero u i 1 b x hx
    rw [Analysis.HodgeTheory.Decomposition.LocalMetric.Constructions.projectiveFormPointPair_congr_at V 1
      (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension u i 1 b).val
      (Projective.ScalarDolbeaultAdjoint.projectiveScalarDolbeaultZero V (HolomorphicFrame.Tests.holomorphicLineFrameTest V u i a)).val 0
      (Projective.ScalarDolbeaultAdjoint.projectiveScalarDolbeaultZero V (HolomorphicFrame.Tests.holomorphicLineFrameTest V u i a)).val x hb rfl,
      Analysis.HodgeTheory.Decomposition.LocalMetric.Constructions.projectiveFormPointPair_zero_left, image_eq_zero_of_notMem_tsupport hx, zero_mul]

end

/-! The metric inverse and genuine frame cutoff identify the scalar and bundle adjoint pairings. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff ComplexConjugate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal
local instance adjointRightPair_realDimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    FiniteDimensional ℝ V.analyticModel := FiniteDimensional.trans ℝ ℂ V.analyticModel

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)

theorem holomorphicLineFrameAdjoint_globalPair_zero (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) (x : V.analyticSpace)
    (hx : x ∉ tsupport (FormPartition.holomorphicLineComplexPartition u i)) :
    FormIntegralPair.holomorphicLineGlobalFormPair V u 0 (HolomorphicMetric.Codifferential.holomorphicLineFrameAdjoint V u i b) a x = 0 := by
  rw [FormIntegralPair.holomorphicLineGlobalFormPair_apply]
  dsimp only [HolomorphicLine.FormPair.holomorphicLineSmoothFormPair]
  rw [holomorphicLineFrameAdjoint_zero V u i b x _ hx, projectiveTangentCovectorPair_zero_left, mul_zero]

theorem holomorphicLineFrameAdjointPair_right (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) (x : V.analyticSpace) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 0
      (Projective.ScalarDolbeaultAdjoint.projectiveScalarDolbeaultAdjoint V (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension u i 1 b)).val
      (HolomorphicFrame.Tests.holomorphicLineFrameTest V u i a).val x =
        FormIntegralPair.holomorphicLineGlobalFormPair V u 0 (HolomorphicMetric.Codifferential.holomorphicLineFrameAdjoint V u i b) a x := by
  by_cases hx : x ∈ tsupport (FormPartition.holomorphicLineComplexPartition u i)
  · have hi := FormPartition.holomorphicLineComplexPartition_support u i hx
    rw [Projective.CovectorPair.projectiveFormPointPair_eq_tangentPair,
      HolomorphicFrame.Tests.holomorphicLineFrameTest_on_partition_support V u i a ⟨x, hi⟩ hx,
      FormIntegralPair.holomorphicLineGlobalFormPair_apply,
      HolomorphicLine.FormPair.holomorphicLineSmoothFormPair_inFrame V u 0 (HolomorphicMetric.Codifferential.holomorphicLineFrameAdjoint V u i b) a i.val ⟨x, trivial⟩ hi,
      HolomorphicMetric.Codifferential.holomorphicLineFrameAdjoint_inFrame V u i b ⟨x, hi⟩,
      HolomorphicMetric.Codifferential.holomorphicLineFrameAdjointForm_apply, Projective.CovectorPair.projectiveTangentCovectorPair_smul_left]
    simp only [map_inv₀, Complex.conj_ofReal]
    rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (HolomorphicLine.MetricWeight.holomorphicLineMetricWeight_pos u i.val ⟨x, hi⟩))), one_mul]
  · have hb := Projective.ScalarDolbeaultAdjoint.projectiveScalarDolbeaultAdjoint_zero_off_closed V
      (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension u i 1 b) (isClosed_tsupport _)
      (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension_zero u i 1 b) hx
    rw [Analysis.HodgeTheory.Decomposition.LocalMetric.Constructions.projectiveFormPointPair_congr_at V 0
      (Projective.ScalarDolbeaultAdjoint.projectiveScalarDolbeaultAdjoint V (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension u i 1 b)).val
      (HolomorphicFrame.Tests.holomorphicLineFrameTest V u i a).val 0 (HolomorphicFrame.Tests.holomorphicLineFrameTest V u i a).val x hb rfl,
      Analysis.HodgeTheory.Decomposition.LocalMetric.Constructions.projectiveFormPointPair_zero_left, holomorphicLineFrameAdjoint_globalPair_zero V u i a b x hx]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AdjointPointPairs
