import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ScalarDolbeaultAdjoint
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FormPartition
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.FrameForms

/-! # Codifferential -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Codifferential

noncomputable section

/-! An actual smooth bundle operator assembled from supported scalar adjoints.
The bundle integration-by-parts identity is proved separately. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal
local instance metricCodifferential_realDimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    FiniteDimensional ℝ V.analyticModel := FiniteDimensional.trans ℝ ℂ V.analyticModel

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)

def holomorphicLineFrameAdjointForm (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u) :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1 →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel
        (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val) 0 :=
  (FrameForms.holomorphicLineInverseMetricFormMul u i.val 0).comp
    ((Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val)).comp
      ((Projective.ScalarDolbeaultAdjoint.projectiveScalarDolbeaultAdjoint V).comp (FrameForms.holomorphicLineWeightedFrameExtension u i 1)))

theorem holomorphicLineFrameAdjointForm_apply (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1)
    (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val) :
    holomorphicLineFrameAdjointForm V u i a x =
      (HolomorphicLine.MetricWeight.holomorphicLineMetricWeight u i.val x : ℂ)⁻¹ •
        Projective.ScalarDolbeaultAdjoint.projectiveScalarDolbeaultAdjoint V (FrameForms.holomorphicLineWeightedFrameExtension u i 1 a) x :=
  FrameForms.holomorphicLineInverseMetricFormMul_apply u i.val 0 _ x

theorem holomorphicLineFrameAdjointForm_zero (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1)
    (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val)
    (hx : x.val ∉ tsupport (Holomorphic.FormPartition.holomorphicLineComplexPartition u i)) :
    holomorphicLineFrameAdjointForm V u i a x = 0 := by
  rw [holomorphicLineFrameAdjointForm_apply,
    Projective.ScalarDolbeaultAdjoint.projectiveScalarDolbeaultAdjoint_zero_off_closed V (FrameForms.holomorphicLineWeightedFrameExtension u i 1 a)
      (isClosed_tsupport _) (FrameForms.holomorphicLineWeightedFrameExtension_zero u i 1 a) hx]
  exact smul_zero (A := TangentSpace 𝓘(ℝ, V.analyticModel) x.val [⋀^Fin 0]→L[ℝ] ℂ)
    ((HolomorphicLine.MetricWeight.holomorphicLineMetricWeight u i.val x : ℂ)⁻¹)

def holomorphicLineFrameAdjoint (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u) :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1 →ₗ[ℂ] HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0 :=
  (Holomorphic.SupportedForms.holomorphicLineSupportedExtension u
    (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val) 0
    (Holomorphic.FormPartition.holomorphicLineFrameCutoff u i) (Holomorphic.FormPartition.holomorphicLineFrameCutoff_smooth u i)
    (Holomorphic.FormPartition.holomorphicLineFrameCutoff_support u i)).comp
      ((HolomorphicSmooth.Frames.holomorphicLineSmoothFrameEquiv u i.val le_rfl 0).symm.toLinearMap.comp
        (holomorphicLineFrameAdjointForm V u i))

theorem holomorphicLineFrameAdjoint_apply_mem (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) (j : V.analyticSpace)
    (x : ↥(⊤ ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j))
    (hx : x.val ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val) :
    (holomorphicLineFrameAdjoint V u i a).val j x =
      Holomorphic.FormPartition.holomorphicLineFrameCutoff u i x •
        ((Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition V.analyticModel V.analyticSpace u i.val j).val
          ⟨x, hx, x.property.2⟩ • holomorphicLineFrameAdjointForm V u i a ⟨x, hx⟩) := by
  change (Holomorphic.SupportedForms.holomorphicLineSupportedExtension u _ 0 (Holomorphic.FormPartition.holomorphicLineFrameCutoff u i)
    (Holomorphic.FormPartition.holomorphicLineFrameCutoff_smooth u i) (Holomorphic.FormPartition.holomorphicLineFrameCutoff_support u i)
    (HolomorphicSmooth.Frames.holomorphicLineSmoothFormOfFrame u i.val le_rfl 0 (holomorphicLineFrameAdjointForm V u i a))).val j x = _
  rw [Holomorphic.SupportedForms.holomorphicLineSupportedExtension_apply_mem u _ 0 _ _ _ _ j x hx,
    HolomorphicSmooth.Frames.holomorphicLineSmoothFormOfFrame_apply]

theorem holomorphicLineFrameAdjoint_inFrame (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1)
    (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val) :
    (holomorphicLineFrameAdjoint V u i a).val i.val ⟨x, trivial, x.property⟩ =
      holomorphicLineFrameAdjointForm V u i a x := by
  rw [holomorphicLineFrameAdjoint_apply_mem V u i a i.val _ x.property,
    Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition_self V.analyticModel V.analyticSpace u i.val x.val x.property, one_smul]
  by_cases hx : x.val ∈ tsupport (Holomorphic.FormPartition.holomorphicLineComplexPartition u i)
  · rw [Holomorphic.FormPartition.holomorphicLineFrameCutoff_one u i x.val hx, one_smul]
  · rw [holomorphicLineFrameAdjointForm_zero V u i a x hx]
    exact smul_zero (A := TangentSpace 𝓘(ℝ, V.analyticModel) x.val [⋀^Fin 0]→L[ℝ] ℂ)
      (Holomorphic.FormPartition.holomorphicLineFrameCutoff u i x)

def holomorphicLineMetricCodifferential :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1 →ₗ[ℂ] HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0 :=
  ∑ i, holomorphicLineFrameAdjoint V u i

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Codifferential
