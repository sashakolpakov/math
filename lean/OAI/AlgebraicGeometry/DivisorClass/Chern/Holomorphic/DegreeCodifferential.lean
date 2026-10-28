import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.DolbeaultAdjointDegrees
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FormPartition
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.FrameForms

/-! # Degree Codifferential -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DegreeCodifferential

noncomputable section

/-! An actual smooth bundle operator assembled from supported scalar adjoints.
The bundle integration-by-parts identity is proved separately. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal
local instance degreeCodifferential_realDimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    FiniteDimensional ℝ V.analyticModel := FiniteDimensional.trans ℝ ℂ V.analyticModel

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) (q : ℕ)

def holomorphicLineDegreeFrameAdjointForm (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u) :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (q + 1) →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel
        (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val) q :=
  (HolomorphicMetric.FrameForms.holomorphicLineInverseMetricFormMul u i.val q).comp
    ((Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val)).comp
      ((Projective.DolbeaultAdjointDegrees.projectiveScalarDolbeaultDegreeAdjoint V q).comp (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension u i (q + 1))))

theorem holomorphicLineDegreeFrameAdjointForm_apply (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (q + 1))
    (x : CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val) :
    holomorphicLineDegreeFrameAdjointForm V u q i a x =
      (HolomorphicLine.MetricWeight.holomorphicLineMetricWeight u i.val x : ℂ)⁻¹ •
        Projective.DolbeaultAdjointDegrees.projectiveScalarDolbeaultDegreeAdjoint V q (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension u i (q + 1) a) x :=
  HolomorphicMetric.FrameForms.holomorphicLineInverseMetricFormMul_apply u i.val q _ x

theorem holomorphicLineDegreeFrameAdjointForm_zero (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (q + 1))
    (x : CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val)
    (hx : x.val ∉ tsupport (FormPartition.holomorphicLineComplexPartition u i)) :
    holomorphicLineDegreeFrameAdjointForm V u q i a x = 0 := by
  rw [holomorphicLineDegreeFrameAdjointForm_apply,
    Projective.DolbeaultAdjointDegrees.projectiveScalarDolbeaultDegreeAdjoint_zero_off_closed V q (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension u i (q + 1) a)
      (isClosed_tsupport _) (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension_zero u i (q + 1) a) hx]
  exact smul_zero (A := TangentSpace 𝓘(ℝ, V.analyticModel) x.val [⋀^Fin q]→L[ℝ] ℂ)
    ((HolomorphicLine.MetricWeight.holomorphicLineMetricWeight u i.val x : ℂ)⁻¹)

def holomorphicLineDegreeFrameAdjoint (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u) :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (q + 1) →ₗ[ℂ] HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ q :=
  (SupportedForms.holomorphicLineSupportedExtension u
    (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val) q
    (FormPartition.holomorphicLineFrameCutoff u i) (FormPartition.holomorphicLineFrameCutoff_smooth u i)
    (FormPartition.holomorphicLineFrameCutoff_support u i)).comp
      ((HolomorphicSmooth.Frames.holomorphicLineSmoothFrameEquiv u i.val le_rfl q).symm.toLinearMap.comp
        (holomorphicLineDegreeFrameAdjointForm V u q i))

theorem holomorphicLineDegreeFrameAdjoint_apply_mem (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (q + 1)) (j : V.analyticSpace)
    (x : ↥(⊤ ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j))
    (hx : x.val ∈ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val) :
    (holomorphicLineDegreeFrameAdjoint V u q i a).val j x =
      FormPartition.holomorphicLineFrameCutoff u i x •
        ((CohomologyTransitions.holomorphicCohomologyTransition V.analyticModel V.analyticSpace u i.val j).val
          ⟨x, hx, x.property.2⟩ • holomorphicLineDegreeFrameAdjointForm V u q i a ⟨x, hx⟩) := by
  change (SupportedForms.holomorphicLineSupportedExtension u _ q (FormPartition.holomorphicLineFrameCutoff u i)
    (FormPartition.holomorphicLineFrameCutoff_smooth u i) (FormPartition.holomorphicLineFrameCutoff_support u i)
    (HolomorphicSmooth.Frames.holomorphicLineSmoothFormOfFrame u i.val le_rfl q (holomorphicLineDegreeFrameAdjointForm V u q i a))).val j x = _
  rw [SupportedForms.holomorphicLineSupportedExtension_apply_mem u _ q _ _ _ _ j x hx,
    HolomorphicSmooth.Frames.holomorphicLineSmoothFormOfFrame_apply]

theorem holomorphicLineDegreeFrameAdjoint_inFrame (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (q + 1))
    (x : CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val) :
    (holomorphicLineDegreeFrameAdjoint V u q i a).val i.val ⟨x, trivial, x.property⟩ =
      holomorphicLineDegreeFrameAdjointForm V u q i a x := by
  rw [holomorphicLineDegreeFrameAdjoint_apply_mem V u q i a i.val _ x.property,
    CohomologyTransitions.holomorphicCohomologyTransition_self V.analyticModel V.analyticSpace u i.val x.val x.property, one_smul]
  by_cases hx : x.val ∈ tsupport (FormPartition.holomorphicLineComplexPartition u i)
  · rw [FormPartition.holomorphicLineFrameCutoff_one u i x.val hx, one_smul]
  · rw [holomorphicLineDegreeFrameAdjointForm_zero V u q i a x hx]
    exact smul_zero (A := TangentSpace 𝓘(ℝ, V.analyticModel) x.val [⋀^Fin q]→L[ℝ] ℂ)
      (FormPartition.holomorphicLineFrameCutoff u i x)

def holomorphicLineDegreeCodifferential :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (q + 1) →ₗ[ℂ] HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ q :=
  ∑ i, holomorphicLineDegreeFrameAdjoint V u q i

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DegreeCodifferential
