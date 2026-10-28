import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.DolbeaultCutoff
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.DolbeaultZero

/-! # Tests -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Tests

noncomputable section

/-! Actual compact frame tests and their exact agreement with the bundle Dolbeault derivative. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal
local instance frameTests_realDimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    FiniteDimensional ℝ V.analyticModel := FiniteDimensional.trans ℝ ℂ V.analyticModel

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)

def holomorphicLineFrameCoordinates (i : V.analyticSpace) (n : ℕ) :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) n :=
  (HolomorphicSmooth.Frames.holomorphicLineSmoothFrameEquiv u i le_rfl n).toLinearMap.comp (HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict le_top)

theorem holomorphicLineFrameCoordinates_apply (i : V.analyticSpace) (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) :
    holomorphicLineFrameCoordinates V u i n a x = a.val i ⟨x, trivial, x.property⟩ := rfl

theorem holomorphicLineFrameCoordinates_dbar (i : V.analyticSpace) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    holomorphicLineFrameCoordinates V u i 1 (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a) =
      Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 (holomorphicLineFrameCoordinates V u i 0 a) := by
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (le_inf le_rfl le_rfl)
    (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (inf_le_inf_right (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) le_top)
    (Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 (a.val i))) =
      Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (le_inf le_rfl le_rfl)
        (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (inf_le_inf_right (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) le_top) (a.val i)))
  rw [Open.ManifoldDolbeault.openManifoldDolbeaultD_restrict, Open.ManifoldDolbeault.openManifoldDolbeaultD_restrict]

def holomorphicLineFrameTest (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u) :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0 →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0 :=
  (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtension (Holomorphic.FormPartition.holomorphicLineFrameCutoff u i)
    (Holomorphic.FormPartition.holomorphicLineFrameCutoff_smooth u i).contMDiffOn (Holomorphic.FormPartition.holomorphicLineFrameCutoff_support u i)).comp
      (holomorphicLineFrameCoordinates V u i.val 0)

theorem holomorphicLineFrameTest_apply (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0)
    (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val) :
    holomorphicLineFrameTest V u i a x =
      Holomorphic.FormPartition.holomorphicLineFrameCutoff u i x • a.val i.val ⟨x, trivial, x.property⟩ := by
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtension (Holomorphic.FormPartition.holomorphicLineFrameCutoff u i)
    (Holomorphic.FormPartition.holomorphicLineFrameCutoff_smooth u i).contMDiffOn (Holomorphic.FormPartition.holomorphicLineFrameCutoff_support u i)
    (holomorphicLineFrameCoordinates V u i.val 0 a) x = _
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtension_apply_mem, holomorphicLineFrameCoordinates_apply]

theorem holomorphicLineFrameTest_on_partition_support (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0)
    (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val)
    (hx : x.val ∈ tsupport (Holomorphic.FormPartition.holomorphicLineComplexPartition u i)) :
    holomorphicLineFrameTest V u i a x = a.val i.val ⟨x, trivial, x.property⟩ := by
  rw [holomorphicLineFrameTest_apply, Holomorphic.FormPartition.holomorphicLineFrameCutoff_one u i x.val hx, one_smul]

theorem holomorphicLineFrameTest_dbar (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0)
    (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val)
    (hx : x.val ∈ tsupport (Holomorphic.FormPartition.holomorphicLineComplexPartition u i)) :
    Projective.ScalarDolbeaultAdjoint.projectiveScalarDolbeaultZero V (holomorphicLineFrameTest V u i a) x =
      (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a).val i.val ⟨x, trivial, x.property⟩ := by
  have h := Supported.DolbeaultCutoff.holomorphicLineFrameCutoff_dbar V u i (holomorphicLineFrameCoordinates V u i.val 0 a) x hx
  rw [← holomorphicLineFrameCoordinates_dbar, holomorphicLineFrameCoordinates_apply] at h
  exact h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Tests
