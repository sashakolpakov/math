import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.DolbeaultAdjointDegrees
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Tests
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.Dolbeault

/-! # Degree Tests -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DegreeTests

noncomputable section

/-! Supported scalar frame tests for the genuine bundle Dolbeault differential in every degree. -/

open _root_.TopologicalSpace Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal
local instance degreeTests_realDimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    FiniteDimensional ℝ V.analyticModel := FiniteDimensional.trans ℝ ℂ V.analyticModel

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem supportedExtension_dbarDegree_of_one_near (q : ℕ) (U : Opens V.analyticSpace)
    (f : V.analyticSpace → ℂ) (hf : ContMDiffOn 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f (U : Set V.analyticSpace))
    (hs : tsupport f ⊆ (U : Set V.analyticSpace))
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U q) (x : U) (hx : ∀ᶠ y in 𝓝 x.val, f y = 1) :
    Projective.DolbeaultAdjointDegrees.projectiveScalarDolbeaultDegree V q (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtension f hf hs a) x =
      Open.ManifoldDolbeault.openManifoldDolbeaultD 0 q q a x := by
  rw [Projective.DolbeaultAdjointDegrees.projectiveScalarDolbeaultDegree_apply, Supported.DolbeaultCutoff.supportedExtension_d_of_one_near V U q f hf hs a x hx]
  change _ = (1 / 2 : ℂ) • (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a x + (-(AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter 0 q)⁻¹) •
    Open.ManifoldAction.openManifoldComplexAction AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹ (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a) x)
  rw [Open.ManifoldAction.openManifoldComplexAction_apply, inv_inv, AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit_coe]

variable (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) (q : ℕ)

theorem holomorphicLineFrameCoordinates_dbarDegree (i : V.analyticSpace) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ q) :
    HolomorphicFrame.Tests.holomorphicLineFrameCoordinates V u i (q + 1) (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ q a).val =
      Open.ManifoldDolbeault.openManifoldDolbeaultD 0 q q (HolomorphicFrame.Tests.holomorphicLineFrameCoordinates V u i q a.val) := by
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (le_inf le_rfl le_rfl)
    (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (inf_le_inf_right (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) le_top)
    (Open.ManifoldDolbeault.openManifoldDolbeaultD 0 q q (a.val.val i))) =
      Open.ManifoldDolbeault.openManifoldDolbeaultD 0 q q (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (le_inf le_rfl le_rfl)
        (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (inf_le_inf_right (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) le_top) (a.val.val i)))
  rw [Open.ManifoldDolbeault.openManifoldDolbeaultD_restrict, Open.ManifoldDolbeault.openManifoldDolbeaultD_restrict]

def holomorphicLineDegreeFrameTest (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u) :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ q →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace q :=
  (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtension (FormPartition.holomorphicLineFrameCutoff u i)
    (FormPartition.holomorphicLineFrameCutoff_smooth u i).contMDiffOn (FormPartition.holomorphicLineFrameCutoff_support u i)).comp
      (HolomorphicFrame.Tests.holomorphicLineFrameCoordinates V u i.val q)

theorem holomorphicLineDegreeFrameTest_apply (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ q)
    (x : CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val) :
    holomorphicLineDegreeFrameTest V u q i a x =
      FormPartition.holomorphicLineFrameCutoff u i x • a.val i.val ⟨x, trivial, x.property⟩ := by
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtension (FormPartition.holomorphicLineFrameCutoff u i)
    (FormPartition.holomorphicLineFrameCutoff_smooth u i).contMDiffOn (FormPartition.holomorphicLineFrameCutoff_support u i)
    (HolomorphicFrame.Tests.holomorphicLineFrameCoordinates V u i.val q a) x = _
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtension_apply_mem, HolomorphicFrame.Tests.holomorphicLineFrameCoordinates_apply]

theorem holomorphicLineDegreeFrameTest_on_partition_support (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ q)
    (x : CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val)
    (hx : x.val ∈ tsupport (FormPartition.holomorphicLineComplexPartition u i)) :
    holomorphicLineDegreeFrameTest V u q i a x = a.val i.val ⟨x, trivial, x.property⟩ := by
  rw [holomorphicLineDegreeFrameTest_apply, FormPartition.holomorphicLineFrameCutoff_one u i x.val hx, one_smul]

theorem holomorphicLineDegreeFrameTest_dbar (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ q)
    (x : CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val)
    (hx : x.val ∈ tsupport (FormPartition.holomorphicLineComplexPartition u i)) :
    Projective.DolbeaultAdjointDegrees.projectiveScalarDolbeaultDegree V q (holomorphicLineDegreeFrameTest V u q i a.val) x =
      (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ q a).val.val i.val ⟨x, trivial, x.property⟩ := by
  have h := supportedExtension_dbarDegree_of_one_near V q _ (FormPartition.holomorphicLineFrameCutoff u i)
    (FormPartition.holomorphicLineFrameCutoff_smooth u i).contMDiffOn (FormPartition.holomorphicLineFrameCutoff_support u i)
    (HolomorphicFrame.Tests.holomorphicLineFrameCoordinates V u i.val q a.val) x
    ((FormPartition.holomorphicLineFrameCutoff_one_near u i).filter_mono (nhds_le_nhdsSet hx))
  rw [← holomorphicLineFrameCoordinates_dbarDegree, HolomorphicFrame.Tests.holomorphicLineFrameCoordinates_apply] at h
  exact h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DegreeTests
