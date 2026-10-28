import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ScalarDolbeaultAdjoint
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FormPartition
import OAI.Analysis.DifferentialForms.Manifold.ManifoldLocallyFiniteSum

/-! # Dolbeault Cutoff -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.DolbeaultCutoff

noncomputable section

/-! Supported scalar tests preserve the actual Dolbeault derivative wherever
the constructed cutoff is identically one on a neighborhood. -/

open _root_.TopologicalSpace Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem projectiveScalarOnePart_apply (c : ℂ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (x : V.analyticSpace) :
    Projective.ScalarDolbeaultAdjoint.projectiveScalarOnePart V c a x = (1 / 2 : ℂ) • (a x + c • (a x).compContinuousLinearMap
      (Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentScalarMap x Complex.I)) := by
  have h := congrArg (fun b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel ⊤ 1 => b ⟨x, trivial⟩)
    (Projective.ScalarDolbeaultAdjoint.projectiveScalarOnePart_onOpen V c ⊤ a)
  rw [Holomorphic.OneFormProjection.openManifoldOnePart_apply] at h
  exact h

theorem supportedExtension_d_of_one_near (U : Opens V.analyticSpace) (n : ℕ)
    (f : V.analyticSpace → ℂ) (hf : ContMDiffOn 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f (U : Set V.analyticSpace))
    (hs : tsupport f ⊆ (U : Set V.analyticSpace))
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U n) (x : U) (hx : ∀ᶠ y in 𝓝 x.val, f y = 1) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtension f hf hs a) x =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a x := by
  change (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtension f hf hs a).val.exteriorDerivative x.val =
    a.extension.exteriorDerivative x.val
  apply Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.exteriorDerivative_congr_eventually
  filter_upwards [hx] with y hy
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtension_apply, hy, one_smul]

theorem supportedExtension_dbar_of_one_near (U : Opens V.analyticSpace)
    (f : V.analyticSpace → ℂ) (hf : ContMDiffOn 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f (U : Set V.analyticSpace))
    (hs : tsupport f ⊆ (U : Set V.analyticSpace))
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U 0) (x : U) (hx : ∀ᶠ y in 𝓝 x.val, f y = 1) :
    Projective.ScalarDolbeaultAdjoint.projectiveScalarDolbeaultZero V (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtension f hf hs a) x =
      Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 a x := by
  change Projective.ScalarDolbeaultAdjoint.projectiveScalarOnePart V Complex.I
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtension f hf hs a)) x = _
  rw [← Manifold.OneFormProjection.openManifoldOnePart_d, projectiveScalarOnePart_apply, Holomorphic.OneFormProjection.openManifoldOnePart_apply,
    supportedExtension_d_of_one_near V U 0 f hf hs a x hx]

local instance dolbeaultCutoff_realDimension : FiniteDimensional ℝ V.analyticModel :=
  FiniteDimensional.trans ℝ ℂ V.analyticModel

variable (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)

theorem holomorphicLineFrameCutoff_dbar (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val) 0)
    (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val)
    (hx : x.val ∈ tsupport (Holomorphic.FormPartition.holomorphicLineComplexPartition u i)) :
    Projective.ScalarDolbeaultAdjoint.projectiveScalarDolbeaultZero V
      (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtension (Holomorphic.FormPartition.holomorphicLineFrameCutoff u i)
        (Holomorphic.FormPartition.holomorphicLineFrameCutoff_smooth u i).contMDiffOn (Holomorphic.FormPartition.holomorphicLineFrameCutoff_support u i) a) x =
      Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 a x :=
  supportedExtension_dbar_of_one_near V _ _ _ _ a x
    ((Holomorphic.FormPartition.holomorphicLineFrameCutoff_one_near u i).filter_mono (nhds_le_nhdsSet hx))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.DolbeaultCutoff
