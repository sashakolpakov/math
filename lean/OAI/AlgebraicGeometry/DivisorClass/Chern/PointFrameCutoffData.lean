import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FormPartition
import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectionChartDerivative

/-! # Point Frame Cutoff Data -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PointFrameCutoffData

noncomputable section

/-! An actual compactly supported smooth cutoff and an actual open neighborhood on which it is one, inside any prescribed original chart and frame. -/

open _root_.TopologicalSpace Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem exists_projective_point_cutoff_open (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (W : Opens V.analyticSpace) (y : V.analyticSpace) (hy : y ∈ W) :
    ∃ f : V.analyticSpace → ℂ, ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f ∧
      tsupport f ⊆ (W : Set V.analyticSpace) ∧ ∃ U : Opens V.analyticSpace,
      y ∈ U ∧ U ≤ W ∧ ∀ x ∈ U, f x = 1 := by
  let : FiniteDimensional ℝ V.analyticModel := FiniteDimensional.trans ℝ ℂ V.analyticModel
  obtain ⟨f, hf, hs, hone⟩ := Holomorphic.FormPartition.exists_smoothComplexCutoff_near_closed (E := V.analyticModel) W {y} isClosed_singleton
    (singleton_subset_iff.mpr hy)
  have hn : {x | f x = 1} ∈ 𝓝 y := by simpa only [nhdsSet_singleton] using! hone
  obtain ⟨T, hT, hTo, hyT⟩ := mem_nhds_iff.mp hn
  refine ⟨f, hf, hs, (⟨T, hTo⟩ : Opens V.analyticSpace) ⊓ W, ⟨hyT, hy⟩, inf_le_right, ?_⟩
  intro x hx
  exact hT hx.1

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PointFrameCutoffData
