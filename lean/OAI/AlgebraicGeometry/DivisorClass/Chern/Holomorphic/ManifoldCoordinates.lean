import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OpenExtension
import OAI.Analysis.DifferentialForms.Manifold.LocallyConstant
import OAI.Analysis.DifferentialForms.Manifold.ComplexCharts

/-! # Manifold Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ManifoldCoordinates

noncomputable section

/-! Holomorphicity on an actual manifold open is tested in its actual chart domains. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem contMDiffOn_complex_iff_chartCoordinates (U : Opens M) (f : M → ℂ) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ) ∞ f (U : Set M) ↔
      ∀ e ∈ atlas E M, ContDiffOn ℂ ∞ (f ∘ e.symm) (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U : Set E) := by
  constructor
  · intro hf e he y hy
    have hF := hf.contMDiffAt (U.isOpen.mem_nhds hy.2)
    have he' : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ e.symm y :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hy.1
    exact (hF.comp y he').contDiffAt.contDiffWithinAt
  · intro hf x hx
    let e := chartAt E x
    have he : e ∈ atlas E M := chart_mem_atlas E x
    have hex : x ∈ e.source := mem_chart_source E x
    have hy : e x ∈ Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U := Analysis.DifferentialForms.Manifold.ChartEquiv.mem_chartImageOpen e U hex hx
    have hF : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ) ∞ (f ∘ e.symm) (e x) :=
      ((hf e he).contDiffAt ((Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds hy)).contMDiffAt
    have he' : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ e x :=
      contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hex
    apply ContMDiffAt.contMDiffWithinAt
    apply (hF.comp x he').congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hex] with z hz
    change f z = f (e.symm (e z))
    rw [e.left_inv hz]

theorem holomorphicOpenExtend_chart_contDiff {U : Opens M}
    (g : Exponential.HolomorphicFunction (E := E) (M := U))
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) :
    ContDiffOn ℂ ∞ (OpenExtension.holomorphicOpenExtend g ∘ e.symm) (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U : Set E) :=
  (contMDiffOn_complex_iff_chartCoordinates U (OpenExtension.holomorphicOpenExtend g)).mp
    (OpenExtension.holomorphicOpenExtend_contMDiffOn g) e he

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ManifoldCoordinates
