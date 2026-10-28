import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic

/-! # Complex Charts -/

namespace OAI.Analysis.DifferentialForms.Manifold.ComplexCharts

/-! Holomorphic chart transitions and the proved underlying real smooth manifold. -/

open scoped _root_.Manifold ContDiff
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

/-- Transition maps in the actual complex atlas are complex smooth on overlaps. -/
theorem complexContDiffAt_chart_transition (e f : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) (hf : f ∈ atlas E M) {y : E}
    (hy : y ∈ e.target) (hfy : e.symm y ∈ f.source) :
    ContDiffAt ℂ ∞ (f ∘ e.symm) y := by
  have he' : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ e.symm y :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hy
  have hf' : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ f (e.symm y) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hf) hfy
  exact (hf'.comp y he').contDiffAt

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- Restricting scalars in the genuine holomorphic transitions gives the
underlying real smooth manifold on the same charted space. -/
theorem complexManifold_isRealSmooth : IsManifold 𝓘(ℝ, E) ∞ M := by
  apply isManifold_of_contDiffOn 𝓘(ℝ, E) ∞ M
  intro e f he hf
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, preimage_id, range_id, inter_univ]
  intro y hy
  have h := (complexContDiffAt_chart_transition e f he hf hy.1 hy.2).restrict_scalars ℝ
  exact h.contDiffWithinAt

end OAI.Analysis.DifferentialForms.Manifold.ComplexCharts
