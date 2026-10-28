import OAI.Analysis.DifferentialForms.Manifold.ComplexCharts
import OAI.Analysis.DifferentialForms.Manifold.ManifoldPullback

/-! # Holomorphic -/

namespace OAI.Analysis.DifferentialForms.Manifold.Holomorphic

/-! Scalar restriction and actual coordinate regularity for complex-smooth manifold maps. -/

open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]

/-- Complex regularity of a manifold map implies real regularity in the same
actual charts, by restriction of scalars. -/
theorem contMDiffAt_real_of_complex {r : ℕ∞ω} {g : M → N} {x : M}
    (hg : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) r g x) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) r g x := by
  obtain ⟨hc, hd⟩ := contMDiffAt_iff.mp hg
  apply contMDiffAt_iff.mpr
  refine ⟨hc, ?_⟩
  have hreal := hd.restrict_scalars ℝ
  simpa only [extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.range_id] using hreal

/-- Global scalar restriction for actual complex-smooth manifold maps. -/
theorem contMDiff_real_of_complex {r : ℕ∞ω} {g : M → N}
    (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) r g) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) r g :=
  fun x => contMDiffAt_real_of_complex (hg x)

variable [IsManifold 𝓘(ℂ, E) ∞ M] [IsManifold 𝓘(ℂ, F) ∞ N]

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] in
/-- A complex-smooth manifold map has complex-smooth coordinate expressions
in any pair of genuine holomorphic charts. -/
theorem complexContDiffAt_manifoldMap_inChart (g : M → N)
    (e : OpenPartialHomeomorph M E) (f : OpenPartialHomeomorph N F)
    (he : e ∈ atlas E M) (hf : f ∈ atlas F N) {y : E}
    (hy : y ∈ e.target) (hfy : g (e.symm y) ∈ f.source)
    (hg : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g (e.symm y)) :
    ContDiffAt ℂ ∞ (f ∘ g ∘ e.symm) y := by
  have he' : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ e.symm y :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hy
  have hf' : ContMDiffAt 𝓘(ℂ, F) 𝓘(ℂ, F) ∞ f (g (e.symm y)) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hf) hfy
  exact (hf'.comp y (hg.comp y he')).contDiffAt

end OAI.Analysis.DifferentialForms.Manifold.Holomorphic
