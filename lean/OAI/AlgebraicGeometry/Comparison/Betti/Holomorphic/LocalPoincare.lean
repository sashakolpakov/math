import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.OpenPoincare
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartMaps

/-! # Local Poincare -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.LocalPoincare

noncomputable section

/-! Local holomorphic Poincaré theorem for the actual manifold complex in every degree. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] {n : ℕ}

theorem local_primitive (a : DeRhamComplex.forms E M (n + 1))
    (ha : DeRhamComplex.differential E M (n + 1) a = 0) (x : M) :
    ∃ (W : Opens M), x ∈ W ∧ ∃ b : DeRhamComplex.forms E W n,
      DeRhamComplex.differential E W n b =
        HolomorphicPullback.pullback (Subtype.val : W → M) (contMDiff_subtype_val (I := 𝓘(ℂ, E))) (n + 1) a := by
  let e := chartAt E x
  have he : e ∈ atlas E M := chart_mem_atlas E x
  let V := Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e
  let j := ChartMaps.chartInverse e V
  have hj : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ j :=
    ChartMaps.chartInverse_holomorphic e he V le_rfl
  let α := HolomorphicPullback.pullback j hj (n + 1) a
  have hα : DeRhamComplex.differential E V (n + 1) α = 0 := by
    rw [HolomorphicPullback.pullback_differential, ha, map_zero]
  have hxV : e x ∈ V := e.map_source (mem_chart_source E x)
  obtain ⟨W, hWV, hxW, β, hβ⟩ := OpenPoincare.local_open_primitive α hα ⟨e x, hxV⟩
  let P := Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e W
  let k := ChartMaps.chartForward e W
  have hk : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ k := ChartMaps.chartForward_holomorphic e he W
  refine ⟨P, ⟨mem_chart_source E x, hxW⟩, HolomorphicPullback.pullback k hk n β, ?_⟩
  rw [HolomorphicPullback.pullback_differential, hβ, ← HolomorphicPullback.pullback_comp, ← HolomorphicPullback.pullback_comp]
  have hcomp : j ∘ (Opens.inclusion hWV ∘ k) = (Subtype.val : P → M) :=
    ChartMaps.chartInverse_inclusion_forward e hWV
  congr 2

theorem local_primitive_on (U : Opens M) (a : DeRhamComplex.forms E U (n + 1))
    (ha : DeRhamComplex.differential E U (n + 1) a = 0) (x : U) :
    ∃ (W : Opens M) (hWU : W ≤ U), (x : M) ∈ W ∧ ∃ b : DeRhamComplex.forms E W n,
      DeRhamComplex.differential E W n b =
        HolomorphicPullback.pullback (Opens.inclusion hWU) (contMDiff_inclusion (I := 𝓘(ℂ, E)) hWU) (n + 1) a := by
  let e := chartAt E (x : M)
  have he : e ∈ atlas E M := chart_mem_atlas E (x : M)
  let V := Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U
  let j : V → U := fun y => ⟨e.symm y, y.property.2⟩
  have hj : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ j := by
    rw [← ContMDiff.subtypeVal_comp_iff]
    exact ChartMaps.chartInverse_holomorphic e he V (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen_le_target e U)
  let α := HolomorphicPullback.pullback j hj (n + 1) a
  have hα : DeRhamComplex.differential E V (n + 1) α = 0 := by
    rw [HolomorphicPullback.pullback_differential, ha, map_zero]
  have hxV : e (x : M) ∈ V :=
    Analysis.DifferentialForms.Manifold.ChartEquiv.mem_chartImageOpen e U (mem_chart_source E (x : M)) x.property
  obtain ⟨W, hWV, hxW, β, hβ⟩ := OpenPoincare.local_open_primitive α hα ⟨e (x : M), hxV⟩
  let P := Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e W
  have hPU : P ≤ U := (Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen_mono e hWV).trans (Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimage_image_le e U)
  let k := ChartMaps.chartForward e W
  have hk : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ k := ChartMaps.chartForward_holomorphic e he W
  refine ⟨P, hPU, ⟨mem_chart_source E (x : M), hxW⟩, HolomorphicPullback.pullback k hk n β, ?_⟩
  rw [HolomorphicPullback.pullback_differential, hβ, ← HolomorphicPullback.pullback_comp, ← HolomorphicPullback.pullback_comp]
  have hcomp : j ∘ (Opens.inclusion hWV ∘ k) = Opens.inclusion hPU := by
    funext y
    apply Subtype.ext
    exact e.left_inv y.property.1
  congr 2

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.LocalPoincare
