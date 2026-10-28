import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Analysis.Complex.Basic

/-! # Immersion Smooth Pullback -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ImmersionSmoothPullback.Constructions

noncomputable section

/-! Smoothness can be checked after an actual immersion. -/

open scoped _root_.Manifold ContDiff

theorem immersionAt_of_order_le
    {E F M N : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]
    {f : M → N} {x : M} {m n : ℕ∞ω} (hmn : m ≤ n)
    (hf : Manifold.IsImmersionAt 𝓘(ℂ, E) 𝓘(ℂ, F) n f x) :
    Manifold.IsImmersionAt 𝓘(ℂ, E) 𝓘(ℂ, F) m f x := by
  obtain ⟨C, iC, jC, ⟨D⟩⟩ := hf
  exact ⟨C, iC, jC, ⟨{
    domChart := D.domChart
    codChart := D.codChart
    mem_domChart_source := D.mem_domChart_source
    mem_codChart_source := D.mem_codChart_source
    domChart_mem_maximalAtlas := IsManifold.maximalAtlas_subset_of_le hmn D.domChart_mem_maximalAtlas
    codChart_mem_maximalAtlas := IsManifold.maximalAtlas_subset_of_le hmn D.codChart_mem_maximalAtlas
    source_subset_preimage_source := D.source_subset_preimage_source
    property := D.property }⟩⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ImmersionSmoothPullback.Constructions
