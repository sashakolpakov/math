import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence

/-! # Nested Cutoff Neighborhood -/

namespace OAI.Analysis.HodgeTheory.Decomposition.NestedCutoffNeighborhood.Constructions

noncomputable section

/-! A compact set has a smooth outer cutoff and an open intermediate
neighborhood on which that cutoff is locally identically one. -/

open Set Filter
open scoped SchwartzMap _root_.Topology
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence.CM.Construction

theorem exists_nested_schwartz_cutoff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ψ : 𝓢(E, ℂ), HasCompactSupport ψ ∧ tsupport ψ ⊆ U ∧
      (∀ x, ψ x = Complex.ofReal (ψ x).re) ∧
      ∃ T : Set E, IsOpen T ∧ K ⊆ T ∧ T ⊆ U ∧
        ∀ x ∈ T, (ψ : E → ℂ) =ᶠ[𝓝 x] 1 := by
  obtain ⟨ψ, hψc, hψU, hψreal, hψnear⟩ := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence.CM.Construction.exists_real_schwartz_cutoff_near_compact hK hU hKU
  let T := U ∩ interior {x | ψ x = 1}
  have hT : IsOpen T := hU.inter isOpen_interior
  refine ⟨ψ, hψc, hψU, hψreal, T, hT, ?_, inter_subset_left, ?_⟩
  · intro x hx
    refine ⟨hKU hx, mem_interior_iff_mem_nhds.mpr ?_⟩
    exact hψnear x hx
  · intro x hx
    filter_upwards [isOpen_interior.mem_nhds hx.2] with y hy
    change ψ y = 1
    exact interior_subset (s := {x : E | ψ x = 1}) hy

end

end OAI.Analysis.HodgeTheory.Decomposition.NestedCutoffNeighborhood.Constructions
