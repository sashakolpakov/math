import OAI.AlgebraicGeometry.CycleClass.Thom.Open.EmbeddingComplexChart

/-! # Inverse Chart Change -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Local.InverseChartChange.Constructions

noncomputable section

/-! Local analytic inverses transport to the complex chart defined by an actual open embedding. -/

open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.EmbeddingComplexChart.Constructions

variable {M N E G : Type} [TopologicalSpace M] [TopologicalSpace N] [Nonempty M]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E M]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]

theorem localInverse_in_embedding_chart (d : ℕ) (j : M → (Fin d → ℂ))
    (hj : Topology.IsOpenEmbedding j) (g : M → N) (x : M)
    (hjold : IsLocalDiffeomorphAt 𝓘(ℂ, E) 𝓘(ℂ, Fin d → ℂ) ω j x)
    (hg : IsLocalDiffeomorphAt 𝓘(ℂ, E) 𝓘(ℂ, G) ω g x) :
    letI := Open.EmbeddingComplexChart.Constructions.embeddingChartedSpace d j hj
    IsLocalDiffeomorphAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, G) ω g x := by
  let := Open.EmbeddingComplexChart.Constructions.embeddingChartedSpace d j hj
  obtain ⟨q, hxq, hq⟩ := hg
  let a := Open.EmbeddingComplexChart.Constructions.embeddingPartialDiffeomorph d j hj
  let b := hjold.localInverse
  let l := (a.trans b).trans q
  have hi : b (j x) = x := hjold.localInverse_left_inv hjold.localInverse_mem_target
  refine ⟨l, ?_, ?_⟩
  · change (x ∈ a.source ∧ j x ∈ b.source) ∧ b (j x) ∈ q.source
    exact ⟨⟨Open.EmbeddingComplexChart.Constructions.embeddingPartial_source d j hj x, hjold.localInverse_mem_source⟩, hi.symm ▸ hxq⟩
  · intro z hz
    change (z ∈ a.source ∧ j z ∈ b.source) ∧ b (j z) ∈ q.source at hz
    have he : b (j z) = z := hj.injective (hjold.localInverse_right_inv hz.1.2)
    change g z = q (b (j z))
    have h := hq hz.2
    rw [he] at h ⊢
    exact h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Local.InverseChartChange.Constructions
