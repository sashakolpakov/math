import OAI.AlgebraicGeometry.CycleClass.Thom.SingleChartComplexManifold

/-! # Embedding Complex Chart -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.EmbeddingComplexChart.Constructions

noncomputable section

/-! An actual open embedding into complex affine space gives a local analytic coordinate map. -/

open scoped _root_.Manifold ContDiff

variable (d : ℕ) {M : Type} [TopologicalSpace M] [Nonempty M]
  (j : M → (Fin d → ℂ)) (hj : Topology.IsOpenEmbedding j)

@[instance_reducible]
def embeddingChartedSpace : ChartedSpace (Fin d → ℂ) M := hj.singletonChartedSpace

theorem embeddingManifold :
    letI := embeddingChartedSpace d j hj
    IsManifold 𝓘(ℂ, Fin d → ℂ) ω M := hj.isManifold_singleton

def embeddingPartialDiffeomorph :
    letI := embeddingChartedSpace d j hj
    PartialDiffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) M (Fin d → ℂ) ω := by
  letI := embeddingChartedSpace d j hj
  refine { __ := hj.toOpenPartialHomeomorph j
           contMDiffOn_toFun := (contMDiff_isOpenEmbedding hj).contMDiffOn
           contMDiffOn_invFun := ?_ }
  rw [hj.toOpenPartialHomeomorph_target]
  exact contMDiffOn_isOpenEmbedding_symm (I := 𝓘(ℂ, Fin d → ℂ)) (n := ω) hj

theorem embeddingPartial_source (x : M) :
    x ∈ (embeddingPartialDiffeomorph d j hj).source := by
  change x ∈ (hj.toOpenPartialHomeomorph j).source
  rw [hj.toOpenPartialHomeomorph_source]
  trivial

theorem embedding_localDiffeomorph :
    letI := embeddingChartedSpace d j hj
    IsLocalDiffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω j := by
  let := embeddingChartedSpace d j hj
  intro x
  exact ⟨embeddingPartialDiffeomorph d j hj, embeddingPartial_source d j hj x, fun _ _ => rfl⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.EmbeddingComplexChart.Constructions
