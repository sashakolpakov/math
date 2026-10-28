import OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter

/-! # Source Neighborhood -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.SourceNeighborhood.Constructions

noncomputable section

/-! Normal neighborhoods may be shrunk inside an actual source open,
using the original embedding and retaining the ambient coordinate map. -/

open _root_.TopologicalSpace OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter

variable {M N E F : Type} [TopologicalSpace M] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)

theorem exists_subpair_source_subset (hf : Topology.IsEmbedding f)
    (O : Opens M) (hx : x ∈ O) :
    ∃ Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x,
      Q.ambientChart = P.ambientChart ∧ f ⁻¹' Q.neighborhood ⊆ O := by
  obtain ⟨U, hU, hpre⟩ := hf.isInducing.isOpen_iff.mp O.isOpen
  have hxU : f x ∈ U := by
    change x ∈ f ⁻¹' U
    rwa [hpre]
  obtain ⟨Q, hQ, hQU⟩ := P.exists_subpair U (hU.mem_nhds hxU)
  refine ⟨Q, hQ, ?_⟩
  intro y hy
  have hyU : y ∈ f ⁻¹' U := hQU hy
  rwa [hpre] at hyU

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.SourceNeighborhood.Constructions
