import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.SourceNeighborhood
import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalChartPurity

/-! # Common Neighborhood -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.CommonNeighborhood.Constructions

noncomputable section

/-! A genuine normal pair may be shrunk simultaneously in the source
and ambient spaces while retaining its original holomorphic chart. -/

open _root_.TopologicalSpace
open scoped _root_.Topology

open OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.SourceNeighborhood.Constructions

variable {M N E F : Type} [TopologicalSpace M] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)

theorem exists_subpair_source_ambient (hf : Topology.IsEmbedding f)
    (O : Opens M) (hx : x ∈ O) (U : Opens N) (hxU : f x ∈ U) :
    ∃ Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x, Q.ambientChart = P.ambientChart ∧
      f ⁻¹' Q.neighborhood ⊆ O ∧ Q.neighborhood ⊆ U := by
  obtain ⟨Q, hQ, hQO⟩ := SourceNeighborhood.Constructions.exists_subpair_source_subset P hf O hx
  obtain ⟨R, hR, hRU⟩ := Q.exists_subpair ((U : Set N) ∩ Q.neighborhood)
    (Filter.inter_mem (U.isOpen.mem_nhds hxU) (Q.openNeighborhood.isOpen.mem_nhds Q.point_mem_neighborhood))
  exact ⟨R, hR.trans hQ, fun _ hy => hQO (hRU hy).2, fun _ hy => (hRU hy).1⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.CommonNeighborhood.Constructions
