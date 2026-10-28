import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Graph Embedding -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Closed.GraphEmbedding.Constructions

/-! Combining a continuous map with an actual closed embedding gives a closed graph embedding. -/

theorem graph_closedEmbedding {X Y N : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace N] [T2Space N] (g : X → N) (hg : Continuous g)
    (e : X → Y) (he : Topology.IsClosedEmbedding e) :
    Topology.IsClosedEmbedding (fun x => (g x, e x)) := by
  have hgraph : Topology.IsClosedEmbedding (fun x : X => (x, g x)) := by
    refine ⟨isEmbedding_graph hg, ?_⟩
    have hr : Set.range (fun x : X => (x, g x)) = {z : X × N | g z.1 = z.2} := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        rfl
      · intro hz
        exact ⟨z.1, Prod.ext rfl hz⟩
    rw [hr]
    exact isClosed_eq (hg.comp continuous_fst) continuous_snd
  exact (Homeomorph.prodComm Y N).isClosedEmbedding.comp
    ((he.prodMap Topology.IsClosedEmbedding.id).comp hgraph)

end OAI.AlgebraicGeometry.CycleClass.Thom.Closed.GraphEmbedding.Constructions
