import OAI.AlgebraicGeometry.Comparison.Betti.Open.Image

/-! # Disjoint Open Images -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.DisjointOpenImages

noncomputable section

/-! Intersect an actual disjoint open-embedding cover with each open subset. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable {ι : Type} {M : ι → TopCat.{0}} {N : TopCat.{0}}
  (f : ∀ i, M i ⟶ N) (hf : ∀ i, Topology.IsOpenEmbedding (f i))

def openImage (V : Opens N) (i : ι) : Opens N :=
  (hf i).functor.obj ((Opens.map (f i)).obj V)

def openImageInclusion (V : Opens N) (i : ι) : openImage f hf V i ⟶ V :=
  (hf i).isOpenMap.adjunction.counit.app V

theorem openImage_cover (hcover : ∀ y : N, ∃ i, y ∈ Set.range (f i)) (V : Opens N) :
    V ≤ iSup (openImage f hf V) := by
  intro y hy
  obtain ⟨i, x, rfl⟩ := hcover y
  apply (Opens.mem_iSup).mpr
  exact ⟨i, x, hy, rfl⟩

theorem openImage_disjoint
    (hdisj : Pairwise (fun i j => Disjoint (Set.range (f i)) (Set.range (f j)))) (V : Opens N) :
    Pairwise (fun i j => Disjoint (openImage f hf V i) (openImage f hf V j)) := by
  intro i j hij
  apply Opens.coe_disjoint.mp
  exact (hdisj hij).mono (Set.image_subset_range _ _) (Set.image_subset_range _ _)

end

end OAI.AlgebraicGeometry.Comparison.Betti.DisjointOpenImages
