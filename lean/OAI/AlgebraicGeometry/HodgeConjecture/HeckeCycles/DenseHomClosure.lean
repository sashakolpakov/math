import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveAwayProjection

/-! # Dense Hom Closure -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DenseHomClosure.CM

/-! Transport a dense rational parametrization into the closure of its
actual homomorphic image. -/

theorem mem {X A G : Type*} [Group X] [Group G] [TopologicalSpace A]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (r : X → A) (hr : DenseRange r) (f : A → G) (hf : Continuous f) (s : X →* G)
    (hs : ∀ x, f (r x) = s x) (a : A) (g : G) (hg : f a = g) : g ∈ s.range.topologicalClosure := by
  have h := CMExtraction.ActiveAwayProjection.Approximation.dense_diagonal_image_mem_closure r hr f hf a
  have he : (fun x => f (r x)) = s := funext hs
  rw [he, hg] at h
  exact h

theorem hom_image {X A G : Type*} [Group X] [Group A] [Group G] [TopologicalSpace A]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (r : X →* A) (hr : DenseRange r) (f : A →* G) (hf : Continuous f) (s : X →* G)
    (hs : f.comp r = s) (a : A) : f a ∈ s.range.topologicalClosure :=
  mem r hr f hf s (fun x => DFunLike.congr_fun hs x) a (f a) rfl

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DenseHomClosure.CM
