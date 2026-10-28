import Mathlib.Topology.DenseEmbedding

/-! # Dense Surjective Parameter -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DenseSurjectiveParameter.CM

/-! A surjective change of parameters preserves a dense image. -/

theorem dense {R S T : Type*} [TopologicalSpace T]
    (r : R → T) (hr : DenseRange r) (e : S → R) (he : Function.Surjective e)
    (f : S → T) (hf : ∀ s, f s = r (e s)) : DenseRange f := by
  have hfun : f = r ∘ e := funext hf
  change Dense (Set.range f)
  rw [hfun, he.range_comp]
  exact hr

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DenseSurjectiveParameter.CM
