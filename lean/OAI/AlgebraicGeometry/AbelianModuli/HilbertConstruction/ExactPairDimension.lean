import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ShortComplexDimensionBalance

/-! # Exact Pair Dimension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExactPairDimension

noncomputable section

/-! Dimension balance for two consecutive exact linear maps. -/
universe u

theorem exact_pair_dimension {K : Type u} [Field K]
    {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C] [Module.Finite K B]
    (f : A →ₗ[K] B) (g : B →ₗ[K] C) (h : Function.Exact f g) :
    Module.finrank K B = Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.range g) := by
  have hk : LinearMap.range f = LinearMap.ker g := (LinearMap.exact_iff.mp h).symm
  have hh := congrArg (fun P : Submodule K B => Module.finrank K P) hk
  have hd := g.finrank_range_add_finrank_ker
  omega

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExactPairDimension
