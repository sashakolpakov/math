import Mathlib.LinearAlgebra.Basis.Basic

/-! # Basis Range Surjectivity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.BasisRangeSurjectivity.LinearAlgebra

/-! A linear map containing a genuine target basis in its range is surjective. -/

variable {R M N I : Type} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N]

theorem surjective_of_basis_range (f : M →ₗ[R] N) (b : Module.Basis I R N)
    (hb : ∀ i, b i ∈ LinearMap.range f) : Function.Surjective f := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← b.span_eq]
  exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hb)

end OAI.AlgebraicGeometry.Comparison.Betti.BasisRangeSurjectivity.LinearAlgebra
