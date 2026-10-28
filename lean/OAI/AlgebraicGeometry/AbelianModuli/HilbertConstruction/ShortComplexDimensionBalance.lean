import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Short Complex Dimension Balance -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ShortComplexDimensionBalance

noncomputable section

/-! Rank-nullity and the concrete kernel quotient give the dimension balance in a short complex. -/
open _root_.CategoryTheory
universe u

theorem shortComplex_dimension_balance {K : Type u} [Field K]
    (S : ShortComplex (ModuleCat.{u} K))
    [Module.Finite K S.X₁] [Module.Finite K S.X₂] :
    Module.finrank K S.X₂ = Module.finrank K S.homology +
      Module.finrank K (LinearMap.range S.f.hom) +
      Module.finrank K (LinearMap.range S.g.hom) := by
  have hf := S.f.hom.finrank_range_add_finrank_ker
  have hc := S.moduleCatToCycles.finrank_range_add_finrank_ker
  have hg := S.g.hom.finrank_range_add_finrank_ker
  have hq := (LinearMap.range S.moduleCatToCycles).finrank_quotient_add_finrank
  have hh := S.moduleCatHomologyIso.toLinearEquiv.finrank_eq
  change Module.finrank K S.homology =
    Module.finrank K (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) at hh
  have hk : LinearMap.ker S.moduleCatToCycles = LinearMap.ker S.f.hom :=
    LinearMap.ker_codRestrict _ _ _
  have hkdim := congrArg (fun P : Submodule K S.X₁ => Module.finrank K P) hk
  omega

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ShortComplexDimensionBalance
