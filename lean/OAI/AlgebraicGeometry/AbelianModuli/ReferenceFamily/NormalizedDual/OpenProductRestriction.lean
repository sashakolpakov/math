import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.VaryingDualOpenFactorization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.OpenProductData
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.RestrictionSquare
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OverPullbackCartesianMap
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductComparisonRepresentative

/-! # Open Product Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.OpenProductRestriction

noncomputable section

/-! A normalized product chart restricts to an actual normalized product
chart on every open subfamily, commuting with the original inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] OpenProductData.NormalizesProductFiber
attribute [local irreducible] Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso

variable (k : Type) [Field k]
    {U X : Over (Spec (.of (DualNumber k)))} (i : U ⟶ X)
    (e : X ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj
      ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X))

def restrictNormalizedDualProduct [IsOpenImmersion i.left]
    (he : OpenProductData.NormalizesDualProductFiber k e) := by
  let F := Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)
  let G := Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)
  let n := Dual.ProductComparisonRepresentative.dualProductComparisonRepresentative k
  have hn : n = Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso k := Dual.ProductComparisonRepresentative.dualProductComparisonRepresentative_eq k
  have he' : OpenProductData.NormalizesProductFiber F G n e :=
    (congrArg (fun c => OpenProductData.NormalizesProductFiber F G c e) hn).mpr he
  let j := F.map (G.map i)
  have : IsOpenImmersion (G.map i).left := OverPullbackCartesianMap.overPullback_map_open (Smooth.AffineDualProduct.dualBaseReduction k) i
  have : IsOpenImmersion j.left := OverPullbackCartesianMap.overPullback_map_open (Smooth.AffineDualProduct.dualBaseProjection k) (G.map i)
  let a := (n.app (G.obj U)).symm
  have h := NormalizedProduct.RestrictionSquare.normalized_product_restriction_square F G n i e he'
  let E := VaryingDualOpenFactorization.dualOpenRestrictionIso k e i j a h
  have hE := VaryingDualOpenFactorization.dualOpenRestrictionIso_reduction k e i j a h
  let r := OpenProductData.normalizedProductRestrictionOfReduction F G n i e E
    (VaryingDualOpenFactorization.dualOpenRestrictionIso_hom_fac k e i j a h) hE
  exact hn ▸ r

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.OpenProductRestriction
