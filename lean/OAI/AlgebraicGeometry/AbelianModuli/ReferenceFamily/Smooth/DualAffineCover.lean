import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.SmoothAffineDualProduct

/-! # Dual Affine Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualAffineCover

noncomputable section

/-! A varying smooth dual-number family has a constructed affine open
cover whose charts are products of their own fibers, identically on reduction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local irreducible] Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso

variable (k : Type) [CommRing k] (X : Over (Spec (.of (DualNumber k)))) (U : X.left.AffineOpenCover)

def dualFamilyAffineChart (i : U.I₀) : Over (Spec (.of (DualNumber k))) :=
  Over.mk (U.f i ≫ X.hom)

attribute [local implicit_reducible] dualFamilyAffineChart

theorem dualFamilyAffineChart_affine (i : U.I₀) :
    IsAffine (dualFamilyAffineChart k X U i).left :=
  inferInstanceAs (IsAffine (Spec (U.X i)))

theorem dualFamilyAffineChart_smooth [Smooth X.hom] (i : U.I₀) :
    Smooth (dualFamilyAffineChart k X U i).hom :=
  inferInstanceAs (Smooth (U.f i ≫ X.hom))

def dualFamilyAffineChartInclusion (i : U.I₀) :
    dualFamilyAffineChart k X U i ⟶ X :=
  Over.homMk (U.f i)

theorem dualFamilyAffineChart_covers (x : X.left) :
    ∃ (i : U.I₀) (y : (dualFamilyAffineChart k X U i).left),
      (dualFamilyAffineChartInclusion k X U i).left y = x :=
  ⟨U.idx x, U.covers x⟩

attribute [local irreducible] dualFamilyAffineChart

/-- Specialize the constructed affine theorem without changing its base-change instances. -/
theorem normalizedSmoothDualAffineChart [Smooth X.hom] (i : U.I₀) :
    type_of% (@Normalized.SmoothAffineDualProduct.exists_normalized_smooth_affine_dual_family_product k inferInstance
    (dualFamilyAffineChart k X U i) (dualFamilyAffineChart_affine k X U i)
    (dualFamilyAffineChart_smooth k X U i)) :=
  @Normalized.SmoothAffineDualProduct.exists_normalized_smooth_affine_dual_family_product k inferInstance
    (dualFamilyAffineChart k X U i) (dualFamilyAffineChart_affine k X U i)
    (dualFamilyAffineChart_smooth k X U i)

/-- The chosen affine cover of the varying family carries these normalized charts. -/
theorem constructedSmoothDualAffineCover [Smooth X.hom] :
    type_of% (normalizedSmoothDualAffineChart k X X.left.affineOpenCover) :=
  normalizedSmoothDualAffineChart k X X.left.affineOpenCover

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualAffineCover
