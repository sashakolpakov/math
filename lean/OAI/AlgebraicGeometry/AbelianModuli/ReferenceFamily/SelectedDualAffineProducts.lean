import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualAffineCover
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.Existence

/-! # Selected Dual Affine Products -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SelectedDualAffineProducts

noncomputable section

/-! Select the constructed normalized affine products while retaining
the exact original base-change instances of their existence theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local irreducible] Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso

variable (k : Type) [CommRing k] (X : Over (Spec (.of (DualNumber k)))) [Smooth X.hom]
    (U : X.left.AffineOpenCover) (i : U.I₀)

def selectedSmoothDualAffineChartData :=
  NormalizedProduct.Existence.normalizedProductChartOfExistence (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k))
    (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)) (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso k)
    (ReferenceFamily.Smooth.DualAffineCover.dualFamilyAffineChart k X U i)
    (@ReferenceFamily.Smooth.AffineDualProduct.exists_smooth_affine_dual_family_product k inferInstance (ReferenceFamily.Smooth.DualAffineCover.dualFamilyAffineChart k X U i)
      (ReferenceFamily.Smooth.DualAffineCover.dualFamilyAffineChart_affine k X U i) (ReferenceFamily.Smooth.DualAffineCover.dualFamilyAffineChart_smooth k X U i))

def selectedSmoothDualAffineChartProduct :=
  (selectedSmoothDualAffineChartData k X U i).iso

theorem selectedSmoothDualAffineChartProduct_normalized :
    type_of% ((selectedSmoothDualAffineChartData k X U i).normalized) :=
  (selectedSmoothDualAffineChartData k X U i).normalized

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SelectedDualAffineProducts
