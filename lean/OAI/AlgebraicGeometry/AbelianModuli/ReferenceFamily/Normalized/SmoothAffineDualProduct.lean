import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.AffineDualProduct
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.FiberNormalization

/-! # Smooth Affine Dual Product -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.SmoothAffineDualProduct

noncomputable section

/-! The constructed affine product can be chosen to induce the identity
on the actual special fiber, using the canonical base-change comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (k : Type) [CommRing k]

theorem dualBaseReduction_projection : ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k ≫ ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) = _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap k (DualNumber k)) ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom = 𝟙 _ := by
    ext c
    rfl
  rw [h, Spec.map_id]

def dualProductSpecialFiberIso :
    Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k) ⋙ Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k) ≅
      𝟭 (Over (Spec (.of k))) :=
  (Over.pullbackComp (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k) (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).symm ≪≫
    eqToIso (congrArg (fun f : Spec (.of k) ⟶ Spec (.of k) => Over.pullback f)
      (dualBaseReduction_projection k)) ≪≫ Over.pullbackId

theorem exists_normalized_smooth_affine_dual_family_product
    (X : Over (Spec (.of (DualNumber k)))) [IsAffine X.left] [Smooth X.hom] :
    ∃ e : X ≅ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).obj
        ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).obj X),
      (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).map e.hom ≫
          (dualProductSpecialFiberIso k).hom.app ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).obj X) =
        𝟙 ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).obj X) :=
  Product.FiberNormalization.exists_product_iso_identity_on_fiber (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k))
    (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)) (dualProductSpecialFiberIso k) X
    (ReferenceFamily.Smooth.AffineDualProduct.exists_smooth_affine_dual_family_product k X)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.SmoothAffineDualProduct
