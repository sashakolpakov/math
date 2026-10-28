import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.AffineDualProduct
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.VaryingDualReduction

/-! # Special Fiber Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.SpecialFiberCoordinates

noncomputable section

/-! The special fiber of the literal tensor-product affine scheme has
its actual coefficient spectrum as a canonical presentation. Its closed
immersion is the prescribed tensor reduction map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver Smooth.AffineDualProduct.dualBaseReduction VaryingDualReduction.dualFamilyReduction
attribute [local implicit_reducible] Dual.TensorReduction.dualTensorReductionIdeal

variable (k : Type) [Field k]

theorem canonicalDualFiberIso_hom_reduction (S : Type) [CommRing S]
    [Algebra (DualNumber k) S] [Algebra k S] [IsScalarTower k (DualNumber k) S] :
    (Smooth.AffineDualProduct.canonicalDualFiberIso k S).hom.left ≫ VaryingDualReduction.dualFamilyReduction k (EtaleSplittingAt.EtaleSplitting.affineOver (DualNumber k) S) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (CanonicalDualSpecialFiber.dualSpecialFiberIdeal k S))) :=
  (CanonicalDualFiberSquare.canonical_dual_specialFiber_isPullback k S).isoPullback_hom_fst

variable (A : Type) [CommRing A] [Algebra k A]

local instance tensorSpecialFiberCoordinates_commRing : CommRing (DualNumber k ⊗[k] A) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := A)

def dualTensorSpecialFiberIso : EtaleSplittingAt.EtaleSplitting.affineOver k A ≅
    (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj (EtaleSplittingAt.EtaleSplitting.affineOver (DualNumber k) (DualNumber k ⊗[k] A)) :=
  EtaleSplittingAt.EtaleSplitting.affineAlgIso k (CanonicalDualSpecialFiber.dualSpecialFiber k (DualNumber k ⊗[k] A)) (Dual.TensorReductionEquiv.dualTensorReductionQuotientEquiv k A) ≪≫
    Smooth.AffineDualProduct.canonicalDualFiberIso k (DualNumber k ⊗[k] A)

theorem dualTensorSpecialFiberIso_hom_reduction :
    (dualTensorSpecialFiberIso k A).hom.left ≫
        VaryingDualReduction.dualFamilyReduction k (EtaleSplittingAt.EtaleSplitting.affineOver (DualNumber k) (DualNumber k ⊗[k] A)) =
      Spec.map (CommRingCat.ofHom (Dual.TensorReduction.dualTensorReduction k A).toRingHom) := by
  let e : CanonicalDualSpecialFiber.dualSpecialFiber k (DualNumber k ⊗[k] A) ≃ₐ[k] A := Dual.TensorReductionEquiv.dualTensorReductionQuotientEquiv k A
  change (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    (Smooth.AffineDualProduct.canonicalDualFiberIso k (DualNumber k ⊗[k] A)).hom.left) ≫
      VaryingDualReduction.dualFamilyReduction k (EtaleSplittingAt.EtaleSplitting.affineOver (DualNumber k) (DualNumber k ⊗[k] A)) = _
  rw [Category.assoc, canonicalDualFiberIso_hom_reduction, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (Dual.TensorReductionEquiv.dualTensorReductionQuotientEquiv_mk k A)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.SpecialFiberCoordinates
