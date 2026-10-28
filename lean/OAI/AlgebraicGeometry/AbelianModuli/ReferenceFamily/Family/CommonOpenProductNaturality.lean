import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenProducts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.ProductRestrictionMaps
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.AlgebraMapDetermination
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorCoefficientNaturality

/-! # Common Open Product Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenProductNaturality

noncomputable section

/-! Product charts constructed from a restricted affine tangent
lift commute with the original tensor restriction maps on both sides.
This is a literal square of algebra homomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (X : Over (Spec (.of R))) [Smooth X.hom]

attribute [local irreducible] CommonOpenProducts.familyCommonOpenProductEquiv

theorem familyCommonOpenProductEquiv_restrict {U V W : X.left.affineOpens}
    (t : U.1 ≤ V.1) (h : V.1 ≤ W.1) (d : Derivation k R k) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    (CommonOpenProducts.familyCommonOpenProductEquiv k R X (t.trans h) d).toAlgHom.comp (ProductRestrictionMaps.familyTangentTensorRestriction k R X t d) =
      (ProductRestrictionMaps.familyProductTensorRestriction k R X t).comp (CommonOpenProducts.familyCommonOpenProductEquiv k R X h d).toAlgHom := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  apply Tensor.AlgebraMapDetermination.tensorAlgebraMap_ext_original R (DualNumber k) (AffineTangentLifts.familyAffineRing R X V)
    (DualNumber k ⊗[k] (k ⊗[R] AffineTangentLifts.familyAffineRing R X U))
  intro a
  change CommonOpenProducts.familyCommonOpenProductEquiv k R X (t.trans h) d
      (ProductRestrictionMaps.familyTangentTensorRestriction k R X t d ((1 : DualNumber k) ⊗ₜ[R] a)) =
    ProductRestrictionMaps.familyProductTensorRestriction k R X t
      (CommonOpenProducts.familyCommonOpenProductEquiv k R X h d ((1 : DualNumber k) ⊗ₜ[R] a))
  rw [ProductRestrictionMaps.familyTangentTensorRestriction_original]
  apply (Dual.NumberCoefficients.dualTensorCoefficientEquiv k (k ⊗[R] AffineTangentLifts.familyAffineRing R X U)).injective
  change Dual.NumberCoefficients.dualTensorCoefficientEquiv k (k ⊗[R] AffineTangentLifts.familyAffineRing R X U)
      (CommonOpenProducts.familyCommonOpenProductEquiv k R X (t.trans h) d
        ((1 : DualNumber k) ⊗ₜ[R] Affine.OpenDiagram.familyAffineCoordinateMap R X t a)) =
    Dual.NumberCoefficients.dualTensorCoefficientEquiv k (k ⊗[R] AffineTangentLifts.familyAffineRing R X U)
      (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) (FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R k X t)
        (CommonOpenProducts.familyCommonOpenProductEquiv k R X h d ((1 : DualNumber k) ⊗ₜ[R] a)))
  rw [Dual.TensorCoefficientNaturality.dualTensorCoefficientEquiv_natural]
  apply TrivSqZeroExt.ext
  · change Dual.TensorReduction.dualTensorReduction k (k ⊗[R] AffineTangentLifts.familyAffineRing R X U)
        (CommonOpenProducts.familyCommonOpenProductEquiv k R X (t.trans h) d
          ((1 : DualNumber k) ⊗ₜ[R] Affine.OpenDiagram.familyAffineCoordinateMap R X t a)) =
      FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R k X t (Dual.TensorReduction.dualTensorReduction k (k ⊗[R] AffineTangentLifts.familyAffineRing R X V)
        (CommonOpenProducts.familyCommonOpenProductEquiv k R X h d ((1 : DualNumber k) ⊗ₜ[R] a)))
    rw [CommonOpenProducts.familyCommonOpenProductEquiv_reduction, CommonOpenProducts.familyCommonOpenProductEquiv_reduction,
      BaseTangentTensor.baseTangentScalarReduction_tmul, BaseTangentTensor.baseTangentScalarReduction_tmul]
    rfl
  · change (Dual.NumberCoefficients.dualTensorCoefficientEquiv k (k ⊗[R] AffineTangentLifts.familyAffineRing R X U)
        (CommonOpenProducts.familyCommonOpenProductEquiv k R X (t.trans h) d
          ((1 : DualNumber k) ⊗ₜ[R] Affine.OpenDiagram.familyAffineCoordinateMap R X t a))).snd =
      FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R k X t
        (Dual.NumberCoefficients.dualTensorCoefficientEquiv k (k ⊗[R] AffineTangentLifts.familyAffineRing R X V)
          (CommonOpenProducts.familyCommonOpenProductEquiv k R X h d ((1 : DualNumber k) ⊗ₜ[R] a))).snd
    rw [CommonOpenProducts.familyCommonOpenProductEquiv_snd, CommonOpenProducts.familyCommonOpenProductEquiv_snd]
    exact FamilyTangent.DifferenceNaturality.familyRestrictedTangent_restrict_apply k R X t h d a

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenProductNaturality
