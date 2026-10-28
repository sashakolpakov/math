import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.ProductCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.RestrictionCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.TensorRestrictionSquare
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ChartMorphismCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorMapCoordinateLaws

/-! # Product Restriction Square -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.ProductRestrictionSquare

noncomputable section

/-! The original family morphism and both affine restrictions form
a commuting square in the actual reference product coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local irreducible] Family.CommonOpenProducts.familyCommonOpenProductEquiv
attribute [local irreducible] ProductCoordinates.familyMorphismProductCoordinates Family.RestrictionCoordinates.familyReferenceRestrictionCoordinates

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] {X Y : Over (Spec (.of R))} [Smooth X.hom] [Smooth Y.hom]
    (f : X ⟶ Y) (V V' : X.left.affineOpens) (W W' : Y.left.affineOpens)
    (t : V'.1 ≤ V.1) (s : W'.1 ≤ W.1)
    (h : V.1 ≤ f.left ⁻¹ᵁ W.1) (h' : V'.1 ≤ f.left ⁻¹ᵁ W'.1) (d : Derivation k R k)

theorem familyMorphismProductCoordinates_square :
    (Family.RestrictionCoordinates.familyReferenceRestrictionCoordinates k R X t d).comp (ProductCoordinates.familyMorphismProductCoordinates k R f V W h d) =
      (ProductCoordinates.familyMorphismProductCoordinates k R f V' W' h' d).comp (Family.RestrictionCoordinates.familyReferenceRestrictionCoordinates k R Y s d) := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  unfold Family.RestrictionCoordinates.familyReferenceRestrictionCoordinates ProductCoordinates.familyMorphismProductCoordinates
  exact Product.ChartMorphismCoordinates.productChartMorphism_square
    (S := DualNumber k ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W) (S' := DualNumber k ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W')
    (T := DualNumber k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) (T' := DualNumber k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V')
    (A := k ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W) (A' := k ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W')
    (B := k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) (B' := k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V')
    (BaseTangentTensor.baseTangentTensorMorphism k R (Family.AffineTangentLifts.familyAffineRing R Y W) (Family.AffineTangentLifts.familyAffineRing R X V)
      (TensorCoordinates.familyMorphismAffineCoordinates R f V W h) d)
    (BaseTangentTensor.baseTangentTensorMorphism k R (Family.AffineTangentLifts.familyAffineRing R Y W') (Family.AffineTangentLifts.familyAffineRing R X V')
      (TensorCoordinates.familyMorphismAffineCoordinates R f V' W' h') d)
    (Family.ProductRestrictionMaps.familyTangentTensorRestriction k R Y s d) (Family.ProductRestrictionMaps.familyTangentTensorRestriction k R X t d)
    (Family.CommonOpenProducts.familyCommonOpenProductEquiv k R Y (le_refl W.1) d)
    (Family.CommonOpenProducts.familyCommonOpenProductEquiv k R Y (le_refl W'.1) d)
    (Family.CommonOpenProducts.familyCommonOpenProductEquiv k R X (le_refl V.1) d)
    (Family.CommonOpenProducts.familyCommonOpenProductEquiv k R X (le_refl V'.1) d)
    (TensorRestrictionSquare.familyMorphismTensorCoordinates_square R (DualNumber k) f V V' W W' t s h h')

theorem familyMorphismCoefficientCoordinates_square :
    (Dual.TensorMapCoordinates.dualTensorMapCoordinates (Family.RestrictionCoordinates.familyReferenceRestrictionCoordinates k R X t d)).comp
        (Dual.TensorMapCoordinates.dualTensorMapCoordinates (ProductCoordinates.familyMorphismProductCoordinates k R f V W h d)) =
      (Dual.TensorMapCoordinates.dualTensorMapCoordinates (ProductCoordinates.familyMorphismProductCoordinates k R f V' W' h' d)).comp
        (Dual.TensorMapCoordinates.dualTensorMapCoordinates (Family.RestrictionCoordinates.familyReferenceRestrictionCoordinates k R Y s d)) := by
  have H := congrArg Dual.TensorMapCoordinates.dualTensorMapCoordinates (familyMorphismProductCoordinates_square k R f V V' W W' t s h h' d)
  rw [Dual.TensorMapCoordinateLaws.dualTensorMapCoordinates_comp, Dual.TensorMapCoordinateLaws.dualTensorMapCoordinates_comp] at H
  exact H

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.ProductRestrictionSquare
