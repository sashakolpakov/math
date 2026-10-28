import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.TensorCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BaseTangentTensor
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenProducts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ChartMorphismCoordinates

/-! # Product Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.ProductCoordinates

noncomputable section

/-! The original family morphism in the family's selected product
charts is an actual map over the specified dual-number base. Its
reduction is exactly the original fixed-fiber tensor morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local irreducible] Family.CommonOpenProducts.familyCommonOpenProductEquiv

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] {X Y : Over (Spec (.of R))} [Smooth X.hom] [Smooth Y.hom]
    (f : X ⟶ Y) (V : X.left.affineOpens) (W : Y.left.affineOpens)
    (h : V.1 ≤ f.left ⁻¹ᵁ W.1) (d : Derivation k R k)

def familyMorphismProductCoordinates :
    (DualNumber k ⊗[k] (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W)) →ₐ[DualNumber k]
      (DualNumber k ⊗[k] (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)) := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  exact Product.ChartMorphismCoordinates.productChartMorphismCoordinates
    (S := DualNumber k ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W) (T := DualNumber k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)
    (A := k ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W) (B := k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)
    (BaseTangentTensor.baseTangentTensorMorphism k R (Family.AffineTangentLifts.familyAffineRing R Y W) (Family.AffineTangentLifts.familyAffineRing R X V)
      (TensorCoordinates.familyMorphismAffineCoordinates R f V W h) d)
    (Family.CommonOpenProducts.familyCommonOpenProductEquiv k R Y (le_refl W.1) d)
    (Family.CommonOpenProducts.familyCommonOpenProductEquiv k R X (le_refl V.1) d)

theorem familyMorphismProductCoordinates_reduction
    (u : DualNumber k ⊗[k] (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W)) :
    Dual.TensorReduction.dualTensorReduction k (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) (familyMorphismProductCoordinates k R f V W h d u) =
      TensorCoordinates.familyMorphismTensorCoordinates R k f V W h
        (Dual.TensorReduction.dualTensorReduction k (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W) u) := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  exact Product.ChartMorphismCoordinates.productChartMorphismCoordinates_reduction
    (S := DualNumber k ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W) (T := DualNumber k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)
    (A := k ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W) (B := k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)
    (BaseTangentTensor.baseTangentTensorMorphism k R (Family.AffineTangentLifts.familyAffineRing R Y W) (Family.AffineTangentLifts.familyAffineRing R X V)
      (TensorCoordinates.familyMorphismAffineCoordinates R f V W h) d)
    (Family.CommonOpenProducts.familyCommonOpenProductEquiv k R Y (le_refl W.1) d)
    (Family.CommonOpenProducts.familyCommonOpenProductEquiv k R X (le_refl V.1) d)
    (BaseTangentTensor.baseTangentScalarReduction k R (Family.AffineTangentLifts.familyAffineRing R Y W) d)
    (BaseTangentTensor.baseTangentScalarReduction k R (Family.AffineTangentLifts.familyAffineRing R X V) d)
    (TensorCoordinates.familyMorphismTensorCoordinates R k f V W h)
    (Family.CommonOpenProducts.familyCommonOpenProductEquiv_reduction k R Y (le_refl W.1) d)
    (Family.CommonOpenProducts.familyCommonOpenProductEquiv_reduction k R X (le_refl V.1) d)
    (BaseTangentTensor.baseTangentTensorMorphism_reduction k R (Family.AffineTangentLifts.familyAffineRing R Y W) (Family.AffineTangentLifts.familyAffineRing R X V)
      (TensorCoordinates.familyMorphismAffineCoordinates R f V W h) d) u

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.ProductCoordinates
