import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenProductNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ChartMorphismCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BaseTangentTensor

/-! # Restriction Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.RestrictionCoordinates

noncomputable section

/-! Original affine restriction maps acquire actual deformed maps
between the selected reference product charts. Their reductions are
the original fixed-fiber tensor restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local irreducible] CommonOpenProducts.familyCommonOpenProductEquiv

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (X : Over (Spec (.of R))) [Smooth X.hom]

def familyReferenceRestrictionCoordinates {U V : X.left.affineOpens} (t : U.1 ≤ V.1) (d : Derivation k R k) :
    (DualNumber k ⊗[k] (k ⊗[R] AffineTangentLifts.familyAffineRing R X V)) →ₐ[DualNumber k]
      (DualNumber k ⊗[k] (k ⊗[R] AffineTangentLifts.familyAffineRing R X U)) := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  exact Product.ChartMorphismCoordinates.productChartMorphismCoordinates
    (S := DualNumber k ⊗[R] AffineTangentLifts.familyAffineRing R X V) (T := DualNumber k ⊗[R] AffineTangentLifts.familyAffineRing R X U)
    (A := k ⊗[R] AffineTangentLifts.familyAffineRing R X V) (B := k ⊗[R] AffineTangentLifts.familyAffineRing R X U)
    (ProductRestrictionMaps.familyTangentTensorRestriction k R X t d)
    (CommonOpenProducts.familyCommonOpenProductEquiv k R X (le_refl V.1) d)
    (CommonOpenProducts.familyCommonOpenProductEquiv k R X (le_refl U.1) d)

theorem familyReferenceRestrictionCoordinates_reduction {U V : X.left.affineOpens}
    (t : U.1 ≤ V.1) (d : Derivation k R k)
    (u : DualNumber k ⊗[k] (k ⊗[R] AffineTangentLifts.familyAffineRing R X V)) :
    Dual.TensorReduction.dualTensorReduction k (k ⊗[R] AffineTangentLifts.familyAffineRing R X U) (familyReferenceRestrictionCoordinates k R X t d u) =
      FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R k X t (Dual.TensorReduction.dualTensorReduction k (k ⊗[R] AffineTangentLifts.familyAffineRing R X V) u) := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  exact Product.ChartMorphismCoordinates.productChartMorphismCoordinates_reduction
    (S := DualNumber k ⊗[R] AffineTangentLifts.familyAffineRing R X V) (T := DualNumber k ⊗[R] AffineTangentLifts.familyAffineRing R X U)
    (A := k ⊗[R] AffineTangentLifts.familyAffineRing R X V) (B := k ⊗[R] AffineTangentLifts.familyAffineRing R X U)
    (ProductRestrictionMaps.familyTangentTensorRestriction k R X t d)
    (CommonOpenProducts.familyCommonOpenProductEquiv k R X (le_refl V.1) d)
    (CommonOpenProducts.familyCommonOpenProductEquiv k R X (le_refl U.1) d)
    (BaseTangentTensor.baseTangentScalarReduction k R (AffineTangentLifts.familyAffineRing R X V) d)
    (BaseTangentTensor.baseTangentScalarReduction k R (AffineTangentLifts.familyAffineRing R X U) d)
    (FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R k X t)
    (CommonOpenProducts.familyCommonOpenProductEquiv_reduction k R X (le_refl V.1) d)
    (CommonOpenProducts.familyCommonOpenProductEquiv_reduction k R X (le_refl U.1) d)
    (BaseTangentTensor.baseTangentTensorMorphism_reduction k R (AffineTangentLifts.familyAffineRing R X V) (AffineTangentLifts.familyAffineRing R X U)
      (Affine.OpenDiagram.familyAffineCoordinateMap R X t) d) u

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.RestrictionCoordinates
