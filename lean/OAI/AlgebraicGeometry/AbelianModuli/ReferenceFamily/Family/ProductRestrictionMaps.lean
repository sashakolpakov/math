import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.DifferenceNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TangentDualScalarTowers

/-! # Product Restriction Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.ProductRestrictionMaps

noncomputable section

/-! The original affine restriction gives literal tensor maps on
the tangent pullbacks and on the constant products of their fixed fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (X : Over (Spec (.of R)))

def familyTangentTensorRestriction {V W : X.left.affineOpens} (h : V.1 ≤ W.1) (d : Derivation k R k) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    (DualNumber k ⊗[R] AffineTangentLifts.familyAffineRing R X W) →ₐ[DualNumber k]
      (DualNumber k ⊗[R] AffineTangentLifts.familyAffineRing R X V) := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  have : IsScalarTower R (DualNumber k) (DualNumber k) :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := DualNumber k) (A := DualNumber k) (fun _ => rfl)
  exact Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) (Affine.OpenDiagram.familyAffineCoordinateMap R X h)

theorem familyTangentTensorRestriction_original {V W : X.left.affineOpens}
    (h : V.1 ≤ W.1) (d : Derivation k R k) (a : AffineTangentLifts.familyAffineRing R X W) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    familyTangentTensorRestriction k R X h d ((1 : DualNumber k) ⊗ₜ[R] a) =
      (1 : DualNumber k) ⊗ₜ[R] Affine.OpenDiagram.familyAffineCoordinateMap R X h a := rfl

def familyProductTensorRestriction {V W : X.left.affineOpens} (h : V.1 ≤ W.1) :
    (DualNumber k ⊗[k] (k ⊗[R] AffineTangentLifts.familyAffineRing R X W)) →ₐ[DualNumber k]
      (DualNumber k ⊗[k] (k ⊗[R] AffineTangentLifts.familyAffineRing R X V)) :=
  Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) (FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R k X h)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.ProductRestrictionMaps
