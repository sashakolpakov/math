import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientUnitLogarithms
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.DifferenceNaturality

/-! # Unit Logarithms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.UnitLogarithms

noncomputable section

/-! Original family units have first-order logarithms linear in the
base tangent. Their restriction and change-of-chart identities retain
the actual affine coordinate maps and fixed-fiber derivations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (X : Over (Spec (.of R))) [Smooth X.hom]

attribute [local instance 50] AffineTangentLifts.familyAffineCoefficientAlgebra
attribute [local instance] AffineTangentLifts.familyAffineCoefficientTower Algebra.TensorProduct.rightAlgebra
attribute [local instance] PointFiberTensorLifts.pointFiberTensor_scalarTower

def familyRestrictedUnitLog {V W : X.left.affineOpens} (h : V.1 ≤ W.1)
    (u : (AffineTangentLifts.familyAffineRing R X V)ˣ) :
    Derivation k R k →ₗ[k] (k ⊗[R] AffineTangentLifts.familyAffineRing R X V) :=
  (CoefficientUnitLogarithms.coefficientUnitLogLinear u).comp (CommonOpenTangentDifferences.familyRestrictedTangent k R X h)

theorem familyRestrictedUnitLog_mul {V W : X.left.affineOpens} (h : V.1 ≤ W.1)
    (u v : (AffineTangentLifts.familyAffineRing R X V)ˣ) (d : Derivation k R k) :
    familyRestrictedUnitLog k R X h (u * v) d =
      familyRestrictedUnitLog k R X h u d + familyRestrictedUnitLog k R X h v d :=
  CoefficientUnitLogarithms.coefficientUnitLog_mul (CommonOpenTangentDifferences.familyRestrictedTangent k R X h d) u v

theorem familyRestrictedUnitLog_restrict {U V W : X.left.affineOpens}
    (h : U.1 ≤ V.1) (j : V.1 ≤ W.1) (u : (AffineTangentLifts.familyAffineRing R X V)ˣ) (d : Derivation k R k) :
    familyRestrictedUnitLog k R X (h.trans j)
        (Units.map (Affine.OpenDiagram.familyAffineCoordinateMap R X h).toMonoidHom u) d =
      FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R k X h (familyRestrictedUnitLog k R X j u d) := by
  change CommonOpenTangentDifferences.familyRestrictedTangent k R X (h.trans j) d (Affine.OpenDiagram.familyAffineCoordinateMap R X h u.val) *
      ((1 : k) ⊗ₜ[R] Affine.OpenDiagram.familyAffineCoordinateMap R X h (u⁻¹).val) =
    FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R k X h
      (CommonOpenTangentDifferences.familyRestrictedTangent k R X j d u.val * ((1 : k) ⊗ₜ[R] (u⁻¹).val))
  rw [FamilyTangent.DifferenceNaturality.familyRestrictedTangent_restrict_apply, map_mul]
  rfl

theorem familyRestrictedUnitLog_difference {V W Z : X.left.affineOpens}
    (h : V.1 ≤ W.1) (j : V.1 ≤ Z.1) (u : (AffineTangentLifts.familyAffineRing R X V)ˣ) (d : Derivation k R k) :
    familyRestrictedUnitLog k R X j u d - familyRestrictedUnitLog k R X h u d =
      CommonOpenTangentDifferences.familyCommonOpenTangentDifference k R X h j d ((1 : k) ⊗ₜ[R] u.val) *
        ((1 : k) ⊗ₜ[R] (u⁻¹).val) := by
  rw [CommonOpenTangentDifferences.familyCommonOpenTangentDifference_original]
  exact (sub_mul (CommonOpenTangentDifferences.familyRestrictedTangent k R X j d u.val)
    (CommonOpenTangentDifferences.familyRestrictedTangent k R X h d u.val) ((1 : k) ⊗ₜ[R] (u⁻¹).val)).symm

theorem familyRestrictedUnitLog_triangle {V W Z : X.left.affineOpens}
    (h : V.1 ≤ W.1) (j : V.1 ≤ Z.1) (u v w : (AffineTangentLifts.familyAffineRing R X V)ˣ)
    (hw : w = u * v) (d : Derivation k R k) :
    familyRestrictedUnitLog k R X j v d - familyRestrictedUnitLog k R X h w d +
        familyRestrictedUnitLog k R X h u d =
      CommonOpenTangentDifferences.familyCommonOpenTangentDifference k R X h j d ((1 : k) ⊗ₜ[R] v.val) *
        ((1 : k) ⊗ₜ[R] (v⁻¹).val) := by
  rw [hw, familyRestrictedUnitLog_mul]
  have hd := familyRestrictedUnitLog_difference k R X h j v d
  calc
    _ = familyRestrictedUnitLog k R X j v d - familyRestrictedUnitLog k R X h v d := by abel
    _ = _ := hd

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.UnitLogarithms
