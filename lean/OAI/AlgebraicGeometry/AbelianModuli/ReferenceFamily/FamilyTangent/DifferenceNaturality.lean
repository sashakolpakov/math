import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenTangentDifferences
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.DerivationPresheaf
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FiberTensorRestrictionDetection

/-! # Difference Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.DifferenceNaturality

noncomputable section

/-! The linear tangent differences commute with restriction to
smaller actual affine opens. Thus the differences live in the fixed
fiber's derivation presheaf, with the original tensor maps retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (X : Over (Spec (.of R))) [Smooth X.hom]

attribute [local instance 50] Family.AffineTangentLifts.familyAffineCoefficientAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra Family.AffineTangentLifts.familyAffineCoefficientTower

theorem familyRestrictedTangent_restrict_apply {U V W : X.left.affineOpens}
    (h : U.1 ≤ V.1) (j : V.1 ≤ W.1) (d : Derivation k R k) (a : Family.AffineTangentLifts.familyAffineRing R X V) :
    Family.CommonOpenTangentDifferences.familyRestrictedTangent k R X (h.trans j) d (Affine.OpenDiagram.familyAffineCoordinateMap R X h a) =
      FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R k X h (Family.CommonOpenTangentDifferences.familyRestrictedTangent k R X j d a) := by
  have he := Derivation.congr_fun
    (LinearMap.congr_fun (Family.CommonOpenTangentDifferences.familyRestrictedTangent_restrict k R X h j) d)
    (Affine.OpenDiagram.familyAffineCoordinateMap R X h a)
  exact he.symm.trans (Family.AffineDerivationRestriction.familyAffineDerivationRestriction_apply k R X h
    (Family.CommonOpenTangentDifferences.familyRestrictedTangent k R X j d) a)

theorem familyCommonOpenTangentDifference_restrict {U V W Z : X.left.affineOpens}
    (t : U.1 ≤ V.1) (h : V.1 ≤ W.1) (j : V.1 ≤ Z.1) :
    (FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction R k X t).comp (Family.CommonOpenTangentDifferences.familyCommonOpenTangentDifference k R X h j) =
      Family.CommonOpenTangentDifferences.familyCommonOpenTangentDifference k R X (t.trans h) (t.trans j) := by
  apply LinearMap.ext
  intro d
  apply Eq.symm
  apply FiberTensorRestrictionDetection.pointFiberTensorDerivation_restriction_of_original k R (Family.AffineTangentLifts.familyAffineRing R X V)
    (Family.AffineTangentLifts.familyAffineRing R X U) (Affine.OpenDiagram.familyAffineCoordinateMap R X t)
    (FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction_etale R k X t)
  intro a
  rw [Family.CommonOpenTangentDifferences.familyCommonOpenTangentDifference_original, Family.CommonOpenTangentDifferences.familyCommonOpenTangentDifference_original]
  rw [familyRestrictedTangent_restrict_apply, familyRestrictedTangent_restrict_apply]
  exact (FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R k X t).map_sub _ _ |>.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.DifferenceNaturality
