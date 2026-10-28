import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.AffineDerivationRestriction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FiberCoefficientDerivationKernel

/-! # Common Open Tangent Differences -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenTangentDifferences

noncomputable section

/-! Chosen tangent lifts on actual affine family opens restrict
coherently to common opens. Their ordered differences descend linearly
to the fixed fiber and satisfy the cocycle equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (X : Over (Spec (.of R))) [Smooth X.hom]

attribute [local instance 50] AffineTangentLifts.familyAffineCoefficientAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra AffineTangentLifts.familyAffineCoefficientTower

local instance familyCommonOpenTensor_ring (V : X.left.affineOpens) :
    CommRing (k ⊗[R] AffineTangentLifts.familyAffineRing R X V) :=
  Algebra.TensorProduct.instCommRing (R := R) (A := k) (B := AffineTangentLifts.familyAffineRing R X V)

local instance familyCommonOpenTensor_tower (V : X.left.affineOpens) :
    IsScalarTower k (AffineTangentLifts.familyAffineRing R X V) (k ⊗[R] AffineTangentLifts.familyAffineRing R X V) :=
  PointFiberTensorLifts.pointFiberTensor_scalarTower k R (AffineTangentLifts.familyAffineRing R X V)

def familyRestrictedTangent {V W : X.left.affineOpens} (h : V.1 ≤ W.1) :
    Derivation k R k →ₗ[k]
      Derivation k (AffineTangentLifts.familyAffineRing R X V) (k ⊗[R] AffineTangentLifts.familyAffineRing R X V) :=
  (AffineDerivationRestriction.familyAffineDerivationRestriction k R X h).comp (AffineTangentLifts.familyAffineTangentDerivation k R X W)

theorem familyRestrictedTangent_base {V W : X.left.affineOpens} (h : V.1 ≤ W.1)
    (d : Derivation k R k) (r : R) :
    familyRestrictedTangent k R X h d (algebraMap R (AffineTangentLifts.familyAffineRing R X V) r) =
      d r ⊗ₜ[R] (1 : AffineTangentLifts.familyAffineRing R X V) := by
  change AffineDerivationRestriction.familyAffineDerivationRestriction k R X h (AffineTangentLifts.familyAffineTangentDerivation k R X W d)
    (algebraMap R (AffineTangentLifts.familyAffineRing R X V) r) = _
  rw [← (Affine.OpenDiagram.familyAffineCoordinateMap R X h).commutes r, AffineDerivationRestriction.familyAffineDerivationRestriction_apply,
    AffineTangentLifts.familyAffineTangentDerivation_base]
  change d r ⊗ₜ[R] (Affine.OpenDiagram.familyAffineCoordinateMap R X h) 1 = _
  rw [map_one]

theorem familyRestrictedTangent_restrict {U V W : X.left.affineOpens}
    (h : U.1 ≤ V.1) (j : V.1 ≤ W.1) :
    (AffineDerivationRestriction.familyAffineDerivationRestriction k R X h).comp (familyRestrictedTangent k R X j) =
      familyRestrictedTangent k R X (h.trans j) := by
  unfold familyRestrictedTangent
  rw [← LinearMap.comp_assoc, AffineDerivationRestriction.familyAffineDerivationRestriction_comp]

theorem familyRestrictedTangent_sameBase {V W Z : X.left.affineOpens}
    (h : V.1 ≤ W.1) (j : V.1 ≤ Z.1) :
    ((Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k R (AffineTangentLifts.familyAffineRing R X V)
      (k ⊗[R] AffineTangentLifts.familyAffineRing R X V)).restrictScalars k).comp (familyRestrictedTangent k R X h) =
    ((Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k R (AffineTangentLifts.familyAffineRing R X V)
      (k ⊗[R] AffineTangentLifts.familyAffineRing R X V)).restrictScalars k).comp (familyRestrictedTangent k R X j) := by
  apply LinearMap.ext
  intro d
  apply Derivation.ext
  intro r
  change familyRestrictedTangent k R X h d (algebraMap R (AffineTangentLifts.familyAffineRing R X V) r) =
    familyRestrictedTangent k R X j d (algebraMap R (AffineTangentLifts.familyAffineRing R X V) r)
  rw [familyRestrictedTangent_base, familyRestrictedTangent_base]

def familyCommonOpenTangentDifference {V W Z : X.left.affineOpens}
    (h : V.1 ≤ W.1) (j : V.1 ≤ Z.1) :
    Derivation k R k →ₗ[k]
      Derivation k (k ⊗[R] AffineTangentLifts.familyAffineRing R X V) (k ⊗[R] AffineTangentLifts.familyAffineRing R X V) :=
  FiberCoefficientDerivationKernel.linearFiberLiftDifference k R (AffineTangentLifts.familyAffineRing R X V)
    (k ⊗[R] AffineTangentLifts.familyAffineRing R X V) (k ⊗[R] AffineTangentLifts.familyAffineRing R X V)
    (familyRestrictedTangent k R X h) (familyRestrictedTangent k R X j)
    (familyRestrictedTangent_sameBase k R X h j)

theorem familyCommonOpenTangentDifference_original {V W Z : X.left.affineOpens}
    (h : V.1 ≤ W.1) (j : V.1 ≤ Z.1) (d : Derivation k R k) (a : AffineTangentLifts.familyAffineRing R X V) :
    familyCommonOpenTangentDifference k R X h j d ((1 : k) ⊗ₜ[R] a) =
      familyRestrictedTangent k R X j d a - familyRestrictedTangent k R X h d a :=
  FiberCoefficientDerivationKernel.linearFiberLiftDifference_algebraMap k R (AffineTangentLifts.familyAffineRing R X V)
    (k ⊗[R] AffineTangentLifts.familyAffineRing R X V) (k ⊗[R] AffineTangentLifts.familyAffineRing R X V)
    (familyRestrictedTangent k R X h) (familyRestrictedTangent k R X j)
    (familyRestrictedTangent_sameBase k R X h j) d a

theorem familyCommonOpenTangentDifference_cocycle {V W Z Q : X.left.affineOpens}
    (h : V.1 ≤ W.1) (j : V.1 ≤ Z.1) (l : V.1 ≤ Q.1) :
    familyCommonOpenTangentDifference k R X h j + familyCommonOpenTangentDifference k R X j l =
      familyCommonOpenTangentDifference k R X h l :=
  FiberCoefficientDerivationKernel.linearFiberLiftDifference_cocycle k R (AffineTangentLifts.familyAffineRing R X V)
    (k ⊗[R] AffineTangentLifts.familyAffineRing R X V) (k ⊗[R] AffineTangentLifts.familyAffineRing R X V)
    (familyRestrictedTangent k R X h) (familyRestrictedTangent k R X j)
    (familyRestrictedTangent_sameBase k R X h j) (familyRestrictedTangent k R X l)
    (familyRestrictedTangent_sameBase k R X j l)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenTangentDifferences
