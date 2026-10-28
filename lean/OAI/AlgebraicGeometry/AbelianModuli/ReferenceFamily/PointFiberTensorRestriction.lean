import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointFiberTensorLifts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BaseTangentOverlapDerivations

/-! # Point Fiber Tensor Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointFiberTensorRestriction

noncomputable section

/-! An actual etale affine restriction extends the chosen tangent
lifts into the fixed overlap fiber. The coefficient restriction is the
literal tensor map and preserves the original base tangent. -/

open scoped TensorProduct

variable (k R A D : Type) [Field k] [CommRing R] [CommRing A] [CommRing D]
    [Algebra k R] [Algebra k A] [Algebra k D] [Algebra R k] [Algebra R A] [Algebra R D]
    [Algebra A D] [IsScalarTower k R k] [IsScalarTower k R A] [IsScalarTower k R D]
    [IsScalarTower k A D] [IsScalarTower R A D]

local instance pointFiberRestriction_sourceRing : CommRing (k ⊗[R] A) :=
  Algebra.TensorProduct.instCommRing (R := R) (A := k) (B := A)

local instance pointFiberRestriction_targetRing : CommRing (k ⊗[R] D) :=
  Algebra.TensorProduct.instCommRing (R := R) (A := k) (B := D)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance pointFiberRestriction_sourceTower : IsScalarTower k A (k ⊗[R] A) :=
  PointFiberTensorLifts.pointFiberTensor_scalarTower k R A

local instance pointFiberRestriction_targetTower : IsScalarTower k D (k ⊗[R] D) :=
  PointFiberTensorLifts.pointFiberTensor_scalarTower k R D

@[instance_reducible]
def pointFiberRestrictionAlgebra : Algebra A (k ⊗[R] D) :=
  ((algebraMap D (k ⊗[R] D)).comp (algebraMap A D)).toAlgebra

attribute [local instance 50] pointFiberRestrictionAlgebra

local instance pointFiberRestriction_tower : IsScalarTower A D (k ⊗[R] D) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance pointFiberRestriction_scalarTower : IsScalarTower k A (k ⊗[R] D) := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  rw [IsScalarTower.algebraMap_apply k D (k ⊗[R] D), IsScalarTower.algebraMap_apply k A D]
  rfl

def pointFiberTensorCoefficientMap : (k ⊗[R] A) →ₐ[A] (k ⊗[R] D) where
  __ := (Algebra.TensorProduct.map (AlgHom.id k k) (IsScalarTower.toAlgHom R A D)).toRingHom
  commutes' a := by
    change (1 : k) ⊗ₜ[R] algebraMap A D a = (1 : k) ⊗ₜ[R] algebraMap A D a
    rfl

omit [Algebra k R] [Algebra k A] [Algebra k D] [IsScalarTower k R k]
  [IsScalarTower k R A] [IsScalarTower k R D] [IsScalarTower k A D] in
theorem pointFiberTensorCoefficientMap_tmul (c : k) (a : A) :
    pointFiberTensorCoefficientMap k R A D (c ⊗ₜ[R] a) = c ⊗ₜ[R] algebraMap A D a := rfl

variable [Algebra.FormallyEtale A D]

def pointFiberTensorDerivationRestriction :
    Derivation k A (k ⊗[R] A) →ₗ[k] Derivation k D (k ⊗[R] D) :=
  Affine.OverlapDerivationMap.affineOverlapDerivationMap k A D (k ⊗[R] A) (k ⊗[R] D) (pointFiberTensorCoefficientMap k R A D)

theorem pointFiberTensorDerivationRestriction_algebraMap (d : Derivation k A (k ⊗[R] A)) (a : A) :
    pointFiberTensorDerivationRestriction k R A D d (algebraMap A D a) =
      pointFiberTensorCoefficientMap k R A D (d a) :=
  Affine.OverlapDerivationMap.affineOverlapDerivationMap_algebraMap k A D (k ⊗[R] A) (k ⊗[R] D)
    (pointFiberTensorCoefficientMap k R A D) d a

theorem pointFiberTensorDerivationRestriction_unique (d : Derivation k A (k ⊗[R] A))
    (e : Derivation k D (k ⊗[R] D))
    (h : ∀ a, e (algebraMap A D a) = pointFiberTensorCoefficientMap k R A D (d a)) :
    e = pointFiberTensorDerivationRestriction k R A D d := by
  apply EtaleCoefficientLiftEquivalence.etaleCoefficientDerivation_ext k A D (k ⊗[R] D)
  intro a
  exact (h a).trans (pointFiberTensorDerivationRestriction_algebraMap k R A D d a).symm

variable [Algebra.FormallySmooth R A]

def pointFiberRestrictedTangent : Derivation k R k →ₗ[k] Derivation k D (k ⊗[R] D) :=
  (pointFiberTensorDerivationRestriction k R A D).comp (PointFiberTensorLifts.pointFiberTensorDerivation k R A)

theorem pointFiberRestrictedTangent_base (d : Derivation k R k) (r : R) :
    pointFiberRestrictedTangent k R A D d (algebraMap R D r) = d r ⊗ₜ[R] (1 : D) := by
  change pointFiberTensorDerivationRestriction k R A D (PointFiberTensorLifts.pointFiberTensorDerivation k R A d)
    (algebraMap R D r) = _
  rw [IsScalarTower.algebraMap_apply R A D r, pointFiberTensorDerivationRestriction_algebraMap,
    PointFiberTensorLifts.pointFiberTensorDerivation_base, pointFiberTensorCoefficientMap_tmul, map_one]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointFiberTensorRestriction
