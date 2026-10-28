import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OpenDiagram
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointFiberTensorLifts

/-! # Affine Tangent Lifts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.AffineTangentLifts

noncomputable section

/-! The smooth coordinate algebras of the family's actual affine
opens carry chosen tangent lifts into their actual fixed-fiber tensor
coordinates, with exact reduction and base-tangent formulas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (X : Over (Spec (.of R)))

abbrev familyAffineRing (V : X.left.affineOpens) : CommAlgCat R :=
  HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra R ((Affine.OpenDiagram.familyAffineOpenDiagram X).obj V)

@[instance_reducible]
def familyAffineCoefficientAlgebra (V : X.left.affineOpens) : Algebra k (familyAffineRing R X V) :=
  ((algebraMap R (familyAffineRing R X V)).comp (algebraMap k R)).toAlgebra

attribute [local instance 50] familyAffineCoefficientAlgebra

omit [Algebra R k] [IsScalarTower k R k] in
theorem familyAffineCoefficientTower (V : X.left.affineOpens) :
    IsScalarTower k R (familyAffineRing R X V) := IsScalarTower.of_algebraMap_eq' rfl

local instance familyAffineFiberTensor_commRing (V : X.left.affineOpens) :
    CommRing (k ⊗[R] familyAffineRing R X V) :=
  Algebra.TensorProduct.instCommRing (R := R) (A := k) (B := familyAffineRing R X V)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable [Smooth X.hom]

def familyAffineTangentDerivation (V : X.left.affineOpens) :
    Derivation k R k →ₗ[k] Derivation k (familyAffineRing R X V) (k ⊗[R] familyAffineRing R X V) := by
  have := familyAffineCoefficientTower k R X V
  have : Algebra.Smooth R (familyAffineRing R X V) := Affine.OpenDiagram.familyAffineCoordinate_smooth R X V
  exact PointFiberTensorLifts.pointFiberTensorDerivation k R (familyAffineRing R X V)

def familyAffineTangentLift (V : X.left.affineOpens) (d : Derivation k R k) :
    familyAffineRing R X V →ₐ[k] DualNumber (k ⊗[R] familyAffineRing R X V) := by
  have := familyAffineCoefficientTower k R X V
  have : Algebra.Smooth R (familyAffineRing R X V) := Affine.OpenDiagram.familyAffineCoordinate_smooth R X V
  exact PointFiberTensorLifts.pointFiberTensorLift k R (familyAffineRing R X V) d

theorem familyAffineTangentLift_snd (V : X.left.affineOpens) (d : Derivation k R k)
    (a : familyAffineRing R X V) :
    (familyAffineTangentLift k R X V d a).snd = familyAffineTangentDerivation k R X V d a := by
  have := familyAffineCoefficientTower k R X V
  have : Algebra.Smooth R (familyAffineRing R X V) := Affine.OpenDiagram.familyAffineCoordinate_smooth R X V
  exact PointFiberTensorLifts.pointFiberTensorLift_snd k R (familyAffineRing R X V) d a

theorem familyAffineTangentLift_reduction (V : X.left.affineOpens) (d : Derivation k R k)
    (a : familyAffineRing R X V) :
    (familyAffineTangentLift k R X V d a).fst = (1 : k) ⊗ₜ[R] a := by
  have := familyAffineCoefficientTower k R X V
  have : Algebra.Smooth R (familyAffineRing R X V) := Affine.OpenDiagram.familyAffineCoordinate_smooth R X V
  exact PointFiberTensorLifts.pointFiberTensorLift_reduction k R (familyAffineRing R X V) d a

theorem familyAffineTangentDerivation_base (V : X.left.affineOpens) (d : Derivation k R k) (r : R) :
    familyAffineTangentDerivation k R X V d (algebraMap R (familyAffineRing R X V) r) =
      d r ⊗ₜ[R] (1 : familyAffineRing R X V) := by
  have := familyAffineCoefficientTower k R X V
  have : Algebra.Smooth R (familyAffineRing R X V) := Affine.OpenDiagram.familyAffineCoordinate_smooth R X V
  exact PointFiberTensorLifts.pointFiberTensorDerivation_base k R (familyAffineRing R X V) d r

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.AffineTangentLifts
