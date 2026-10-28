import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BaseTangentTensorLifts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorReductionEquiv

/-! # Tangent Dual Scalar Towers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TangentDualScalarTowers

noncomputable section

/-! The actual dual-number base map supplied by a tangent derivation
has the prescribed reduction. Its scalar action and the coefficient
reduction therefore form the original base-point tower. -/

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k]

theorem baseTangentDualAlgebra_reduction (d : Derivation k R k) (r : R) :
    letI := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    (algebraMap R (DualNumber k) r).fst = algebraMap R k r :=
  AlgHom.congr_fun (((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R k).symm d).property) r

theorem baseTangentDualReductionTower (d : Derivation k R k) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    letI : Algebra (DualNumber k) k := (TrivSqZeroExt.fstHom k k k).toRingHom.toAlgebra
    IsScalarTower R (DualNumber k) k := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  let : Algebra (DualNumber k) k := (TrivSqZeroExt.fstHom k k k).toRingHom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq (R := R) (S := DualNumber k) (A := k)
    (fun r => (baseTangentDualAlgebra_reduction k R d r).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TangentDualScalarTowers
