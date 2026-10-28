import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BaseTangentTensor

/-! # Tangent Coefficient Product -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TangentCoefficientProduct

noncomputable section

section

/-! Reduction of a product map on a tangent pullback is determined
by its values on the original affine functions and the full dual-number
base action. -/

open scoped TensorProduct

variable (k R A : Type) [Field k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra R k] [Algebra R A] [IsScalarTower k R k]

theorem tangentProduct_reduction_of_original (d : Derivation k R k) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    ∀ e : (DualNumber k ⊗[R] A) →ₐ[DualNumber k] (DualNumber k ⊗[k] (k ⊗[R] A)),
      (∀ a, Dual.TensorReduction.dualTensorReduction k (k ⊗[R] A) (e ((1 : DualNumber k) ⊗ₜ[R] a)) = (1 : k) ⊗ₜ[R] a) →
      ∀ p, Dual.TensorReduction.dualTensorReduction k (k ⊗[R] A) (e p) = BaseTangentTensor.baseTangentScalarReduction k R A d p := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  intro e h p
  let q := BaseTangentTensor.baseTangentScalarReduction k R A d
  change Dual.TensorReduction.dualTensorReduction k (k ⊗[R] A) (e p) = q p
  induction p using TensorProduct.inductionOn with
  | add p q' hp hq => simp only [map_add, hp, hq]
  | tmul c a =>
    have hc : e (c ⊗ₜ[R] (1 : A)) =
        algebraMap (DualNumber k) (DualNumber k ⊗[k] (k ⊗[R] A)) c := e.commutes c
    have hm : c ⊗ₜ[R] a = (c ⊗ₜ[R] (1 : A)) * ((1 : DualNumber k) ⊗ₜ[R] a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    conv_lhs => rw [hm]
    rw [map_mul, map_mul, hc, Dual.TensorReductionEquiv.dualTensorReduction_algebraMap, h]
    change (c.fst ⊗ₜ[R] (1 : A)) * ((1 : k) ⊗ₜ[R] a) = c.fst ⊗ₜ[R] a
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end

/-! Any prescribed affine lift of a base tangent constructs an
actual product equivalence. The original lift is retained, so this also
applies to the uniquely restricted lifts on common affine opens. -/

open scoped TensorProduct

variable (k R A : Type) [Field k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra k A] [Algebra R k] [Algebra R A]
    [IsScalarTower k R k] [Algebra.FormallySmooth R A]

local instance tangentCoefficient_fiberRing : CommRing (k ⊗[R] A) :=
  Algebra.TensorProduct.instCommRing (R := R) (A := k) (B := A)

local instance tangentCoefficient_productRing : CommRing (DualNumber k ⊗[k] (k ⊗[R] A)) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := k ⊗[R] A)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (d : Derivation k R k) (f : A →ₐ[k] DualNumber (k ⊗[R] A))
    (hf : ∀ a, (f a).fst = (1 : k) ⊗ₜ[R] a)
    (hb : ∀ r, f (algebraMap R A r) = Dual.NumberCoefficients.dualNumberRingMap (algebraMap k (k ⊗[R] A))
      (((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R k).symm d).val r))

def tangentCoefficientProductEquiv :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    (DualNumber k ⊗[R] A) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] (k ⊗[R] A)) := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  let dSelf : Algebra (DualNumber k) (DualNumber k) := inferInstance
  let : Module (DualNumber k) (DualNumber k) := dSelf.toModule
  let : SMul (DualNumber k) (DualNumber k) := dSelf.toSMul
  let dTarget : Algebra (DualNumber k) (DualNumber k ⊗[k] (k ⊗[R] A)) := inferInstance
  let : Module (DualNumber k) (DualNumber k ⊗[k] (k ⊗[R] A)) := dTarget.toModule
  let : SMul (DualNumber k) (DualNumber k ⊗[k] (k ⊗[R] A)) := dTarget.toSMul
  let : Algebra (DualNumber k) k := (TrivSqZeroExt.fstHom k k k).toRingHom.toAlgebra
  have : IsScalarTower R (DualNumber k) k := TangentDualScalarTowers.baseTangentDualReductionTower k R d
  let qT := BaseTangentTensorLifts.baseTangentProductAlgebra k R (k ⊗[R] A) d
  let : Module R (DualNumber k ⊗[k] (k ⊗[R] A)) := qT.toModule
  let : SMul R (DualNumber k ⊗[k] (k ⊗[R] A)) := qT.toSMul
  have : IsScalarTower R (DualNumber k) (DualNumber k ⊗[k] (k ⊗[R] A)) :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := DualNumber k)
      (A := DualNumber k ⊗[k] (k ⊗[R] A)) rfl
  have hD : Function.Surjective (algebraMap (DualNumber k) k) := fun c => ⟨⟨c, 0⟩, rfl⟩
  have hI : RingHom.ker (algebraMap (DualNumber k) k) *
      RingHom.ker (algebraMap (DualNumber k) k) = ⊥ := Dual.TensorReduction.dualScalarReductionIdeal_square k
  have hB : ∀ c : DualNumber k,
      algebraMap (DualNumber k) (k ⊗[R] A) c = algebraMap k (k ⊗[R] A) c.fst := fun _ => rfl
  let eT := Dual.TensorReductionEquiv.dualTensorReductionWithBase k (k ⊗[R] A) hB
  let fT := Dual.CoefficientLiftTensorMap.dualCoefficientLiftTensorMap k R A (k ⊗[R] A) (fun _ => rfl) f hb
  apply Tensor.ScalarExtensionProduct.tensorScalarExtensionProductEquiv R (DualNumber k) k A
    (DualNumber k ⊗[k] (k ⊗[R] A)) hD hI eT fT
  intro a
  exact (Dual.TensorReductionEquiv.dualTensorReductionWithBase_mk k (k ⊗[R] A) hB (fT a)).trans
    ((Dual.CoefficientLiftTensorMap.dualCoefficientLiftTensorMap_reduction k R A (k ⊗[R] A) (fun _ => rfl) f hb a).trans (hf a))

theorem tangentCoefficientProductEquiv_coefficients (a : A) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    Dual.NumberCoefficients.dualTensorCoefficientEquiv k (k ⊗[R] A)
      (tangentCoefficientProductEquiv k R A d f hf hb ((1 : DualNumber k) ⊗ₜ[R] a)) = f a := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  let qT := BaseTangentTensorLifts.baseTangentProductAlgebra k R (k ⊗[R] A) d
  let : Module R (DualNumber k ⊗[k] (k ⊗[R] A)) := qT.toModule
  let : SMul R (DualNumber k ⊗[k] (k ⊗[R] A)) := qT.toSMul
  have : IsScalarTower R (DualNumber k) (DualNumber k ⊗[k] (k ⊗[R] A)) :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := DualNumber k)
      (A := DualNumber k ⊗[k] (k ⊗[R] A)) rfl
  let fT := Dual.CoefficientLiftTensorMap.dualCoefficientLiftTensorMap k R A (k ⊗[R] A) (fun _ => rfl) f hb
  have he : tangentCoefficientProductEquiv k R A d f hf hb ((1 : DualNumber k) ⊗ₜ[R] a) = fT a :=
    Affine.ScalarExtensionMap.affineScalarExtensionMap_algebraMap R (DualNumber k) A (DualNumber k ⊗[R] A)
      (DualNumber k ⊗[k] (k ⊗[R] A)) fT a
  exact (congrArg (Dual.NumberCoefficients.dualTensorCoefficientEquiv k (k ⊗[R] A)) he).trans
    (Dual.CoefficientLiftTensorMap.dualCoefficientLiftTensorMap_coefficients k R A (k ⊗[R] A) (fun _ => rfl) f hb a)

theorem tangentCoefficientProductEquiv_reduction :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    ∀ p, Dual.TensorReduction.dualTensorReduction k (k ⊗[R] A) (tangentCoefficientProductEquiv k R A d f hf hb p) =
      BaseTangentTensor.baseTangentScalarReduction k R A d p := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  apply tangentProduct_reduction_of_original k R A d
    (tangentCoefficientProductEquiv k R A d f hf hb).toAlgHom
  intro a
  exact (congrArg TrivSqZeroExt.fst (tangentCoefficientProductEquiv_coefficients k R A d f hf hb a)).trans
    (hf a)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TangentCoefficientProduct
