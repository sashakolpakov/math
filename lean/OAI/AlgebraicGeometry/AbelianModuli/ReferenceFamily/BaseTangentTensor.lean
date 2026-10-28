import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TangentDualScalarTowers
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointFiberTensorLifts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.ScalarExtensionProduct
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorReductionEquiv

/-! # Base Tangent Tensor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BaseTangentTensor

noncomputable section

section

/-! Every chosen affine tangent lift gives an actual product
equivalence for the family's literal pullback along that tangent point.
Its map on original functions is the prescribed linear-coefficient lift. -/

open scoped TensorProduct

variable (k R A : Type) [Field k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra k A] [Algebra R k] [Algebra R A]
    [IsScalarTower k R k] [IsScalarTower k R A] [Algebra.FormallySmooth R A]

local instance tangentProduct_fiberRing : CommRing (k ⊗[R] A) :=
  Algebra.TensorProduct.instCommRing (R := R) (A := k) (B := A)

local instance tangentProduct_productRing : CommRing (DualNumber k ⊗[k] (k ⊗[R] A)) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := k ⊗[R] A)

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] PointFiberTensorLifts.pointFiberTensor_scalarTower

def baseTangentTensorProductEquiv (d : Derivation k R k) :
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
  have := PointFiberTensorLifts.pointFiberTensor_scalarTower k R A
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
  let f := BaseTangentTensorLifts.baseTangentTensorLift k R A (k ⊗[R] A) d
  apply Tensor.ScalarExtensionProduct.tensorScalarExtensionProductEquiv R (DualNumber k) k A
    (DualNumber k ⊗[k] (k ⊗[R] A)) hD hI eT f
  intro a
  exact (Dual.TensorReductionEquiv.dualTensorReductionWithBase_mk k (k ⊗[R] A) hB (f a)).trans
    (BaseTangentTensorLifts.baseTangentTensorLift_reduction k R A (k ⊗[R] A) d a)

theorem baseTangentTensorProductEquiv_original (d : Derivation k R k) (a : A) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    baseTangentTensorProductEquiv k R A d ((1 : DualNumber k) ⊗ₜ[R] a) =
      BaseTangentTensorLifts.baseTangentTensorLift k R A (k ⊗[R] A) d a := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  let qT := BaseTangentTensorLifts.baseTangentProductAlgebra k R (k ⊗[R] A) d
  let : Module R (DualNumber k ⊗[k] (k ⊗[R] A)) := qT.toModule
  let : SMul R (DualNumber k ⊗[k] (k ⊗[R] A)) := qT.toSMul
  have : IsScalarTower R (DualNumber k) (DualNumber k ⊗[k] (k ⊗[R] A)) :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := DualNumber k)
      (A := DualNumber k ⊗[k] (k ⊗[R] A)) rfl
  exact Affine.ScalarExtensionMap.affineScalarExtensionMap_algebraMap R (DualNumber k) A (DualNumber k ⊗[R] A)
    (DualNumber k ⊗[k] (k ⊗[R] A)) (BaseTangentTensorLifts.baseTangentTensorLift k R A (k ⊗[R] A) d) a

theorem baseTangentTensorProductEquiv_coefficients (d : Derivation k R k) (a : A) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    Dual.NumberCoefficients.dualTensorCoefficientEquiv k (k ⊗[R] A)
      (baseTangentTensorProductEquiv k R A d ((1 : DualNumber k) ⊗ₜ[R] a)) =
        PointFiberTensorLifts.pointFiberTensorLift k R A d a := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  rw [baseTangentTensorProductEquiv_original]
  exact BaseTangentTensorLifts.baseTangentTensorLift_coefficients k R A (k ⊗[R] A) d a

end

section

/-! The affine tangent product preserves the actual reduction on
every function of the tensor pullback. Its second coefficients on the
original functions remain the chosen linear tangent lifts. -/

open scoped TensorProduct

variable (k R A : Type) [Field k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra k A] [Algebra R k] [Algebra R A]
    [IsScalarTower k R k] [IsScalarTower k R A]

def baseTangentScalarReduction (d : Derivation k R k) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    (DualNumber k ⊗[R] A) →+* (k ⊗[R] A) := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  have : IsScalarTower R R (DualNumber k) :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := R) (A := DualNumber k) (fun _ => rfl)
  let q : DualNumber k →ₐ[R] k :=
    { (TrivSqZeroExt.fstHom k k k).toRingHom with
      commutes' := TangentDualScalarTowers.baseTangentDualAlgebra_reduction k R d }
  exact (Algebra.TensorProduct.map q (AlgHom.id R A)).toRingHom

omit [Algebra k A] [IsScalarTower k R A] in
theorem baseTangentScalarReduction_tmul (d : Derivation k R k) (c : DualNumber k) (a : A) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    baseTangentScalarReduction k R A d (c ⊗ₜ[R] a) = c.fst ⊗ₜ[R] a := rfl

variable [Algebra.FormallySmooth R A]

theorem baseTangentTensorProductEquiv_original_reduction (d : Derivation k R k) (a : A) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    Dual.TensorReduction.dualTensorReduction k (k ⊗[R] A)
      (baseTangentTensorProductEquiv k R A d ((1 : DualNumber k) ⊗ₜ[R] a)) = (1 : k) ⊗ₜ[R] a :=
  (congrArg TrivSqZeroExt.fst (baseTangentTensorProductEquiv_coefficients k R A d a)).trans
    (PointFiberTensorLifts.pointFiberTensorLift_reduction k R A d a)

theorem baseTangentTensorProductEquiv_reduction (d : Derivation k R k) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    ∀ p : DualNumber k ⊗[R] A,
      Dual.TensorReduction.dualTensorReduction k (k ⊗[R] A) (baseTangentTensorProductEquiv k R A d p) =
        baseTangentScalarReduction k R A d p := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  let e := baseTangentTensorProductEquiv k R A d
  let q := baseTangentScalarReduction k R A d
  intro p
  change Dual.TensorReduction.dualTensorReduction k (k ⊗[R] A) (e p) = q p
  induction p using TensorProduct.inductionOn with
  | add p q' hp hq => simp only [map_add, hp, hq]
  | tmul c a =>
    have hc : e (c ⊗ₜ[R] (1 : A)) =
        algebraMap (DualNumber k) (DualNumber k ⊗[k] (k ⊗[R] A)) c := e.commutes c
    have ha : Dual.TensorReduction.dualTensorReduction k (k ⊗[R] A) (e ((1 : DualNumber k) ⊗ₜ[R] a)) =
        (1 : k) ⊗ₜ[R] a := baseTangentTensorProductEquiv_original_reduction k R A d a
    have hm : c ⊗ₜ[R] a = (c ⊗ₜ[R] (1 : A)) * ((1 : DualNumber k) ⊗ₜ[R] a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    conv_lhs => rw [hm]
    rw [map_mul, map_mul, hc, Dual.TensorReductionEquiv.dualTensorReduction_algebraMap, ha]
    change (c.fst ⊗ₜ[R] (1 : A)) * ((1 : k) ⊗ₜ[R] a) = c.fst ⊗ₜ[R] a
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem baseTangentTensorProductEquiv_original_snd (d : Derivation k R k) (a : A) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    (Dual.NumberCoefficients.dualTensorCoefficientEquiv k (k ⊗[R] A)
      (baseTangentTensorProductEquiv k R A d ((1 : DualNumber k) ⊗ₜ[R] a))).snd =
        PointFiberTensorLifts.pointFiberTensorDerivation k R A d a :=
  (congrArg TrivSqZeroExt.snd (baseTangentTensorProductEquiv_coefficients k R A d a)).trans
    (PointFiberTensorLifts.pointFiberTensorLift_snd k R A d a)

end

/-! Scalar extension of an original algebra morphism along the actual
base tangent commutes with its original fixed-fiber reduction. -/

open scoped TensorProduct

variable (k R A B : Type) [Field k] [CommRing R] [CommRing A] [CommRing B]
    [Algebra k R] [Algebra R k] [IsScalarTower k R k] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B)

def pointFiberTensorMorphism : (k ⊗[R] A) →ₐ[k] (k ⊗[R] B) :=
  Algebra.TensorProduct.map (AlgHom.id k k) f

def baseTangentTensorMorphism (d : Derivation k R k) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    (DualNumber k ⊗[R] A) →ₐ[DualNumber k] (DualNumber k ⊗[R] B) := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  have : IsScalarTower R (DualNumber k) (DualNumber k) :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := DualNumber k) (A := DualNumber k) (fun _ => rfl)
  exact Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) f

theorem baseTangentTensorMorphism_reduction (d : Derivation k R k) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    ∀ p, baseTangentScalarReduction k R B d (baseTangentTensorMorphism k R A B f d p) =
      pointFiberTensorMorphism k R A B f (baseTangentScalarReduction k R A d p) := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  intro p
  induction p using TensorProduct.inductionOn with
  | add p q hp hq => simp only [map_add, hp, hq]
  | tmul c a => rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BaseTangentTensor
