import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.Obstruction

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.BaseChange

noncomputable section

/-! Ideal-tensor obstructions map naturally to the obstruction for the
extended ideal after coefficient base change. -/

open TensorProduct

universe u v w
variable (B : Type u) [CommRing B] (A : Type v) [CommRing A] [Algebra B A]
variable (M : Type w) [AddCommGroup M] [Module B M]

def idealCoefficientInclusion (I : Ideal B) : I →ₗ[B] I.map (algebraMap B A) where
  toFun r := ⟨algebraMap B A r.val, Ideal.mem_map_of_mem _ r.property⟩
  map_add' r s := Subtype.ext (map_add (algebraMap B A) r.val s.val)
  map_smul' r s := by
    apply Subtype.ext
    change algebraMap B A (r * s.val) = r • algebraMap B A s.val
    rw [Algebra.smul_def, map_mul]

def idealTensorBaseChangeComparison (I : Ideal B) :
    ((A ⊗[B] M) ⊗[A] I.map (algebraMap B A)) ≃ₗ[B]
      M ⊗[B] I.map (algebraMap B A) :=
  ((TensorProduct.comm A (A ⊗[B] M) (I.map (algebraMap B A))).restrictScalars B).trans
    (((AlgebraTensorModule.cancelBaseChange B A A (I.map (algebraMap B A)) M).restrictScalars B).trans
      (TensorProduct.comm B (I.map (algebraMap B A)) M))

def idealTensorBaseChangeMap (I : Ideal B) :
    M ⊗[B] I →ₗ[B] (A ⊗[B] M) ⊗[A] I.map (algebraMap B A) :=
  (idealTensorBaseChangeComparison B A M I).symm.toLinearMap.comp
    ((idealCoefficientInclusion B A I).lTensor M)

theorem idealTensorBaseChangeMap_tmul (I : Ideal B) (m : M) (r : I) :
    idealTensorBaseChangeMap B A M I (m ⊗ₜ[B] r) =
      ((1 : A) ⊗ₜ[B] m) ⊗ₜ[A] idealCoefficientInclusion B A I r := by
  apply (idealTensorBaseChangeComparison B A M I).injective
  simp [idealTensorBaseChangeMap, idealTensorBaseChangeComparison]

theorem idealTensorBaseChangeMap_multiplication (I : Ideal B) (x : M ⊗[B] I) :
    Obstruction.idealTensorMultiplication A A (A ⊗[B] M) (I.map (algebraMap B A))
        (idealTensorBaseChangeMap B A M I x) =
      (1 : A) ⊗ₜ[B] Obstruction.idealTensorMultiplication B B M I x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  | tmul m r =>
    rw [idealTensorBaseChangeMap_tmul, Obstruction.idealTensorMultiplication_tmul, Obstruction.idealTensorMultiplication_tmul]
    simp [idealCoefficientInclusion, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]

theorem idealTensorObstruction_baseChange_zero (I : Ideal B)
    [Module.Flat A (A ⊗[B] M)] (x : (Obstruction.idealTensorMultiplication B B M I).ker) :
    idealTensorBaseChangeMap B A M I x.val = 0 := by
  apply Obstruction.idealTensorMultiplication_injective A A (A ⊗[B] M) (I.map (algebraMap B A))
  rw [map_zero, idealTensorBaseChangeMap_multiplication, x.property, TensorProduct.tmul_zero]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.BaseChange
