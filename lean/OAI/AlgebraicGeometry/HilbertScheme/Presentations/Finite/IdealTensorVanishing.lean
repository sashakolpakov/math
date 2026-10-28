import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.VanishingDescent
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Ideal Tensor Vanishing -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.IdealTensorVanishing

noncomputable section

/-! A finite list of ideal-tensor obstructions which vanish after base
change vanishes over one finite intermediate coefficient algebra. -/

open TensorProduct

universe u v w t z z'
variable {B : Type u} [CommRing B]
variable {M : Type w} [AddCommGroup M] [Module B M]
variable {κ : Type t} [Fintype κ]

theorem tensorPiLeft_lTensor [DecidableEq κ] {N : Type z} {P : Type z'} [AddCommGroup N] [Module B N]
    [AddCommGroup P] [Module B P] (f : N →ₗ[B] P) (x : (κ → M) ⊗[B] N) :
    TensorProduct.piLeft B P (fun _ : κ => M) (f.lTensor (κ → M) x) =
      fun i => f.lTensor M (TensorProduct.piLeft B N (fun _ : κ => M) x i) := by
  classical
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, hx, hy, Pi.add_apply]
    rfl
  | tmul m n => rfl

variable {A : Type v} [CommRing A] [Algebra B A]
variable (C : Subalgebra B A) [Algebra.FiniteType B C]

theorem finite_idealCoefficientTensor_zero_descent (I : Ideal B) (x : κ → M ⊗[B] I)
    (hx : ∀ i, (IdealTensor.BaseChange.idealCoefficientInclusion B A I).lTensor M (x i) = 0) :
    ∃ D : Subalgebra B A, C ≤ D ∧ Algebra.FiniteType B D ∧
      ∀ i, (IdealTensor.BaseChange.idealCoefficientInclusion B D I).lTensor M (x i) = 0 := by
  classical
  let e := TensorProduct.piLeft B I (fun _ : κ => M)
  let z := e.symm x
  have hz : (IdealTensor.BaseChange.idealCoefficientInclusion B A I).lTensor (κ → M) z = 0 := by
    apply (TensorProduct.piLeft B (I.map (algebraMap B A)) (fun _ : κ => M)).injective
    rw [tensorPiLeft_lTensor, map_zero]
    funext i
    have he : TensorProduct.piLeft B I (fun _ : κ => M) z i = x i := congrFun (e.apply_symm_apply x) i
    rw [he]
    exact hx i
  obtain ⟨D, hCD, hD, hzero⟩ := IdealTensor.VanishingDescent.idealCoefficientTensor_zero_finite_descent C I z hz
  refine ⟨D, hCD, hD, fun i => ?_⟩
  have h := congrArg (TensorProduct.piLeft B (I.map (algebraMap B D)) (fun _ : κ => M)) hzero
  rw [tensorPiLeft_lTensor, map_zero] at h
  have he : TensorProduct.piLeft B I (fun _ : κ => M) z i = x i := congrFun (e.apply_symm_apply x) i
  have hi := congrFun h i
  simpa only [he, Pi.zero_apply] using hi

theorem finite_idealTensorBaseChange_zero_descent (I : Ideal B) (x : κ → M ⊗[B] I)
    (hx : ∀ i, IdealTensor.BaseChange.idealTensorBaseChangeMap B A M I (x i) = 0) :
    ∃ D : Subalgebra B A, C ≤ D ∧ Algebra.FiniteType B D ∧
      ∀ i, IdealTensor.BaseChange.idealTensorBaseChangeMap B D M I (x i) = 0 := by
  have hx' (i : κ) : (IdealTensor.BaseChange.idealCoefficientInclusion B A I).lTensor M (x i) = 0 := by
    have h := congrArg (IdealTensor.BaseChange.idealTensorBaseChangeComparison B A M I) (hx i)
    simpa only [IdealTensor.BaseChange.idealTensorBaseChangeMap, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply, map_zero] using h
  obtain ⟨D, hCD, hD, hz⟩ := finite_idealCoefficientTensor_zero_descent C I x hx'
  refine ⟨D, hCD, hD, fun i => ?_⟩
  simp only [IdealTensor.BaseChange.idealTensorBaseChangeMap, LinearMap.comp_apply, hz i, map_zero]

theorem finite_idealTensorObstructions_descend [Module.Flat A (A ⊗[B] M)]
    (I : Ideal B) (x : κ → (IdealTensor.Obstruction.idealTensorMultiplication B B M I).ker) :
    ∃ D : Subalgebra B A, C ≤ D ∧ Algebra.FiniteType B D ∧
      ∀ i, IdealTensor.BaseChange.idealTensorBaseChangeMap B D M I (x i).val = 0 :=
  finite_idealTensorBaseChange_zero_descent C I (fun i => (x i).val)
    (fun i => IdealTensor.BaseChange.idealTensorObstruction_baseChange_zero B A M I (x i))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.IdealTensorVanishing
