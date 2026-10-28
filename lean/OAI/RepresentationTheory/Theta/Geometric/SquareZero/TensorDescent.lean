import OAI.RepresentationTheory.Theta.Geometric.SquareZero.Subalgebra
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Tensor Descent -/

namespace OAI.RepresentationTheory.Theta.Geometric.SquareZero.TensorDescent

noncomputable section

section

/-! Flatness over the complex field descends a tensor coefficient whose
reduction is one to the split square-zero subalgebra. -/

open scoped TensorProduct

variable {M R S B : Type*} [AddCommGroup M] [Module ℂ M] [Module ℂᵐᵒᵖ M]
    [IsCentralScalar ℂ M] [CommRing R] [Algebra ℂ R]
    [CommRing S] [Algebra ℂ S] [CommRing B] [Algebra ℂ B]

theorem squareZeroTensorMap_injective [Nontrivial R]
    (i : M →ₗ[ℂ] R) (hi : Function.Injective i) (hsq : ∀ x y, i x * i y = 0) :
    Function.Injective (Algebra.TensorProduct.map (Subalgebra.squareZeroSubalgebraMap i hsq)
      (AlgHom.id ℂ B)) :=
  Module.Flat.rTensor_preserves_injective_linearMap
    (Subalgebra.squareZeroSubalgebraMap i hsq).toLinearMap (Subalgebra.squareZeroSubalgebraMap_injective i hi hsq)

theorem squareZeroTensorMap_inr (i : M →ₗ[ℂ] R) (hsq : ∀ x y, i x * i y = 0)
    (x : M ⊗[ℂ] B) :
    Algebra.TensorProduct.map (Subalgebra.squareZeroSubalgebraMap i hsq) (AlgHom.id ℂ B)
      ((TrivSqZeroExt.inrHom ℂ M).rTensor B x) = i.rTensor B x := by
  have h : (Subalgebra.squareZeroSubalgebraMap i hsq).toLinearMap.comp
      (TrivSqZeroExt.inrHom ℂ M) = i := by
    ext m
    change algebraMap ℂ R 0 + i m = i m
    rw [map_zero, zero_add]
  have ht := congrArg (fun f : M →ₗ[ℂ] R => f.rTensor B x) h
  rw [LinearMap.rTensor_comp] at ht
  exact ht

theorem squareZeroTensor_exists_lift_of_reduction_one
    (i : M →ₗ[ℂ] R) (hsq : ∀ x y, i x * i y = 0) (q : R →ₐ[ℂ] S)
    (he : Function.Exact i q.toLinearMap) (x : R ⊗[ℂ] B)
    (hx : Algebra.TensorProduct.map q (AlgHom.id ℂ B) x = 1) :
    ∃ y : TrivSqZeroExt ℂ M ⊗[ℂ] B,
      Algebra.TensorProduct.map (Subalgebra.squareZeroSubalgebraMap i hsq) (AlgHom.id ℂ B) y = x := by
  have hk : q.toLinearMap.rTensor B (x - 1) = 0 := by
    change Algebra.TensorProduct.map q (AlgHom.id ℂ B) (x - 1) = 0
    rw [map_sub, hx, map_one, sub_self]
  have ht := Module.Flat.rTensor_exact B he
  obtain ⟨m, hm⟩ := (ht (x - 1)).mp hk
  refine ⟨1 + (TrivSqZeroExt.inrHom ℂ M).rTensor B m, ?_⟩
  rw [map_add, map_one, squareZeroTensorMap_inr, hm, add_sub_cancel]

end

/-! Normalized regular units descend across the injected split
square-zero subalgebra. No flatness of that algebra injection is used. -/

open scoped TensorProduct

variable {M R S B : Type*} [AddCommGroup M] [Module ℂ M] [Module ℂᵐᵒᵖ M]
    [IsCentralScalar ℂ M] [CommRing R] [Algebra ℂ R] [Nontrivial R]
    [CommRing S] [Algebra ℂ S] [CommRing B] [Algebra ℂ B]

theorem squareZeroTensor_exists_unit_lift_of_reduction_one
    (i : M →ₗ[ℂ] R) (hi : Function.Injective i) (hsq : ∀ x y, i x * i y = 0)
    (q : R →ₐ[ℂ] S) (he : Function.Exact i q.toLinearMap) (x : (R ⊗[ℂ] B)ˣ)
    (hx : Algebra.TensorProduct.map q (AlgHom.id ℂ B) (x : R ⊗[ℂ] B) = 1) :
    ∃! y : (TrivSqZeroExt ℂ M ⊗[ℂ] B)ˣ,
      Algebra.TensorProduct.map (Subalgebra.squareZeroSubalgebraMap i hsq) (AlgHom.id ℂ B)
        (y : TrivSqZeroExt ℂ M ⊗[ℂ] B) = x := by
  have hx' : Algebra.TensorProduct.map q (AlgHom.id ℂ B) (↑x⁻¹ : R ⊗[ℂ] B) = 1 := by
    change Algebra.TensorProduct.map q (AlgHom.id ℂ B) x.inv = 1
    have h := congrArg (Algebra.TensorProduct.map q (AlgHom.id ℂ B)) x.val_inv
    simpa only [map_mul, hx, one_mul, map_one] using h
  obtain ⟨y, hy⟩ := squareZeroTensor_exists_lift_of_reduction_one i hsq q he _ hx
  obtain ⟨z, hz⟩ := squareZeroTensor_exists_lift_of_reduction_one i hsq q he _ hx'
  have hinj := squareZeroTensorMap_injective (B := B) i hi hsq
  have hyz : y * z = 1 := by
    apply hinj
    rw [map_mul, hy, hz, map_one]
    exact x.val_inv
  let u : (TrivSqZeroExt ℂ M ⊗[ℂ] B)ˣ := ⟨y, z, hyz, (mul_comm z y).trans hyz⟩
  refine ⟨u, hy, ?_⟩
  intro v hv
  exact Units.ext (hinj (hv.trans hy.symm))

end

end OAI.RepresentationTheory.Theta.Geometric.SquareZero.TensorDescent
