import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Abel

/-! # Complex Gaussian -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ComplexGaussian.LocalSectionLifting

noncomputable section

/-! Removing an invertible block from a differential by explicit changes of coordinates. -/

universe u v₁ v₂ v₃ v₄

variable {R : Type u} [CommRing R]
    {A : Type v₁} [AddCommGroup A] [Module R A]
    {B : Type v₂} [AddCommGroup B] [Module R B]
    {C : Type v₃} [AddCommGroup C] [Module R C]
    {D : Type v₄} [AddCommGroup D] [Module R D]

def blockSourceShear (c : A →ₗ[R] D) (d : B ≃ₗ[R] D) : (A × B) ≃ₗ[R] (A × B) where
  toFun x := (x.1, x.2 - d.symm (c x.1))
  invFun x := (x.1, x.2 + d.symm (c x.1))
  left_inv x := by rcases x with ⟨x, y⟩; simp
  right_inv x := by rcases x with ⟨x, y⟩; simp
  map_add' x y := by ext <;> simp [map_add, sub_add_sub_comm]
  map_smul' r x := by ext <;> simp [smul_sub]

def blockTargetShear (b : B →ₗ[R] C) (d : B ≃ₗ[R] D) : (C × D) ≃ₗ[R] (C × D) where
  toFun x := (x.1 - b (d.symm x.2), x.2)
  invFun x := (x.1 + b (d.symm x.2), x.2)
  left_inv x := by rcases x with ⟨x, y⟩; simp
  right_inv x := by rcases x with ⟨x, y⟩; simp
  map_add' x y := by ext <;> simp [map_add, sub_add_sub_comm]
  map_smul' r x := by ext <;> simp [smul_sub]

def blockDifferential (a : A →ₗ[R] C) (b : B →ₗ[R] C) (c : A →ₗ[R] D) (d : B ≃ₗ[R] D) :
    (A × B) →ₗ[R] (C × D) :=
  (a.coprod b).prod (c.coprod d.toLinearMap)

def schurDifferential (a : A →ₗ[R] C) (b : B →ₗ[R] C) (c : A →ₗ[R] D) (d : B ≃ₗ[R] D) :
    A →ₗ[R] C := a - b.comp (d.symm.toLinearMap.comp c)

theorem blockDifferential_normal_form (a : A →ₗ[R] C) (b : B →ₗ[R] C)
    (c : A →ₗ[R] D) (d : B ≃ₗ[R] D) (x : A × B) :
    blockTargetShear b d (blockDifferential a b c d (blockSourceShear c d x)) =
      (schurDifferential a b c d x.1, d x.2) := by
  rcases x with ⟨x, y⟩
  apply Prod.ext
  · change a x + b (y - d.symm (c x)) - b (d.symm (c x + d (y - d.symm (c x)))) =
      a x - b (d.symm (c x))
    simp only [map_sub, map_add,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
    abel
  · simp [blockTargetShear, blockDifferential, blockSourceShear]

theorem blockDifferential_target_coordinates (a : A →ₗ[R] C) (b : B →ₗ[R] C)
    (c : A →ₗ[R] D) (d : B ≃ₗ[R] D) (x : A × B) :
    blockTargetShear b d (blockDifferential a b c d x) =
      (schurDifferential a b c d x.1, d (((blockSourceShear c d).symm x).2)) := by
  have h := blockDifferential_normal_form a b c d ((blockSourceShear c d).symm x)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h

theorem blockDifferential_lift_schur (a : A →ₗ[R] C) (b : B →ₗ[R] C)
    (c : A →ₗ[R] D) (d : B ≃ₗ[R] D) (x : A) :
    blockDifferential a b c d (blockSourceShear c d (x, 0)) = (schurDifferential a b c d x, 0) := by
  apply (blockTargetShear b d).injective
  exact (blockDifferential_normal_form a b c d (x, 0)).trans (by simp [blockTargetShear])

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ComplexGaussian.LocalSectionLifting
