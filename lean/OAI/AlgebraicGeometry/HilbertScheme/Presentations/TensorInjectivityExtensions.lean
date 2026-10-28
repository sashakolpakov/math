import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Tensor Injectivity Extensions -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorInjectivityExtensions

noncomputable section

/-! Tensor injectivity propagates through short exact extensions and
through scalar extension by a flat module. -/

open TensorProduct

universe u v w t z z'
variable {B : Type u} [CommRing B]
variable {K : Type v} [AddCommGroup K] [Module B K]
variable {F : Type w} [AddCommGroup F] [Module B F]
variable {P : Type t} [AddCommGroup P] [Module B P]
variable {N : Type z} [AddCommGroup N] [Module B N]
variable {Q : Type z'} [AddCommGroup Q] [Module B Q]

theorem tensorMap_exchange (f : K →ₗ[B] F) (g : P →ₗ[B] N) (x : P ⊗[B] K) :
    g.rTensor F (f.lTensor P x) = f.lTensor N (g.rTensor K x) := by
  induction x with
  | tmul p k => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem lTensor_injective_of_shortExact (f : K →ₗ[B] F) [Module.Flat B F]
    (i : P →ₗ[B] N) (j : N →ₗ[B] Q) (hi : Function.Injective i)
    (hex : Function.Exact i j) (hj : Function.Surjective j)
    (hP : Function.Injective (f.lTensor P)) (hQ : Function.Injective (f.lTensor Q)) :
    Function.Injective (f.lTensor N) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  have hz : j.rTensor K x = 0 := by
    apply hQ
    rw [map_zero, ← tensorMap_exchange, hx, map_zero]
  obtain ⟨y, rfl⟩ := (rTensor_exact K hex hj x).mp hz
  have hy : f.lTensor P y = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := F) i hi
    rw [map_zero, tensorMap_exchange]
    exact hx
  have hy0 : y = 0 := hP (hy.trans (map_zero _).symm)
  rw [hy0, map_zero]

theorem lTensor_injective_of_flat_scalar_module
    (A : Type t) [CommRing A] [Algebra B A]
    (N : Type z) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower B A N]
    [Module.Flat A N] (f : K →ₗ[B] F) (hf : Function.Injective (f.lTensor A)) :
    Function.Injective (f.lTensor N) := by
  let fA : A ⊗[B] K →ₗ[A] A ⊗[B] F := AlgebraTensorModule.lTensor A A f
  have hfA : Function.Injective fA := hf
  let eK := AlgebraTensorModule.cancelBaseChange B A A N K
  let eF := AlgebraTensorModule.cancelBaseChange B A A N F
  have he (x : N ⊗[A] (A ⊗[B] K)) :
      f.lTensor N (eK x) = eF (fA.lTensor N x) := by
    exact LinearMap.congr_fun (AlgebraTensorModule.lTensor_comp_cancelBaseChange B A A f) x
  intro x y hxy
  apply eK.symm.injective
  apply Module.Flat.lTensor_preserves_injective_linearMap fA hfA
  apply eF.injective
  rw [← he, ← he, eK.apply_symm_apply, eK.apply_symm_apply]
  exact hxy

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorInjectivityExtensions
