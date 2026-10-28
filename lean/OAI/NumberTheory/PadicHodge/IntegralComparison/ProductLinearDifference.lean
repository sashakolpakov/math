import OAI.NumberTheory.PadicHodge.IntegralComparison.SequentialModuleDifference
import Mathlib.LinearAlgebra.Pi

/-! # Product Linear Difference -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProductLinearDifference

noncomputable section

/-!
# IntegralComparison: transporting a countable difference map through component equivalences
-/

universe u v w

variable (R : Type u) [Ring R] (M : ℕ → Type v) (N : ℕ → Type w)
  [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  (e : ∀ n, M n ≃ₗ[R] N n) (t : ∀ n, M (n + 1) →ₗ[R] M n)

def transition (n : ℕ) : N (n + 1) →ₗ[R] N n :=
  (e n).toLinearMap.comp ((t n).comp (e (n + 1)).symm.toLinearMap)

def transport (d : (∀ n, M n) →ₗ[R] ∀ n, M n) : (∀ n, N n) →ₗ[R] ∀ n, N n :=
  (LinearEquiv.piCongrRight e).toLinearMap.comp
    (d.comp (LinearEquiv.piCongrRight e).symm.toLinearMap)

theorem transport_apply (d : (∀ n, M n) →ₗ[R] ∀ n, M n)
    (hd : ∀ x n, d x n = x n - t n (x (n + 1))) (y : ∀ n, N n) (n : ℕ) :
    transport R M N e d y n = y n - transition R M N e t n (y (n + 1)) := by
  change e n (d (fun m => (e m).symm (y m)) n) = _
  rw [hd, map_sub, LinearEquiv.apply_symm_apply]
  rfl

theorem transport_eq (d : (∀ n, M n) →ₗ[R] ∀ n, M n)
    (hd : ∀ x n, d x n = x n - t n (x (n + 1))) :
    transport R M N e d = SequentialModuleDifference.difference R N (transition R M N e t) := by
  apply LinearMap.ext
  intro y
  exact funext (transport_apply R M N e t d hd y)

def compatible : Submodule R (∀ n, N n) :=
  LinearMap.ker (SequentialModuleDifference.difference R N (transition R M N e t))

theorem mem_compatible (y : ∀ n, N n) : y ∈ compatible R M N e t ↔
    ∀ n, transition R M N e t n (y (n + 1)) = y n :=
  SequentialModuleDifference.difference_eq_zero_iff R N (transition R M N e t) y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProductLinearDifference
