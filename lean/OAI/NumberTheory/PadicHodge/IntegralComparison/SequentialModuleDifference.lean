import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.Pi

/-! # Sequential Module Difference -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SequentialModuleDifference

noncomputable section

/-!
# IntegralComparison: the difference map for a surjective inverse sequence of modules
-/

universe u v

variable (R : Type u) [Ring R] (M : ℕ → Type v)
  [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  (t : ∀ n, M (n + 1) →ₗ[R] M n)

def difference : (∀ n, M n) →ₗ[R] (∀ n, M n) where
  toFun x n := x n - t n (x (n + 1))
  map_add' x y := by
    funext n
    change (x n + y n) - t n (x (n + 1) + y (n + 1)) = _
    rw [map_add]
    exact add_sub_add_comm _ _ _ _
  map_smul' r x := by
    funext n
    change r • x n - t n (r • x (n + 1)) = r • (x n - t n (x (n + 1)))
    rw [map_smul, smul_sub]

theorem difference_eq_zero_iff (x : ∀ n, M n) :
    difference R M t x = 0 ↔ ∀ n, t n (x (n + 1)) = x n := by
  constructor
  · intro h n
    exact (sub_eq_zero.mp (congrFun h n)).symm
  · intro h
    funext n
    exact sub_eq_zero.mpr (h n).symm

variable (ht : ∀ n, Function.Surjective (t n))

def preimage (y : ∀ n, M n) : ∀ n, M n
  | 0 => 0
  | n + 1 => (ht n (preimage y n - y n)).choose

theorem difference_preimage (y : ∀ n, M n) : difference R M t (SequentialModuleDifference.preimage R M t ht y) = y := by
  funext n
  change SequentialModuleDifference.preimage R M t ht y n - t n ((ht n (SequentialModuleDifference.preimage R M t ht y n - y n)).choose) = y n
  rw [(ht n (SequentialModuleDifference.preimage R M t ht y n - y n)).choose_spec]
  exact sub_sub_cancel _ _

include ht in
theorem surjective : Function.Surjective (difference R M t) :=
  fun y => ⟨SequentialModuleDifference.preimage R M t ht y, difference_preimage R M t ht y⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SequentialModuleDifference
