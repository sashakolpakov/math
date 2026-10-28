import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Pi

/-! # Sequential Module -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SequentialModule.SequentialModuleDifference

noncomputable section

/-!
# The difference map of a surjective sequential module system

For successive maps `t n: M (n+1) → M n`, the difference map sends a
sequence `x` to `x n - t n (x (n+1))`. If every transition is surjective,
recursive lifting solves this equation for every right-hand side.
-/

open _root_.CategoryTheory

universe u v

variable (R : Type u) [Ring R] (M : ℕ → Type v)
  [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  (t : ∀ n, M (n + 1) →ₗ[R] M n)

def shift : (∀ n, M n) →ₗ[R] (∀ n, M n) where
  toFun x n := t n (x (n + 1))
  map_add' x y := funext (fun n => (t n).map_add (x (n + 1)) (y (n + 1)))
  map_smul' r x := funext (fun n => (t n).map_smul r (x (n + 1)))

def difference : (∀ n, M n) →ₗ[R] (∀ n, M n) := LinearMap.id - shift R M t

theorem difference_apply (x : ∀ n, M n) (n : ℕ) :
    difference R M t x n = x n - t n (x (n + 1)) := rfl

variable (ht : ∀ n, Function.Surjective (t n))

def lift (y : ∀ n, M n) : ∀ n, M n
  | 0 => 0
  | n + 1 => Classical.choose (ht n (lift y n - y n))

theorem transition_lift (y : ∀ n, M n) (n : ℕ) :
    t n (SequentialModuleDifference.lift R M t ht y (n + 1)) = SequentialModuleDifference.lift R M t ht y n - y n :=
  Classical.choose_spec (ht n (SequentialModuleDifference.lift R M t ht y n - y n))

theorem difference_lift (y : ∀ n, M n) : difference R M t (SequentialModuleDifference.lift R M t ht y) = y := by
  ext n
  rw [difference_apply, transition_lift, sub_sub_cancel]

include ht in
theorem surjective : Function.Surjective (difference R M t) :=
  fun y => ⟨SequentialModuleDifference.lift R M t ht y, difference_lift R M t ht y⟩

include ht in
theorem shortExact : (difference R M t).shortComplexKer.ShortExact :=
  LinearMap.shortExact_shortComplexKer (surjective R M t ht)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SequentialModule.SequentialModuleDifference
