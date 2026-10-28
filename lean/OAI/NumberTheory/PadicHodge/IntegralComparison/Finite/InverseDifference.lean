import OAI.NumberTheory.PadicHodge.IntegralComparison.SequentialModuleDifference
import Mathlib

/-! # Inverse Difference -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.InverseDifference

noncomputable section

/-!
# IntegralComparison: finite inverse systems have surjective countable difference maps

Every finite set of difference equations has a backward solution. Compactness
of the product of finite discrete modules gives a simultaneous solution.
-/

universe u v

variable (R : Type u) [Ring R] (M : ℕ → Type v)
  [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  (t : ∀ n, M (n + 1) →ₗ[R] M n)

def segment (y : ∀ n, M n) : (n len : ℕ) → M n
  | _, 0 => 0
  | n, len + 1 => y n + t n (segment y (n + 1) len)

def finiteSolution (y : ∀ n, M n) (N : ℕ) : ∀ n, M n := fun n => InverseDifference.segment R M t y n (N - n)

theorem partial_difference (y : ∀ n, M n) (N n : ℕ) (hn : n < N) :
    finiteSolution R M t y N n - t n (finiteSolution R M t y N (n + 1)) = y n := by
  have h : N - n = N - (n + 1) + 1 := by omega
  change InverseDifference.segment R M t y n (N - n) - t n (InverseDifference.segment R M t y (n + 1) (N - (n + 1))) = y n
  rw [h]
  exact add_sub_cancel_right _ _

theorem surjective [∀ n, Finite (M n)] : Function.Surjective (SequentialModuleDifference.difference R M t) := by
  classical
  let (n : ℕ) : TopologicalSpace (M n) := ⊥
  let (n : ℕ) : DiscreteTopology (M n) := ⟨rfl⟩
  let (n : ℕ) : CompactSpace (M n) := inferInstance
  intro y
  have hc (n : ℕ) : IsClosed {x : ∀ n, M n | x n - t n (x (n + 1)) = y n} := by
    apply isClosed_eq _ continuous_const
    exact (continuous_of_discreteTopology : Continuous (fun z : M n × M (n + 1) => z.1 - t n z.2)).comp
      ((continuous_apply n).prodMk (continuous_apply (n + 1)))
  have hfin (s : Finset ℕ) : (⋂ n ∈ s, {x : ∀ n, M n | x n - t n (x (n + 1)) = y n}).Nonempty := by
    refine ⟨finiteSolution R M t y (s.sup id + 1), Set.mem_iInter.mpr (fun n => Set.mem_iInter.mpr (fun hn => ?_))⟩
    exact partial_difference R M t y (s.sup id + 1) n (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))
  obtain ⟨x, hx⟩ := CompactSpace.iInter_nonempty hc hfin
  exact ⟨x, funext (fun n => Set.mem_iInter.mp hx n)⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.InverseDifference
