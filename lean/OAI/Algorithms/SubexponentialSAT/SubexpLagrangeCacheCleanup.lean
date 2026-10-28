import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheContext
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

namespace OAI.Algorithms

/-! Physical cleanup after the cache's final record reversal. -/

namespace SubexponentialSAT.SubexpLagrangeCacheCleanup

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLagrangeCachePreparation

def ports : List (Fin 256) := [217, 248, 5, 10, 104, 194, 201, 202, 213, 242, 243]
def command : Code := SubexpSetupStorage.clearMany ports

def store (x : Inputs) (current index cache : List Bool) : Store :=
  Function.update (Function.update (Function.update (Function.update (preparedStore x)
    217 current) 248 index) 250 cache) 246 []

theorem output_stacks (x : Inputs) (current index cache : List Bool) (regs : Fin 16 → Bool) :
    (SubexpSetupStorage.clearManyState ports (⟨regs, store x current index cache⟩ : Data)).stacks =
      Function.update (rawStore x) 250 cache := by
  funext k
  rw [SubexpSetupStorage.clearMany_stacks]
  by_cases hk : k ∈ ports
  · simp [ports] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [ports, rawStore]
  · have hne : k ≠ 217 ∧ k ≠ 248 ∧ k ≠ 5 ∧ k ≠ 10 ∧ k ≠ 104 ∧ k ≠ 194 ∧
        k ≠ 201 ∧ k ≠ 202 ∧ k ≠ 213 ∧ k ≠ 242 ∧ k ≠ 243 := by
      simpa [ports] using hk
    rcases hne with ⟨h217, h248, h5, h10, h104, h194, h201, h202, h213, h242, h243⟩
    by_cases h246 : k = 246
    · subst k
      simp [ports, store, rawStore]
    · by_cases h250 : k = 250
      · subst k; simp [ports, store]
      · simp [ite_eq_right hk, store, preparedStore, allocatedStore, cellStore, parameterStore,
          h217, h248, h5, h10, h104, h194, h201, h202,
          h213, h242, h243, h246, h250]

def runtimeBound (x : Inputs) (current index : List Bool) : ℕ :=
  2 * current.length + 2 * index.length + 100 * (primeValue x + 1) * (inputLength x + 1)

theorem cost_le (x : Inputs) (current index cache : List Bool) (regs : Fin 16 → Bool) :
    SubexpSetupStorage.clearManyCost ports (⟨regs, store x current index cache⟩ : Data) ≤
      runtimeBound x current index := by
  have hM : x.modulus.length ≤ inputLength x := by unfold inputLength; omega
  have hB : x.width.length ≤ inputLength x := by unfold inputLength; omega
  have hT : x.reduction.length ≤ inputLength x := by unfold inputLength; omega
  have hpB := Nat.mul_le_mul_left (primeValue x) hB
  simp only [ports, SubexpSetupStorage.clearManyCost, SubexpSetupStorage.clearState,
    store, preparedStore, allocatedStore, cellStore, parameterStore, zeroCell, zeroArray,
    unaryPrime, Function.update_apply, runtimeBound]
  norm_num [Fin.ext_iff, Fin.coe_ofNat_eq_mod, Subexp.BlockCopyProgram.copies_length,
    List.length_replicate]
  nlinarith [Nat.zero_le (primeValue x * inputLength x)]

theorem command_run (x : Inputs) (current index cache : List Bool) :
    ExecutesIn command (runtimeBound x current index) (store x current index cache)
      (Function.update (rawStore x) 250 cache) := by
  intro regs
  let a : Data := ⟨regs, store x current index cache⟩
  let b := SubexpSetupStorage.clearManyState ports a
  have he := SubexpSetupStorage.clearMany_eval ports a
  have hb : b = (⟨b.regs, Function.update (rawStore x) 250 cache⟩ : Data) :=
    congrArg (StructuredProgram.State.mk b.regs) (output_stacks x current index cache regs)
  change Eval command _ a b at he
  rw [hb] at he
  exact ⟨_, b.regs, cost_le x current index cache regs, he⟩

end SubexponentialSAT.SubexpLagrangeCacheCleanup

end OAI.Algorithms
