import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchStorage
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram

namespace OAI.Algorithms

/-! Size bounds for the actual storage instructions in the basis batch. -/

namespace SubexponentialSAT.Subexp.LocalBasisBatchProgram

open BitProgram StructuredCalls

theorem eval_stack_length_le {r s : ℕ} {code : Cmd r s} {steps : ℕ}
    {a b : State r s} (h : Eval code steps a b) (j : Fin s) :
    (b.stacks j).length ≤ (a.stacks j).length + steps := by
  exact SequentialProgram.trace_stack_length_le (compiled_trace h j j) j

theorem clearManyCost_le (ports : List (Fin 128)) (a : Data) (B : ℕ)
    (hb : ∀ j ∈ ports, (a.stacks j).length ≤ B) :
    clearManyCost ports a ≤ ports.length * (2 * B + 3) := by
  induction ports generalizing a with
  | nil => simp [clearManyCost]
  | cons j js ih =>
      have hfirst := hb j (by simp)
      have hrest : ∀ k ∈ js, ((clearState j a).stacks k).length ≤ B := by
        intro k hk
        by_cases hkj : k = j
        · subst k
          simp [clearState, StackRoutines.clearStacks]
        · simpa [clearState, StackRoutines.clearStacks, hkj] using hb k (by simp [hk])
      have htail := ih (clearState j a) hrest
      change 2 * (a.stacks j).length + 3 + clearManyCost js (clearState j a) ≤
        (js.length + 1) * (2 * B + 3)
      nlinarith only [htail, hfirst]

theorem copyManyCost_le (pairs : List (Fin 128 × Fin 128)) (a : Data) (B : ℕ)
    (hdisjoint : ∀ p ∈ pairs, ∀ q ∈ pairs, p.1 ≠ q.2)
    (hb : ∀ p ∈ pairs, (a.stacks p.1).length ≤ B) :
    copyManyCost pairs a ≤ pairs.length * (7 * B + 5) := by
  induction pairs generalizing a with
  | nil => simp [copyManyCost]
  | cons pair pairs ih =>
      rcases pair with ⟨src, dst⟩
      have hfirst := hb (src, dst) (by simp)
      have hd : ∀ p ∈ pairs, ∀ q ∈ pairs, p.1 ≠ q.2 := by
        intro p hp q hq
        exact hdisjoint p (by simp [hp]) q (by simp [hq])
      have hrest : ∀ p ∈ pairs, ((copyState src dst a).stacks p.1).length ≤ B := by
        intro p hp
        rw [copyState_frame src dst p.1 a
          (hdisjoint p (by simp [hp]) (src, dst) (by simp))]
        exact hb p (by simp [hp])
      have htail := ih (copyState src dst a) hd hrest
      change (a.stacks src).length ≤ B at hfirst
      change 7 * (a.stacks src).length + 5 + copyManyCost pairs (copyState src dst a) ≤
        (pairs.length + 1) * (7 * B + 5)
      nlinarith only [htail, hfirst]

end SubexponentialSAT.Subexp.LocalBasisBatchProgram

end OAI.Algorithms
