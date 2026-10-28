import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCorrect
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

/-- The suffix is linear in the count word; every caller stack is included. -/
theorem answer_all_prefix (a : State 80 1220) (bound : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate,
      prefixSteps ≤ answerSteps a →
      Trace answerProgram prefixSteps (a.withPC (some answerProgram.entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ 1232 * bound + 15 := by
  intro prefixSteps intermediate hsteps htrace i
  have hstart : dataBits (a.withPC (some answerProgram.entry)) ≤ 1220 * bound :=
    StreamResources.dataBits_le_mul _ ha
  have hlocal := StructuredSpace.local_stack_bound answerProgram
    (steps := answerSteps a) hstart
    prefixSteps intermediate hsteps htrace i
  have hcount := ha ABI.countStack
  have hanswer := ha ABI.answerStack
  have hscratch := ha ABI.positivityScratch
  simp only [answerSteps] at hlocal
  omega

/-- Lifting a leaf preserves the suspended DFS frame and all prefix bounds. -/
theorem leafCall_all_prefix {l steps bound frameBound : ℕ}
    (p : Program 40 896 l) (frame : Cfg 80 1220 l) {a b : Cfg 40 896 l}
    (h : Trace p steps a b)
    (hb : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps a intermediate → ∀ i, (intermediate.stacks i).length ≤ bound)
    (hf : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (ProgramLinking.liftProgram p ABI.leafRegisters ABI.leafStacks) prefixSteps
        (ProgramLinking.embedCfg ABI.leafRegisters ABI.leafStacks id none frame a)
        intermediate → ∀ i, (intermediate.stacks i).length ≤ max bound frameBound :=
  StructuredSpace.liftProgram_stack_bound p ABI.leafRegisters ABI.leafStacks frame
    ABI.leafRegisters.injective ABI.leafStacks.injective h hb hf

theorem power_all_prefix (regs : Fin 2 → Bool) (n : ℕ) :
    ∀ prefixSteps intermediate, prefixSteps ≤ 4 * n + 5 →
      Trace powerProgram prefixSteps
        ((⟨regs, ![Encoding.encodeNat n, []]⟩ : State 2 2).withPC
          (some powerProgram.entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ 5 * n + 6 := by
  intro prefixSteps intermediate hsteps htrace i
  have hstart : dataBits
      ((⟨regs, ![Encoding.encodeNat n, []]⟩ : State 2 2).withPC
        (some powerProgram.entry)) ≤ n + 1 := by
    simp [dataBits, stackBits, Fin.sum_univ_two]
  have h := StructuredSpace.local_stack_bound powerProgram (steps := 4 * n + 5)
    hstart prefixSteps intermediate hsteps htrace i
  omega

/-- Header parsing is a polynomial local routine, including its preserved input. -/
theorem header_all_prefix (n : ℕ) (body : List Bool) :
    ∀ prefixSteps intermediate,
      prefixSteps ≤ 7 * (Encoding.encodeNat n ++ body).length + 6 +
        FrontendProgram.initializeBound n →
      Trace headerProgram prefixSteps
        (initial headerProgram (Encoding.encodeNat n ++ body)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤
        8 * (Encoding.encodeNat n ++ body).length + 6 + FrontendProgram.initializeBound n := by
  intro prefixSteps intermediate hsteps htrace i
  have hstart : dataBits (initial headerProgram (Encoding.encodeNat n ++ body)) ≤
      (Encoding.encodeNat n ++ body).length := by simp
  have h := StructuredSpace.local_stack_bound headerProgram
    (steps := 7 * (Encoding.encodeNat n ++ body).length + 6 +
      FrontendProgram.initializeBound n) hstart prefixSteps intermediate hsteps htrace i
  omega

theorem clearLeaf_all_prefix (a : State 80 1220) (bound : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ 896 * (2 * bound + 3) + 1 →
      Trace (compiled clearLeaf ABI.countStack ABI.countStack) prefixSteps
        (a.withPC (some (compiled clearLeaf ABI.countStack ABI.countStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ 3012 * bound + 2689 := by
  intro prefixSteps intermediate hs ht i
  have hstart : dataBits (a.withPC
      (some (compiled clearLeaf ABI.countStack ABI.countStack).entry)) ≤ 1220 * bound :=
    StreamResources.dataBits_le_mul _ ha
  have h := StructuredSpace.local_stack_bound (compiled clearLeaf ABI.countStack ABI.countStack)
    (steps := 896 * (2 * bound + 3) + 1) hstart prefixSteps intermediate hs ht i
  calc
    (intermediate.stacks i).length ≤
        1220 * bound + (896 * (2 * bound + 3) + 1) := h
    _ = 3012 * bound + 2689 := by ring

theorem loadLeaf_all_prefix (a : State 80 1220) (bound : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ 1815 * bound + 2747 →
      Trace (compiled loadLeaf ABI.countStack ABI.countStack) prefixSteps
        (a.withPC (some (compiled loadLeaf ABI.countStack ABI.countStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ 3035 * bound + 2747 := by
  intro prefixSteps intermediate hs ht i
  have hstart : dataBits (a.withPC
      (some (compiled loadLeaf ABI.countStack ABI.countStack).entry)) ≤ 1220 * bound :=
    StreamResources.dataBits_le_mul _ ha
  have h := StructuredSpace.local_stack_bound (compiled loadLeaf ABI.countStack ABI.countStack)
    (steps := 1815 * bound + 2747) hstart prefixSteps intermediate hs ht i
  calc
    (intermediate.stacks i).length ≤ 1220 * bound + (1815 * bound + 2747) := h
    _ = 3035 * bound + 2747 := by ring

theorem exportLeaf_all_prefix (a : State 80 1220) (bound : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ 1803 * bound + 2700 →
      Trace (compiled exportLeaf ABI.countStack ABI.countStack) prefixSteps
        (a.withPC (some (compiled exportLeaf ABI.countStack ABI.countStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ 3023 * bound + 2700 := by
  intro prefixSteps intermediate hs ht i
  have hstart : dataBits (a.withPC
      (some (compiled exportLeaf ABI.countStack ABI.countStack).entry)) ≤ 1220 * bound :=
    StreamResources.dataBits_le_mul _ ha
  have h := StructuredSpace.local_stack_bound (compiled exportLeaf ABI.countStack ABI.countStack)
    (steps := 1803 * bound + 2700) hstart prefixSteps intermediate hs ht i
  calc
    (intermediate.stacks i).length ≤ 1220 * bound + (1803 * bound + 2700) := h
    _ = 3023 * bound + 2700 := by ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
