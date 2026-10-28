import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramStream
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramTotal

namespace OAI.Algorithms

/-! Arithmetic callbacks on a fixed stream ABI. The remaining record stream is
preserved byte-for-byte across each real signed-arithmetic call. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

private theorem localOperation_eval_total (multiply : Bool) (regs : Fin 8 → Bool)
    (acc next : WordPair) :
    ∃ t ≤ 25000*(pairLength acc+pairLength next+3)^2, ∃ regs' result,
      Eval (localOperation multiply) t (localInput regs acc next)
        (pairState regs' result.1 result.2) ∧
      pairValue result = combine multiply (pairValue acc) (pairValue next) ∧
      pairTotal result.1 result.2 = (if multiply then
        pairTotal acc.1 acc.2 * pairTotal next.1 next.2 else
        pairTotal acc.1 acc.2 + pairTotal next.1 next.2) ∧
      pairLength result ≤ wordGrowth multiply (pairLength acc) (pairLength next) := by
  have hd : Ready (localInput regs acc next) := by
    intro j hj
    fin_cases j <;> simp_all [localInput]
  have hl : inputLength (localInput regs acc next) = pairLength acc+pairLength next := by
    simp [inputLength, localInput, pairLength, Nat.add_assoc]
  cases multiply with
  | false =>
    obtain ⟨t, ht, r, p, n, he, hv, htotal, hb⟩ := addReuseCommand_eval_total _ hd
    refine ⟨t, by simpa only [hl] using ht, r, (p,n), he, ?_, ?_, ?_⟩
    · simpa [pairValue, localInput, combine] using hv
    · simpa [localInput] using htotal
    · simpa only [hl, pairLength, wordGrowth, Bool.false_eq_true, ↓reduceIte] using hb
  | true =>
    obtain ⟨t, ht, r, p, n, he, hv, htotal, hb⟩ := multiplyReuseCommand_eval_total _ hd
    refine ⟨t, by simpa only [hl] using ht, r, (p,n), he, ?_, ?_, ?_⟩
    · simpa [pairValue, localInput, combine] using hv
    · simpa [localInput] using htotal
    · simpa only [hl, pairLength, wordGrowth, ↓reduceIte] using hb

private theorem outside_streamPorts_total (j : Fin 16)
    (hj : ¬ ∃ i, streamPorts i = j) : j = 15 := by
  have hv : ¬ j.val < 15 := by
    intro h
    exact hj ⟨⟨j.val,h⟩, Fin.ext rfl⟩
  apply Fin.ext
  change j.val = 15
  omega

theorem streamOperation_eval_total (multiply : Bool) (regs : Fin 8 → Bool)
    (acc next : WordPair) (queue : List Bool) :
    ∃ t ≤ 25000*(pairLength acc+pairLength next+3)^2+1, ∃ regs' result,
      Eval (streamOperation multiply) t (streamData regs acc next queue)
        (streamData regs' result ([],[]) queue) ∧
      pairValue result = combine multiply (pairValue acc) (pairValue next) ∧
      pairTotal result.1 result.2 = (if multiply then
        pairTotal acc.1 acc.2 * pairTotal next.1 next.2 else
        pairTotal acc.1 acc.2 + pairTotal next.1 next.2) ∧
      pairLength result ≤ wordGrowth multiply (pairLength acc) (pairLength next) := by
  obtain ⟨t, ht, r, result, he, hv, htotal, hb⟩ := localOperation_eval_total multiply regs acc next
  have hs : embedState id streamPorts (streamData regs acc next queue)
      (localInput regs acc next) = streamData regs acc next queue := by
    apply embedState_eq_of_ports id streamPorts _ _ _ Function.injective_id streamPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [streamData, localInput, streamPorts]
    · intro i hi; rfl
  have hf : embedState id streamPorts (streamData regs acc next queue)
      (pairState r result.1 result.2) = streamData r result ([],[]) queue := by
    apply embedState_eq_of_ports id streamPorts _ _ _ Function.injective_id streamPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [streamData, pairState, streamPorts]
    · intro i hi
      rw [outside_streamPorts_total i hi]
      rfl
  have hcall := eval_call_lifted (localOperationProgram multiply) id streamPorts
    (streamData regs acc next queue) Function.injective_id streamPorts_injective
    (compiled_halt_trace he 0 1)
  rw [hs, hf] at hcall
  exact ⟨t+1, by omega, r, result, hcall, hv, htotal, hb⟩

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
