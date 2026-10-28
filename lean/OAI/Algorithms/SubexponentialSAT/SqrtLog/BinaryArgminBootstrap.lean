import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgminScan

namespace OAI.Algorithms

/-! Bootstrap the binary argmin from an empty incumbent. The initial candidate
load is paid explicitly, including the empty-input case. -/

namespace SubexponentialSAT.SqrtLog.BinaryArgmin

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev installFirst : Cmd 8 9 := .seq replace cleanup

theorem installFirst_eval (B C : ℕ) (next : Entry) (queue : List Bool)
    (regs : Fin 8 → Bool) (hn : Fits B C next) :
    ∃ n ≤ 100 * (B + C + 1), ∃ regs',
      Eval installFirst n (data regs next empty queue) (data regs' empty next queue) := by
  let d := data regs next empty queue
  have hr := replace_eval d (by rfl)
  have hc := cleanup_eval (afterReplace d)
  have hf : afterCleanup (afterReplace d) =
      data (afterCleanup (afterReplace d)).regs empty next queue := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;> simp [ afterReplace, afterClear, afterCopy,
        StackRoutines.clearStacks, StackRoutines.copyStacks, d, data, store, empty]
  refine ⟨9 * next.payload.length + 9 * next.score.length + 25, ?_,
    (afterCleanup (afterReplace d)).regs, ?_⟩
  · rcases hn with ⟨hs, hp⟩
    omega
  · rw [← hf]
    convert Eval.seq hr hc using 1
    simp [afterReplace, afterClear, afterCopy, StackRoutines.clearStacks,
      StackRoutines.copyStacks, d, data, store, empty]
    omega

/-- Extra callback obligation for the first load, where the incumbent is empty
and need not have the fixed score width. It requires actual traces as usual. -/
structure FirstLoadSpec (load : Cmd 8 9) (encode : List Entry → List Bool)
    (B C cost : ℕ) : Prop where
  nil : ∀ regs, ∃ n ≤ cost, ∃ regs', regs' 7 = false ∧
    Eval load n (data regs empty empty (encode []))
      (data regs' empty empty (encode []))
  cons : ∀ next rest regs, Fits B C next → (∀ a ∈ rest, Fits B C a) →
    ∃ n ≤ cost, ∃ regs', regs' 7 = true ∧
      Eval load n (data regs empty empty (encode (next :: rest)))
        (data regs' next empty (encode rest))

abbrev selectCommand (load : Cmd 8 9) : Cmd 8 9 :=
  .seq load (.ite 7
    (.seq installFirst (.seq (scanCommand load) (atom (.set 7 true)))) (.base .skip))

theorem select_nil (load : Cmd 8 9) (encode : List Entry → List Bool)
    (B C cost : ℕ) (hfirst : FirstLoadSpec load encode B C cost)
    (regs : Fin 8 → Bool) :
    ∃ n ≤ cost + 1, ∃ regs', regs' 7 = false ∧
      Eval (selectCommand load) n (data regs empty empty (encode []))
        (data regs' empty empty (encode [])) := by
  obtain ⟨n, hn, regs', hf, ht⟩ := hfirst.nil regs
  exact ⟨n + 1, Nat.add_le_add_right hn 1, regs', hf,
    Eval.seq ht (Eval.ite_false hf (Eval.base (.skip _)))⟩

theorem select_cons (load : Cmd 8 9) (encode : List Entry → List Bool)
    (B C cost : ℕ) (hload : LoaderSpec load encode B C cost)
    (hfirst : FirstLoadSpec load encode B C cost)
    (seed : Entry) (rest : List Entry) (regs : Fin 8 → Bool)
    (hs : Fits B C seed) (hr : ∀ a ∈ rest, Fits B C a) :
    ∃ n ≤ cost + 100 * (B + C + 1) + scanBudget B C cost rest.length + 2,
      ∃ regs', regs' 7 = true ∧
      Eval (selectCommand load) n (data regs empty empty (encode (seed :: rest)))
        (data regs' empty (HashSelect.best value seed rest) (encode [])) := by
  obtain ⟨l, hl, r₁, htrue, hread⟩ := hfirst.cons seed rest regs hs hr
  obtain ⟨i, hi, r₂, hinit⟩ := installFirst_eval B C seed (encode rest) r₁ hs
  obtain ⟨s, hsb, r₃, _, hscan⟩ := scan_eval load encode B C cost hload seed rest r₂ hs hr
  let final := Function.update r₃ 7 true
  have hmark : Eval (atom (.set 7 true)) 1
      (data r₃ empty (HashSelect.best value seed rest) (encode []))
      (data final empty (HashSelect.best value seed rest) (encode [])) :=
    Eval.base (StructuredProgram.Eval.atom (.set 7 true) _)
  refine ⟨l + (i + (s + 1) + 1), by omega, final, by simp [final], ?_⟩
  exact Eval.seq hread (Eval.ite_true htrue (Eval.seq hinit (Eval.seq hscan hmark)))

theorem select_cons_linear (B C cost count : ℕ) :
    cost + 100 * (B + C + 1) + scanBudget B C cost count + 2 ≤
      (count + 2) * (cost + 100 * (B + C + 1) + 3) := by
  unfold scanBudget
  nlinarith

end SubexponentialSAT.SqrtLog.BinaryArgmin

end OAI.Algorithms
