import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingPrefixProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingPrefixProgram

open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.Subexp

/-- Three persistent inputs and eight initially empty output/work stacks. -/
def input (regs : Fin 3 → Bool) (table count width : List Bool) : Data :=
  ⟨regs, ![table,count,width,[],[],[],[],[],[],[],[]]⟩

def output (regs : Fin 3 → Bool) (table count width : List Bool) : Data :=
  ⟨regs, ![table,count,width,table.take (count.length * width.length),
    unary count.length,[],[],[],[],[],[]]⟩

abbrev copy (source target : Fin 11) : Cmd 3 11 :=
  .call (StackRoutines.copyProgram source target 7 0 1)
def copied (source target : Fin 11) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks source target a.stacks⟩

theorem copy_eval (source target : Fin 11) (a : Data)
    (hsd : source ≠ target) (hs7 : source ≠ 7) (ht7 : target ≠ 7)
    (ht : a.stacks 7 = []) :
    Eval (copy source target) (7 * (a.stacks source).length + 5) a (copied source target a) :=
  TupleProgram.copy_eval source target 7 0 1 hsd hs7 ht7.symm (by decide) a ht

abbrev clear (stack : Fin 11) : Cmd 3 11 := .call (StackRoutines.clearProgram stack 0 1)
def cleared (stack : Fin 11) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks stack a.stacks⟩

theorem clear_eval (stack : Fin 11) (a : Data) :
    Eval (clear stack) (2 * (a.stacks stack).length + 3) a (cleared stack a) :=
  TupleProgram.clear_eval stack 0 1 a

/-- All control is fixed. Counter values, table width and prefix length are
runtime data. Only the first h*W table bits are read. -/
abbrev command : Cmd 3 11 :=
  .seq (copy 1 5) (.seq (normalize 4)
    (.seq (copy 2 5) (.seq (normalize 8)
      (.seq (copy 4 5) (.seq multiply
        (.seq (clear 8) (.seq readPrefix (clear 6))))))))

def budget (h W : ℕ) : ℕ := 24 * h * W + 25 * h + 13 * W + 48

theorem budget_le_input (h W tableBits : ℕ) (henough : h * W ≤ tableBits) :
    budget h W ≤ 48 * (tableBits + h + W + 1) := by
  unfold budget
  nlinarith

theorem command_eval (regs : Fin 3 → Bool) (table count width : List Bool)
    (henough : count.length * width.length ≤ table.length) :
    ∃ n ≤ budget count.length width.length, ∃ regs',
      Eval command n (input regs table count width) (output regs' table count width) := by
  let a := input regs table count width
  let a1 := copied 1 5 a
  let a2 := afterNormalize 4 a1
  let a3 := copied 2 5 a2
  let a4 := afterNormalize 8 a3
  let a5 := copied 4 5 a4
  have h1 : Eval (copy 1 5) (7 * count.length + 5) a a1 :=
    copy_eval 1 5 a (by decide) (by decide) (by decide) rfl
  have hc1 : a1.stacks 5 = count := by simp [a1, a, copied, input, StackRoutines.copyStacks]
  have h2 := normalize_eval 4 (by decide) a1
  rw [hc1] at h2
  have ht2 : a2.stacks 7 = [] := by
    simp [a2, a1, a, afterNormalize, copied, input, StackRoutines.copyStacks]
  have hw2 : a2.stacks 2 = width := by
    simp [a2, a1, a, afterNormalize, copied, input, StackRoutines.copyStacks]
  have h3 := copy_eval 2 5 a2 (by decide) (by decide) (by decide) ht2
  rw [hw2] at h3
  have hw3 : a3.stacks 5 = width := by
    simp [a3, a2, a1, a, afterNormalize, copied, input, StackRoutines.copyStacks]
  have h4 := normalize_eval 8 (by decide) a3
  rw [hw3] at h4
  have ht4 : a4.stacks 7 = [] := by
    simp [a4, a3, a2, a1, a, afterNormalize, copied, input, StackRoutines.copyStacks]
  have hh4 : a4.stacks 4 = unary count.length := by
    simp [a4, a3, a2, a1, a, afterNormalize, copied, input, StackRoutines.copyStacks, unary]
  have h5 := copy_eval 4 5 a4 (by decide) (by decide) (by decide) ht4
  rw [hh4, List.length_replicate] at h5
  have hmW : a5.stacks 8 = unary width.length := by
    simp [a5, a4, a3, a2, a1, a, afterNormalize, copied, input, StackRoutines.copyStacks, unary]
  have hmh : a5.stacks 5 = unary count.length := by
    simp [a5, a4, a3, a2, a1, a, afterNormalize, copied, input, StackRoutines.copyStacks, unary]
  have hmt : a5.stacks 7 = [] := by
    simp [a5, a4, a3, a2, a1, a, afterNormalize, copied, input, StackRoutines.copyStacks]
  obtain ⟨n, hn, r6, h6⟩ := multiply_eval a5 width.length count.length hmW hmh hmt
  let a6 : Data := ⟨r6, Function.update (Function.update a5.stacks 5 []) 6
    (unary (count.length * width.length) ++ a5.stacks 6)⟩
  let a7 := cleared 8 a6
  have hw6 : a6.stacks 8 = unary width.length := by simpa [a6] using hmW
  have h7 := clear_eval 8 a6
  rw [hw6, List.length_replicate] at h7
  have hm6 : a7.stacks 6 = unary (count.length * width.length) := by
    simp [a7, a6, a5, a4, a3, a2, a1, a, cleared, afterNormalize, copied, input,
      StackRoutines.clearStacks, StackRoutines.copyStacks]
  have htable : a7.stacks 0 = table := by
    simp [a7, a6, a5, a4, a3, a2, a1, a, cleared, afterNormalize, copied, input,
      StackRoutines.clearStacks, StackRoutines.copyStacks]
  have empty7 : a7.stacks 5 = [] ∧ a7.stacks 7 = [] ∧ a7.stacks 8 = [] ∧
      a7.stacks 9 = [] ∧ a7.stacks 10 = [] := by
    simp [a7, a6, a5, a4, a3, a2, a1, a, cleared, afterNormalize, copied, input,
      StackRoutines.clearStacks, StackRoutines.copyStacks]
  have h8 := readPrefix_eval a7 (count.length * width.length) hm6
    (by simpa [htable] using henough) empty7.1 empty7.2.1 empty7.2.2.1
      empty7.2.2.2.1 empty7.2.2.2.2
  let a8 : Data := ⟨readRegs a7.regs 0 1 none, Function.update a7.stacks 3
    ((a7.stacks 0).take (count.length * width.length) ++ a7.stacks 3)⟩
  let a9 := cleared 6 a8
  have hp8 : a8.stacks 6 = unary (count.length * width.length) := by simpa [a8] using hm6
  have h9 := clear_eval 6 a8
  rw [hp8, List.length_replicate] at h9
  have ht := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq h9)))))))
  have heq : a9 = output a9.regs table count width := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;>
        simp [ a8, a7, a6, a5, a4, a3, a2, a1, a, cleared,
          afterNormalize, copied, input, StackRoutines.clearStacks, StackRoutines.copyStacks, unary]
  change Eval command _ a a9 at ht
  rw [heq] at ht
  refine ⟨_, ?_, a9.regs, ht⟩
  unfold budget
  nlinarith

def program := compiled command 0 3

theorem program_trace (regs : Fin 3 → Bool) (table count width : List Bool)
    (henough : count.length * width.length ≤ table.length) :
    ∃ n ≤ budget count.length width.length + 1, ∃ regs',
      Trace program n ((input regs table count width).withPC (some program.entry))
        ((output regs' table count width).withPC none) := by
  obtain ⟨n, hn, regs', ht⟩ := command_eval regs table count width henough
  exact ⟨n + 1, by omega, regs', compiled_halt_trace ht 0 3⟩

end SubexponentialSAT.SqrtLog.PackingPrefixProgram

end OAI.Algorithms
