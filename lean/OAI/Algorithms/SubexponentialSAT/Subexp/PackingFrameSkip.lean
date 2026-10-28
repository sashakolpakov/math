import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockZeroProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.SelectorMapProgram

namespace OAI.Algorithms

/-! An actual framed-pre skip call with arbitrary surrounding packing data. -/

namespace SubexponentialSAT.Subexp.PackingFrameSkip

open BitProgram StructuredCalls MatrixProgramSupport

variable {s : ℕ}

def registers (i : Fin 3) : Fin 8 := Fin.castAdd 5 i
def stackPorts (count source : Fin s) : Fin 2 → Fin s := ![count, source]

theorem registers_injective : Function.Injective registers := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 8 => k.val) h)

theorem stacks_injective (count source : Fin s) (h : count ≠ source) :
    Function.Injective (stackPorts count source) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [stackPorts]

abbrev command (count source : Fin s) : Cmd 8 s :=
  .call (ProgramLinking.liftProgram BlockZeroProgram.skipProgram registers (stackPorts count source))

def finalState (count source : Fin s) (a : Data s)
    (pre : List (List Bool)) (rest : List Bool) : Data s :=
  ⟨Function.update (Function.update (Function.update a.regs 0 false) 1 false) 2
      (a.regs 2 || !pre.isEmpty),
    Function.update (Function.update a.stacks count []) source rest⟩

theorem frames_eq_words (xs : List (List Bool)) : BlockZeroProgram.frames xs = words xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    change Encoding.frame b ++ BlockZeroProgram.frames bs = Encoding.frame b ++ words bs
    rw [ih]

theorem command_eval (count source : Fin s) (hcs : count ≠ source)
    (a : Data s) (pre : List (List Bool)) (rest : List Bool)
    (hc : (a.stacks count).length = pre.length)
    (hs : a.stacks source = words pre ++ rest) :
    Eval (command count source) (BlockZeroProgram.skipCost pre) a
      (finalState count source a pre rest) := by
  let x : StructuredProgram.State 3 2 :=
    ⟨![a.regs 0, a.regs 1, a.regs 2], ![a.stacks count, words pre ++ rest]⟩
  let y : StructuredProgram.State 3 2 :=
    ⟨![false, false, a.regs 2 || !pre.isEmpty], ![[], rest]⟩
  have hw := frames_eq_words pre
  have hx : embedState registers (stackPorts count source) a x = a := by
    apply SelectorMapProgram.embed_eq _ _ registers_injective (stacks_injective count source hcs)
    · intro i
      fin_cases i <;> rfl
    · intro i
      fin_cases i
      · rfl
      · exact hs
    · intros; rfl
    · intros; rfl
  have hy : embedState registers (stackPorts count source) a y =
      finalState count source a pre rest := by
    apply SelectorMapProgram.embed_eq _ _ registers_injective (stacks_injective count source hcs)
    · intro i
      fin_cases i <;> simp [y, finalState, registers]
    · intro i
      fin_cases i <;> simp [y, finalState, stackPorts, hcs]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [registers] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [registers] using h.symm⟩
      have h2 : j ≠ 2 := fun h => hj ⟨2, by simpa [registers] using h.symm⟩
      simp [finalState, h0, h1, h2]
    · intro j hj
      have hcj : j ≠ count := fun h => hj ⟨0, by simpa [stackPorts] using h.symm⟩
      have hsj : j ≠ source := fun h => hj ⟨1, by simpa [stackPorts] using h.symm⟩
      simp [finalState, hcj, hsj]
  have ht : Trace BlockZeroProgram.skipProgram (BlockZeroProgram.skipCost pre)
      (x.withPC (some BlockZeroProgram.skipProgram.entry)) (y.withPC none) := by
    simpa only [x, y, BlockZeroProgram.skipCfg, hw, StructuredProgram.State.withPC] using
      BlockZeroProgram.skipProgram_trace pre rest (a.stacks count) hc
        (a.regs 0) (a.regs 1) (a.regs 2)
  have he := eval_call_lifted BlockZeroProgram.skipProgram registers (stackPorts count source)
    a registers_injective (stacks_injective count source hcs) ht
  simpa only [hx, hy, command] using he

theorem cost_le (pre : List (List Bool)) :
    BlockZeroProgram.skipCost pre ≤ 4 * (words pre).length + 3 := by
  have hw := frames_eq_words pre
  simpa only [hw] using BlockZeroProgram.skipCost_le pre

end SubexponentialSAT.Subexp.PackingFrameSkip

end OAI.Algorithms
