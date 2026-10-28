import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ModularRingPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Fixed-width exact integer scores for the selector. The input sum may
have arbitrarily many redundant high zeros; the machine physically removes
them or pads the input to the requested width. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Score

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives
open SubexponentialSAT.ModularRingPrograms SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic

abbrev Data := State 8 9

abbrev data (regs : Fin 8 → Bool) (input shape width : List Bool) : Data :=
  ⟨regs, ![input, [], [], [], [], [], [], shape, width]⟩

abbrev small (regs : Fin 8 → Bool) (input shape : List Bool) : State 8 8 :=
  ⟨regs, normalizationState input shape [] []⟩

private theorem updateInput (regs : Fin 8 → Bool) (before shape width input : List Bool) :
    Function.update (data regs before shape width).stacks 0 input =
      (data regs input shape width).stacks := by
  funext i; fin_cases i <;> simp []

private theorem updateShape (regs : Fin 8 → Bool) (input before width shape : List Bool) :
    Function.update (data regs input before width).stacks 7 shape =
      (data regs input shape width).stacks := by
  funext i; fin_cases i <;> simp []

theorem embedded (frameRegs regs : Fin 8 → Bool) (frameInput width input shape : List Bool) :
    embedState id (Fin.castAdd 1) (data frameRegs frameInput [] width) (small regs input shape) =
      data regs input shape width := by
  apply embedState_eq_of_ports id (Fin.castAdd 1) _ _ _ Function.injective_id (Fin.castAdd_injective 8 1)
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
    have h7 : i ≠ 7 := fun h => hi ⟨7,h.symm⟩
    have hs : (data regs input shape width).stacks =
        Function.update (Function.update (data frameRegs frameInput [] width).stacks 0 input) 7 shape := by
      rw [updateInput,updateShape]
    change (data regs input shape width).stacks i=(data frameRegs frameInput [] width).stacks i
    rw [hs,Function.update_of_ne h7,Function.update_of_ne h0]

abbrev copyWidth : Cmd 8 9 := .call (StackRoutines.copyProgram 8 7 6 0 1)
abbrev normalize : Cmd 8 9 :=
  .call (ProgramLinking.liftProgram normalizeProgram id (Fin.castAdd 1))
abbrev command : Cmd 8 9 := .seq copyWidth normalize
abbrev program := compiled command 0 0

theorem copyWidth_eval (regs : Fin 8 → Bool) (input width : List Bool) :
    Eval copyWidth (7 * width.length + 5) (data regs input [] width)
      (data (readRegs regs 0 1 none) input width width) := by
  have he := copy_eval (data regs input [] width) 8 7 6 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  have hs : afterCopy (data regs input [] width) 8 7 0 1 =
      data (readRegs regs 0 1 none) input width width := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterCopy, StackRoutines.copyStacks]
  simpa [copyWidth, hs, data] using he

theorem command_eval (regs : Fin 8 → Bool) (input width : List Bool) :
    ∃ n finalRegs, n ≤ 14 * width.length + 2 * input.length + 14 ∧
      Eval command n (data regs input [] width)
        (data finalRegs (padTo width input) [] width) := by
  obtain ⟨rf,n,hn,he⟩ := normalize_correct (readRegs regs 0 1 none) input width []
  change Trace normalizeProgram n
    ((small (readRegs regs 0 1 none) input width).withPC (some normalizeProgram.entry))
    ((small rf (padTo width input) []).withPC none) at he
  have hl := eval_call_lifted normalizeProgram id (Fin.castAdd 1)
    (data regs input [] width) Function.injective_id (Fin.castAdd_injective 8 1)
    (a := small (readRegs regs 0 1 none) input width)
    (b := small rf (padTo width input) []) he
  change Eval normalize n
    (embedState id (Fin.castAdd 1) (data regs input [] width)
      (small (readRegs regs 0 1 none) input width))
    (embedState id (Fin.castAdd 1) (data regs input [] width)
      (small rf (padTo width input) [])) at hl
  rw [embedded,embedded] at hl
  exact ⟨7 * width.length + 5 + n,rf,by omega,(copyWidth_eval regs input width).seq hl⟩

theorem exact_score (regs : Fin 8 → Bool) (input width : List Bool)
    (h : BinaryArithmetic.toNat input < 2 ^ width.length) :
    ∃ finalRegs word, word.length = width.length ∧ BinaryArithmetic.toNat word = BinaryArithmetic.toNat input ∧
      RunsIn program (14 * width.length + 2 * input.length + 15)
        ((data regs input [] width).withPC (some program.entry))
        ((data finalRegs word [] width).withPC none) := by
  obtain ⟨n,rf,hn,he⟩ := command_eval regs input width
  refine ⟨rf,padTo width input,?_,padTo_value_of_lt width input h,
    n+1,by omega,compiled_halt_trace he 0 0⟩
  exact padTo_length width input

end SubexponentialSAT.SqrtLog.LeafProgram.Score

end OAI.Algorithms
