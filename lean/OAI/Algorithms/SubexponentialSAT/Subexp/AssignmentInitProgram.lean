import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderPorts
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCopyProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-!
# Physical initialization of the sequential assignment memory

The input contains the already generated alphabet and incidence records.
This fixed routine duplicates the runtime tables, creates the initial packed
assignment by actual repeated copying, and clears all temporary ports. The
production of the input records is a separate frontend stage.
-/

namespace SubexponentialSAT.Subexp.AssignmentInitProgram

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 16 48

structure Context where
  defaultWord : List Bool
  packedAlphabet : List Bool
  alphabetRecords : List Bool
  width : List Bool
  depth : List Bool
  rawPairs : List Bool
  seedRecords : List Bool
  seedCount : ℕ

def unary (n : ℕ) : List Bool := List.replicate n true

def state (ctx : Context) (regs : Fin 16 → Bool)
    (word assignment remaining counter duplicate : List Bool) : Data :=
  ⟨regs, fun j =>
    if j = 0 then word
    else if j = 2 then counter
    else if j = 8 then assignment
    else if j = 9 then ctx.packedAlphabet
    else if j = 10 then ctx.width
    else if j = 11 then remaining
    else if j = 30 then ctx.alphabetRecords
    else if j = 34 then ctx.depth
    else if j = 39 then duplicate
    else if j = 45 then ctx.rawPairs
    else if j = 46 then ctx.seedRecords
    else if j = 47 then unary ctx.seedCount else []⟩

def inputState (ctx : Context) (regs : Fin 16 → Bool) : Data :=
  state ctx regs ctx.defaultWord [] [] [] []

def outputState (ctx : Context) : Data :=
  state ctx (fun _ => false) []
    (BlockCopyProgram.copies ctx.seedCount ctx.defaultWord)
    (unary ctx.seedCount) [] ctx.alphabetRecords

def copyRegisters : Fin 3 → Fin 16 := Fin.castAdd 13
def copyPorts : Fin 4 → Fin 48 := ![0, 8, 1, 2]

theorem copyRegisters_injective : Function.Injective copyRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun z : Fin 16 => z.val) h)

theorem copyPorts_injective : Function.Injective copyPorts := by decide

abbrev reset : Cmd 16 48 := SequentialProgram.resetList (List.finRange 16)
abbrev copyRemaining : Cmd 16 48 := .call (copyProgram 47 11 1 (0 : Fin 16) 1)
abbrev copyCounter : Cmd 16 48 := .call (copyProgram 47 2 1 (0 : Fin 16) 1)
abbrev repeatDefault : Cmd 16 48 :=
  .call (ProgramLinking.liftProgram BlockCopyProgram.program copyRegisters copyPorts)
abbrev copyAlphabet : Cmd 16 48 := .call (copyProgram 30 39 1 (0 : Fin 16) 1)
abbrev clearDefault : Cmd 16 48 := .call (clearProgram 0 (0 : Fin 16) 1)

abbrev command : Cmd 16 48 :=
  .seq reset (.seq copyRemaining (.seq copyCounter
    (.seq repeatDefault (.seq copyAlphabet clearDefault))))

abbrev program : Program 16 48 (size command + 1) := compiled command 0 8

theorem reset_eval (d : Data) :
    Eval reset 16 d ⟨fun _ => false, d.stacks⟩ := by
  have h := SequentialProgram.resetList_eval (List.finRange 16) d
  simpa [reset, SequentialProgram.resetState] using h

theorem copyRemaining_eval (ctx : Context) :
    Eval copyRemaining (7 * ctx.seedCount + 5)
      (state ctx (fun _ => false) ctx.defaultWord [] [] [] [])
      (state ctx (fun _ => false) ctx.defaultWord [] (unary ctx.seedCount) [] []) := by
  have h := TupleProgram.copy_eval (47 : Fin 48) 11 1 (0 : Fin 16) 1
    (by decide) (by decide) (by decide) (by decide)
    (state ctx (fun _ => false) ctx.defaultWord [] [] [] []) (by simp [state])
  convert h using 1
  · simp [state, unary]
  · apply congrArg₂ StructuredProgram.State.mk
    · funext j; fin_cases j <;> simp [state, readRegs]
    · funext j; fin_cases j <;> simp [state, copyStacks]

theorem copyCounter_eval (ctx : Context) :
    Eval copyCounter (7 * ctx.seedCount + 5)
      (state ctx (fun _ => false) ctx.defaultWord [] (unary ctx.seedCount) [] [])
      (state ctx (fun _ => false) ctx.defaultWord [] (unary ctx.seedCount)
        (unary ctx.seedCount) []) := by
  have h := TupleProgram.copy_eval (47 : Fin 48) 2 1 (0 : Fin 16) 1
    (by decide) (by decide) (by decide) (by decide)
    (state ctx (fun _ => false) ctx.defaultWord [] (unary ctx.seedCount) [] [])
    (by simp [state])
  convert h using 1
  · simp [state, unary]
  · apply congrArg₂ StructuredProgram.State.mk
    · funext j; fin_cases j <;> simp [state, readRegs]
    · funext j; fin_cases j <;> simp [state, copyStacks]

theorem repeatDefault_eval (ctx : Context) :
    Eval repeatDefault (ctx.seedCount * (7 * ctx.defaultWord.length + 7) + 3)
      (state ctx (fun _ => false) ctx.defaultWord [] (unary ctx.seedCount)
        (unary ctx.seedCount) [])
      (state ctx (fun _ => false) ctx.defaultWord
        (BlockCopyProgram.copies ctx.seedCount ctx.defaultWord)
        (unary ctx.seedCount) [] []) := by
  let before := state ctx (fun _ => false) ctx.defaultWord []
    (unary ctx.seedCount) (unary ctx.seedCount) []
  let after := state ctx (fun _ => false) ctx.defaultWord
    (BlockCopyProgram.copies ctx.seedCount ctx.defaultWord) (unary ctx.seedCount) [] []
  have hin : embedState copyRegisters copyPorts before
      (BlockCopyProgram.initialState ctx.seedCount ctx.defaultWord []) = before := by
    apply embedState_eq_of_ports _ _ _ _ _ copyRegisters_injective copyPorts_injective
    · intro i; fin_cases i <;> simp [before, state, copyRegisters,
        BlockCopyProgram.initialState, BlockCopyProgram.data]
    · intros; rfl
    · intro i; fin_cases i <;> simp [before, state, copyPorts, unary,
        BlockCopyProgram.initialState, BlockCopyProgram.data]
    · intros; rfl
  have hout : embedState copyRegisters copyPorts before
      (BlockCopyProgram.data false false ctx.defaultWord
        (BlockCopyProgram.copies ctx.seedCount ctx.defaultWord ++ []) []) = after := by
    apply embedState_eq_of_ports _ _ _ _ _ copyRegisters_injective copyPorts_injective
    · intro i; fin_cases i <;> simp [after, state, copyRegisters, BlockCopyProgram.data]
    · intros; rfl
    · intro i; fin_cases i <;> simp [after, state, copyPorts, BlockCopyProgram.data]
    · intro j hj
      have h2 : j ≠ 2 := fun h => hj ⟨3, by simpa [copyPorts] using h.symm⟩
      have h8 : j ≠ 8 := fun h => hj ⟨1, by simpa [copyPorts] using h.symm⟩
      simp [before, after, state, h2, h8]
  have h := eval_call_lifted BlockCopyProgram.program copyRegisters copyPorts before
    copyRegisters_injective copyPorts_injective
    (BlockCopyProgram.program_trace ctx.seedCount ctx.defaultWord [])
  simpa only [hin, hout, repeatDefault, before, after] using h

theorem copyAlphabet_eval (ctx : Context) :
    Eval copyAlphabet (7 * ctx.alphabetRecords.length + 5)
      (state ctx (fun _ => false) ctx.defaultWord
        (BlockCopyProgram.copies ctx.seedCount ctx.defaultWord) (unary ctx.seedCount) [] [])
      (state ctx (fun _ => false) ctx.defaultWord
        (BlockCopyProgram.copies ctx.seedCount ctx.defaultWord) (unary ctx.seedCount) []
        ctx.alphabetRecords) := by
  have h := TupleProgram.copy_eval (30 : Fin 48) 39 1 (0 : Fin 16) 1
    (by decide) (by decide) (by decide) (by decide)
    (state ctx (fun _ => false) ctx.defaultWord
      (BlockCopyProgram.copies ctx.seedCount ctx.defaultWord) (unary ctx.seedCount) [] [])
    (by simp [state])
  convert h using 1
  · simp [state]
  · apply congrArg₂ StructuredProgram.State.mk
    · funext j; fin_cases j <;> simp [state, readRegs]
    · funext j; fin_cases j <;> simp [state, copyStacks]

theorem clearDefault_eval (ctx : Context) :
    Eval clearDefault (2 * ctx.defaultWord.length + 3)
      (state ctx (fun _ => false) ctx.defaultWord
        (BlockCopyProgram.copies ctx.seedCount ctx.defaultWord) (unary ctx.seedCount) []
        ctx.alphabetRecords)
      (outputState ctx) := by
  have h := TupleProgram.clear_eval (0 : Fin 48) (0 : Fin 16) 1
    (state ctx (fun _ => false) ctx.defaultWord
      (BlockCopyProgram.copies ctx.seedCount ctx.defaultWord) (unary ctx.seedCount) []
      ctx.alphabetRecords)
  convert h using 1
  · simp [state]
  · apply congrArg₂ StructuredProgram.State.mk
    · funext j; fin_cases j <;> simp [state, readRegs]
    · funext j; fin_cases j <;> simp [state, clearStacks]

def sourceCost (ctx : Context) : ℕ :=
  ctx.seedCount * (7 * ctx.defaultWord.length + 21) +
    7 * ctx.alphabetRecords.length + 2 * ctx.defaultWord.length + 38

theorem sourceCost_le (ctx : Context) (B : ℕ)
    (hcount : ctx.seedCount ≤ B) (hword : ctx.defaultWord.length ≤ B)
    (halphabet : ctx.alphabetRecords.length ≤ B) :
    sourceCost ctx ≤ 40 * (B + 1) ^ 2 := by
  calc
    sourceCost ctx ≤ B * (7 * B + 21) + 7 * B + 2 * B + 38 := by
      unfold sourceCost
      gcongr
    _ ≤ 40 * (B + 1) ^ 2 := by nlinarith

theorem command_eval (ctx : Context) (regs : Fin 16 → Bool) :
    Eval command (sourceCost ctx - 1) (inputState ctx regs) (outputState ctx) := by
  have hr := reset_eval (inputState ctx regs)
  have he := hr.seq ((copyRemaining_eval ctx).seq ((copyCounter_eval ctx).seq
    ((repeatDefault_eval ctx).seq ((copyAlphabet_eval ctx).seq (clearDefault_eval ctx)))))
  convert he using 1 ; simp [sourceCost, Nat.mul_add] ; omega

theorem program_trace (ctx : Context) (regs : Fin 16 → Bool) :
    Trace program (sourceCost ctx)
      ((inputState ctx regs).withPC (some program.entry))
      ((outputState ctx).withPC none) := by
  have ht := compiled_halt_trace (command_eval ctx regs) 0 8
  have hp : 1 ≤ sourceCost ctx := by unfold sourceCost; omega
  simpa [program, Nat.sub_add_cancel hp] using ht

theorem program_primitive (ctx : Context) (regs : Fin 16 → Bool) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program * sourceCost ctx)
      (primitiveCfg program ((inputState ctx regs).withPC (some program.entry)))
      (primitiveCfg program ((outputState ctx).withPC none)) :=
  primitive_trace _ (program_trace ctx regs)

theorem output_highState (ctx : Context) :
    SequentialProgram.HighState
      (ScoreBuilderProgram.environment ctx.alphabetRecords ctx.depth ctx.rawPairs
        ctx.seedRecords (unary ctx.seedCount))
      (outputState ctx).stacks := by
  intro j hj
  have h0 : j ≠ 0 := by intro h; subst j; omega
  have h2 : j ≠ 2 := by intro h; subst j; omega
  have h8 : j ≠ 8 := by intro h; subst j; omega
  have h9 : j ≠ 9 := by intro h; subst j; omega
  have h10 : j ≠ 10 := by intro h; subst j; omega
  have h11 : j ≠ 11 := by intro h; subst j; omega
  simp [outputState, state, ScoreBuilderProgram.environment, h0, h2, h8, h9, h10, h11]

theorem output_memory {A : Type*} (encode : A → List Bool) (a : A) (tail : List A)
    (ctx : Context) (hword : ctx.defaultWord = encode a)
    (halphabet : ctx.packedAlphabet = ((a :: tail).map encode).flatten)
    (hwidth : ctx.width.length = (encode a).length) :
    SequentialProgram.Memory encode a tail ctx.seedCount [] (outputState ctx).stacks := by
  constructor
  · simp [outputState, state, BlockCopyProgram.copies, hword]
  · simp [outputState, state, halphabet]
  · simpa [outputState, state] using hwidth
  · simp [outputState, state]
  · intro j hj
    have hn : j ≠ 8 ∧ j ≠ 9 ∧ j ≠ 10 ∧ j ≠ 11 ∧ j.val < 20 :=
      (show ∀ j : Fin 48, j ∈ SequentialProgram.scratchPorts →
        j ≠ 8 ∧ j ≠ 9 ∧ j ≠ 10 ∧ j ≠ 11 ∧ j.val < 20 by decide) j hj
    have h30 : j ≠ 30 := by intro h; subst j; omega
    have h34 : j ≠ 34 := by intro h; subst j; omega
    have h39 : j ≠ 39 := by intro h; subst j; omega
    have h45 : j ≠ 45 := by intro h; subst j; omega
    have h46 : j ≠ 46 := by intro h; subst j; omega
    have h47 : j ≠ 47 := by intro h; subst j; omega
    simp [outputState, state, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1,
      h30, h34, h39, h45, h46, h47]

@[simp] theorem output_remaining (ctx : Context) :
    ((outputState ctx).stacks 11).length = ctx.seedCount := by
  simp [outputState, state, unary]

end SubexponentialSAT.Subexp.AssignmentInitProgram

end OAI.Algorithms
