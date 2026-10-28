import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ModularPrograms
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-!
# Preserving conversion of a binary rank to a fixed-width assignment

Copy the binary rank and the unary shape, then call the existing padding
program. The master rank and shape stay available for enumeration and repeated
evaluation. All lengths remain Boolean-stack data.
-/

namespace SubexponentialSAT.RankAssignmentProgram

open BitProgram StackRoutines StructuredCalls ModularPrograms ModularArithmetic

/-- The padding routine's shape, input, and output use three work stacks. -/
def paddingPorts : Fin 3 → Fin 6 := ![2, 3, 5]

theorem paddingPorts_injective : Function.Injective paddingPorts := by decide

def workStacks (shape input output : List Bool) (stk : Stacks (Fin 6)) : Stacks (Fin 6) :=
  Function.update (Function.update (Function.update stk 2 shape) 3 input) 5 output

private theorem extend_padding (shape input output : List Bool) (stk : Stacks (Fin 6)) :
    Function.extend paddingPorts (operandStacks shape input output) stk =
      workStacks shape input output stk := by
  classical
  funext j
  fin_cases j
  · exact Function.extend_apply' _ _ _ (by decide)
  · exact Function.extend_apply' _ _ _ (by decide)
  · simpa [paddingPorts, operandStacks, workStacks] using
      paddingPorts_injective.extend_apply (operandStacks shape input output) stk (0 : Fin 3)
  · simpa [paddingPorts, operandStacks, workStacks] using
      paddingPorts_injective.extend_apply (operandStacks shape input output) stk (1 : Fin 3)
  · exact Function.extend_apply' _ _ _ (by decide)
  · simpa [paddingPorts, operandStacks, workStacks] using
      paddingPorts_injective.extend_apply (operandStacks shape input output) stk (2 : Fin 3)

private theorem embed_padding (shape input output : List Bool) (stk : Stacks (Fin 6))
    (regs frameRegs : Fin 8 → Bool) :
    embedState id paddingPorts ⟨frameRegs, stk⟩ ⟨regs, operandStacks shape input output⟩ =
      ⟨regs, workStacks shape input output stk⟩ := by
  simp [embedState, extend_padding]

abbrev paddingCmd : Cmd 8 6 :=
  .call (ProgramLinking.liftProgram paddingLEProgram id paddingPorts)

theorem padding_eval (shape input : List Bool) (regs : Fin 8 → Bool) (stk : Stacks (Fin 6))
    (hlen : input.length ≤ shape.length) (hs : stk 2 = shape)
    (hi : stk 3 = input) (ht : stk 5 = []) :
    ∃ finalRegs : Fin 8 → Bool,
      Eval paddingCmd (7 * shape.length + 6) ⟨regs, stk⟩
        ⟨finalRegs, workStacks (padTo shape input) [] [] stk⟩ ∧
      finalRegs 0 = regs 0 := by
  obtain ⟨finalRegs, trace, hreg⟩ := paddingLE_correct regs shape input hlen
  have run := eval_call_lifted paddingLEProgram id paddingPorts (⟨regs, stk⟩ : State 8 6)
    Function.injective_id paddingPorts_injective
    (a := ⟨regs, operandStacks shape input []⟩)
    (b := ⟨finalRegs, operandStacks (padTo shape input) [] []⟩) trace
  have hstart : workStacks shape input [] stk = stk := by
    funext j
    fin_cases j <;> simp [workStacks, hs, hi, ht]
  refine ⟨finalRegs, ?_, hreg⟩
  simpa only [paddingCmd, embed_padding, hstart] using run

private theorem copy_eval (src dst tmp : Fin 6)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (regs : Fin 8 → Bool) (stk : Stacks (Fin 6)) (ht : stk tmp = []) :
    Eval (.call (copyProgram src dst tmp (1 : Fin 8) 3)) (7 * (stk src).length + 5)
      ⟨regs, stk⟩ ⟨readRegs regs 1 3 none, copyStacks src dst stk⟩ := by
  apply Eval.call
  have t := halt_after_trace _
    (copyProgram_trace src dst tmp (1 : Fin 8) 3 hsd hst htd (by decide) regs stk ht)
    7 rfl rfl
  simpa [StructuredProgram.State.withPC, copyResult, copyProgram, Nat.add_assoc] using t

/-- Ports 0 and 1 are preserved masters; port 2 becomes the working assignment;
ports 3, 4, and 5 are scratch. -/
abbrev command : Cmd 8 6 :=
  .seq (.call (copyProgram 1 2 4 1 3))
    (.seq (.call (copyProgram 0 3 4 1 3)) paddingCmd)

theorem command_eval (rank shape : List Bool) (regs : Fin 8 → Bool) (stk : Stacks (Fin 6))
    (hrank : stk 0 = rank) (hshape : stk 1 = shape) (hlen : rank.length ≤ shape.length)
    (ho : stk 2 = []) (hc : stk 3 = []) (ht : stk 4 = []) (hb : stk 5 = []) :
    ∃ finalRegs : Fin 8 → Bool,
      Eval command (7 * rank.length + 14 * shape.length + 16) ⟨regs, stk⟩
        ⟨finalRegs, Function.update stk 2 (padTo shape rank)⟩ ∧
      finalRegs 0 = regs 0 := by
  have a := copy_eval 1 2 4 (by decide) (by decide) (by decide) regs stk ht
  have b := copy_eval 0 3 4 (by decide) (by decide) (by decide)
    (readRegs regs 1 3 none) (copyStacks 1 2 stk) (by simpa [copyStacks] using ht)
  obtain ⟨finalRegs, c, hreg⟩ := padding_eval shape rank
    (readRegs (readRegs regs 1 3 none) 1 3 none) (copyStacks 0 3 (copyStacks 1 2 stk)) hlen
    (by simp [copyStacks, hshape, ho]) (by simp [copyStacks, hrank, hc])
    (by simpa [copyStacks] using hb)
  have hfinal : workStacks (padTo shape rank) [] [] (copyStacks 0 3 (copyStacks 1 2 stk)) =
      Function.update stk 2 (padTo shape rank) := by
    funext j
    fin_cases j <;> simp [workStacks, copyStacks, hc, hb]
  refine ⟨finalRegs, ?_, ?_⟩
  · have total := a.seq (b.seq c)
    rw [hfinal] at total
    dsimp [command]
    convert total using 1 ; simp [copyStacks, hrank, hshape] ; omega
  · simpa [readRegs] using hreg

/-- Twenty-six labels, independently of rank length and declared width. -/
abbrev program : Program 8 6 26 := compiled command 0 2

theorem program_trace (rank shape : List Bool) (regs : Fin 8 → Bool) (stk : Stacks (Fin 6))
    (hrank : stk 0 = rank) (hshape : stk 1 = shape) (hlen : rank.length ≤ shape.length)
    (ho : stk 2 = []) (hc : stk 3 = []) (ht : stk 4 = []) (hb : stk 5 = []) :
    ∃ finalRegs : Fin 8 → Bool,
      @Trace 8 6 (size command + 1) program (7 * rank.length + 14 * shape.length + 17)
        ⟨some program.entry, regs, stk⟩
        ⟨none, finalRegs, Function.update stk 2 (padTo shape rank)⟩ ∧
      finalRegs 0 = regs 0 := by
  obtain ⟨finalRegs, h, hreg⟩ := command_eval rank shape regs stk
    hrank hshape hlen ho hc ht hb
  refine ⟨finalRegs, ?_, hreg⟩
  have t := compiled_halt_trace h 0 2
  have hp : compiled command 0 2 = program := by rfl
  rw [hp] at t
  simpa [StructuredProgram.State.withPC, Nat.add_assoc] using t

theorem padTo_eq_append_zeros (shape rank : List Bool) (hlen : rank.length ≤ shape.length) :
    padTo shape rank = rank ++ List.replicate (shape.length - rank.length) false := by
  induction shape generalizing rank with
  | nil =>
      have hr : rank = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      simp [hr, padTo]
  | cons b shape ih =>
      cases rank with
      | nil => simp [padTo, ih [] (Nat.zero_le _), List.replicate_succ]
      | cons a rank =>
          have hl : rank.length ≤ shape.length := by simpa using hlen
          simp [padTo, ih rank hl]

theorem output_length (shape rank : List Bool) (stk : Stacks (Fin 6)) :
    ((Function.update stk 2 (padTo shape rank)) 2).length = shape.length := by
  simp [padTo_length]

theorem output_value (shape rank : List Bool) (stk : Stacks (Fin 6))
    (hlen : rank.length ≤ shape.length) :
    BinaryArithmetic.toNat ((Function.update stk 2 (padTo shape rank)) 2) =
      BinaryArithmetic.toNat rank := by
  simpa using padTo_correct shape rank hlen

/-- The rank, shape, and all scratch stacks are unchanged in the final state. -/
theorem output_frame (shape rank : List Bool) (stk : Stacks (Fin 6)) (j : Fin 6)
    (hj : j ≠ 2) :
    Function.update stk 2 (padTo shape rank) j = stk j := by simp [hj]

theorem program_primitive (rank shape : List Bool) (regs : Fin 8 → Bool) (stk : Stacks (Fin 6))
    (hrank : stk 0 = rank) (hshape : stk 1 = shape) (hlen : rank.length ≤ shape.length)
    (ho : stk 2 = []) (hc : stk 3 = []) (ht : stk 4 = []) (hb : stk 5 = []) :
    ∃ finalRegs : Fin 8 → Bool,
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * (7 * rank.length + 14 * shape.length + 17))
        (primitiveCfg program ⟨some program.entry, regs, stk⟩)
        (primitiveCfg program ⟨none, finalRegs, Function.update stk 2 (padTo shape rank)⟩) ∧
      finalRegs 0 = regs 0 := by
  obtain ⟨finalRegs, h, hreg⟩ := program_trace rank shape regs stk
    hrank hshape hlen ho hc ht hb
  exact ⟨finalRegs, primitive_trace program h, hreg⟩

end SubexponentialSAT.RankAssignmentProgram

end OAI.Algorithms
