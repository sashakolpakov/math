import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpHornerControl

namespace OAI.Algorithms

/-! Construct the zero accumulator and four-word coefficient-width counter
from the runtime base-width counter, using actual fixed stack programs. -/

namespace SubexponentialSAT.SubexpHornerInitialize

open BitProgram StructuredCalls SubexpScanPrimitives SubexpHornerControl

abbrev copyWidth : Cmd 8 87 := .call (StackRoutines.copyProgram 74 82 83 (0 : Fin 8) 1)
abbrev command : Cmd 8 87 :=
  .seq copyWidth (.seq (.call (zeroFillProgram 82 72 (0 : Fin 8) 1))
    (.seq copyWidth (.call (zeroFillProgram 82 81 (0 : Fin 8) 1))))

theorem command_eval (regs : Fin 8 → Bool) (w : Words)
    (ha : w.accumulator = []) (hw : w.blockWidth = [])
    (hi : w.index = []) (ht : w.scratch = []) :
    Eval command (28 * w.width.length + 16) (state regs w)
      (state (readRegs regs 0 1 none)
        { w with
          accumulator := List.replicate (4 * w.width.length) false
          blockWidth := List.replicate (4 * w.width.length) false }) := by
  let d0 := state regs w
  let d1 := afterCopy d0 74 82 0 1
  let d2 : State 8 87 := ⟨readRegs d1.regs 0 1 none,
    zeroFillStacks 82 72 (d1.stacks 82).length d1.stacks⟩
  let d3 := afterCopy d2 74 82 0 1
  let d4 : State 8 87 := ⟨readRegs d3.regs 0 1 none,
    zeroFillStacks 82 81 (d3.stacks 82).length d3.stacks⟩
  have h1 := copy_eval d0 74 82 83 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [d0, state, store, ht])
  have h2 := zeroFill_eval 82 72 0 1 (by decide) (by decide) d1
  have h3 := copy_eval d2 74 82 83 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [d2, d1, d0, afterCopy, zeroFillStacks, StackRoutines.copyStacks, state, store, ht])
  have h4 := zeroFill_eval 82 81 0 1 (by decide) (by decide) d3
  have hlen1 : (d1.stacks 82).length = w.width.length := by
    simp [d1, d0, afterCopy, StackRoutines.copyStacks, state, store, hi]
  have hlen2 : (d2.stacks 74).length = w.width.length := by
    simp [d2, d1, d0, afterCopy, zeroFillStacks, StackRoutines.copyStacks, state, store]
  have hlen3 : (d3.stacks 82).length = w.width.length := by
    simp [d3, d2, d1, d0, afterCopy, zeroFillStacks, StackRoutines.copyStacks, state, store]
  have hout : d4 = state (readRegs regs 0 1 none)
      { w with
        accumulator := List.replicate (4 * w.width.length) false
        blockWidth := List.replicate (4 * w.width.length) false } := by
    apply state_ext
    · simp [d4, d3, d2, d1, d0, afterCopy, state, StackRoutines.readRegs_reset]
    · funext i
      by_cases h72 : i = 72 <;> by_cases h81 : i = 81 <;> by_cases h82 : i = 82 <;>
        simp [d4, d3, d2, d1, d0, afterCopy, zeroFillStacks, StackRoutines.copyStacks,
          state, store, h72, h81, h82, ha, hw, hi]
  have hh := h1.seq (h2.seq (h3.seq h4))
  change Eval command _ _ d4 at hh
  rw [hout] at hh
  convert hh using 1
  simp only [hlen1, hlen2, hlen3]
  change 28 * w.width.length + 16 =
    (7 * w.width.length + 5) + (7 * w.width.length + 3 +
      (7 * w.width.length + 5 + (7 * w.width.length + 3)))
  omega

end SubexponentialSAT.SubexpHornerInitialize

end OAI.Algorithms
