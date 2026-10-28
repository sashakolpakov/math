import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeMomentLoop

namespace OAI.Algorithms

/-! Install the actual generated node table in the local worker's lookup master. -/

namespace SubexponentialSAT.SubexpNodeIndexMaster

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpNodeMomentLoop (Data)

abbrev command : Cmd 16 320 :=
  .seq (SubexpNodeMomentLoop.clear 125) (SubexpNodeMomentLoop.copy 300 125)

def result (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks 125 (d.stacks 300)⟩

def cost (d : Data) : ℕ := 2 * (d.stacks 125).length + 7 * (d.stacks 300).length + 8

theorem command_eval (d : Data) (htmp : d.stacks 305 = []) :
    Eval command (cost d) d (result d) := by
  let cleared := SubexpNodeMomentLoop.clearOut d 125
  have hc := SubexpNodeMomentLoop.clear_eval d 125
  have hp := copy_eval cleared 300 125 305 0 1
    (by decide) (by decide) (by decide) (by decide)
    (by simpa [cleared, SubexpNodeMomentLoop.clearOut] using htmp)
  have he : afterCopy cleared 300 125 0 1 = result d := by
    apply state_ext
    · simp [cleared, SubexpNodeMomentLoop.clearOut, afterCopy, result,
        StackRoutines.readRegs_reset]
    · simp [cleared, SubexpNodeMomentLoop.clearOut, afterCopy, result,
        StackRoutines.copyStacks]
  rw [he] at hp
  have h := hc.seq hp
  convert h using 1 <;>
    simp [command, cost, SubexpNodeMomentLoop.copy, cleared,
      SubexpNodeMomentLoop.clearOut]
  all_goals omega

theorem result_frame (d : Data) (i : Fin 320) (hi : i ≠ 125) :
    (result d).stacks i = d.stacks i := by
  simp [result, hi]

theorem result_nodes (d : Data) (nodes : List (List Bool))
    (h : d.stacks 300 = Encoding.encodeList id nodes) :
    (result d).stacks 125 = Encoding.encodeList id nodes := by
  simpa [result] using h

abbrev program : Program 16 320 (size command + 1) := compiled command 300 125

theorem program_trace (d : Data) (htmp : d.stacks 305 = []) :
    Trace program (cost d + 1)
      (d.withPC (some program.entry)) ((result d).withPC none) :=
  compiled_halt_trace (command_eval d htmp) 300 125

end SubexponentialSAT.SubexpNodeIndexMaster

end OAI.Algorithms
