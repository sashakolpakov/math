import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramCofactorState
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramCalls

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (ServiceSpec LowFrame)

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

abbrev command (multiply : Cmd 16 256) : Code :=
  copy 258 215 ;; copy 257 215 ;; copy 207 240 ;;
    lowerCall (Cofactor.scan multiply) 215 240 ;; move 240 262

def budget (N K W J : ℕ) : ℕ :=
  N * (Cofactor.includeBudget K W J + 25 * W + 28) + 13 * W + 24

def cleanPorts : List (Fin 320) :=
  [120,121,122,215,217,218,219,223,229,240,241,244,245,246,262,318,319]

theorem command_run {C : Type*} (encode : C → List Bool)
    (multiply : Cmd 16 256) (mulOp : C → C → C) (K W J : ℕ)
    (d : Data) (remaining processed : List C) (unit minusOne : C)
    (hm : ServiceSpec (d.stacks ∘ localPorts) encode multiply mulOp K)
    (hw : ∀ a, (encode a).length = W) (hW : 0 < W)
    (hr : d.stacks 257 = remaining.flatMap encode)
    (hp : d.stacks 258 = processed.flatMap encode)
    (hu : d.stacks 207 = encode unit) (hn : d.stacks 211 = encode minusOne)
    (hJ : d.stacks 243 = List.replicate J true) (hwidth : (d.stacks 104).length = W)
    (hc : ∀ i ∈ cleanPorts, d.stacks i = []) :
    ∃ n ≤ budget (remaining.length + processed.length) K W J, ∃ rf,
      Eval (command multiply) n d
        ⟨rf, Function.update d.stacks 262
          (encode ((remaining ++ processed).foldl (Cofactor.includeValue mulOp minusOne J) unit))⟩ := by
  let value := (remaining ++ processed).foldl (Cofactor.includeValue mulOp minusOne J) unit
  let d1 := afterCopy d 258 215 0 1
  let d2 := afterCopy d1 257 215 0 1
  let d3 := afterCopy d2 207 240 0 1
  let s := d3.stacks ∘ localPorts
  have h1 := copy_run d 258 215 (by decide) (by decide) (by decide) (hc 318 (by simp [cleanPorts]))
  have h2 := copy_run d1 257 215 (by decide) (by decide) (by decide)
    (by simpa [d1, afterCopy, StackRoutines.copyStacks] using hc 318 (by simp [cleanPorts]))
  have h3 := copy_run d2 207 240 (by decide) (by decide) (by decide)
    (by simpa [d2, d1, afterCopy, StackRoutines.copyStacks] using hc 318 (by simp [cleanPorts]))
  have hf : LowFrame (d.stacks ∘ localPorts) s := by
    intro i hi
    have h215 : localPorts i ≠ (215 : Fin 320) := by
      intro he; have hv := congrArg Fin.val he; change i.val = 215 at hv; omega
    have h240 : localPorts i ≠ (240 : Fin 320) := by
      intro he; have hv := congrArg Fin.val he; change i.val = 240 at hv; omega
    simp [s, d3, d2, d1, afterCopy, StackRoutines.copyStacks, Function.comp_def, h215, h240]
  have hscan := Cofactor.scan_state_run (d.stacks ∘ localPorts) encode multiply mulOp minusOne K W J
    hm hw hW s hf (remaining ++ processed) unit
    (by simpa [s, d3, d2, d1, afterCopy, StackRoutines.copyStacks, localPorts] using hn)
    (by simpa [s, d3, d2, d1, afterCopy, StackRoutines.copyStacks, localPorts] using hJ)
    (by simpa [s, d3, d2, d1, afterCopy, StackRoutines.copyStacks, localPorts] using hwidth)
    (by simp [s, d3, d2, d1, afterCopy, StackRoutines.copyStacks, localPorts,
      hr, hp, hc 215 (by simp [cleanPorts]), List.flatMap_append])
    (by simp [s, d3, d2, d1, afterCopy, StackRoutines.copyStacks, localPorts,
      hu, hc 240 (by simp [cleanPorts])])
    (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [s, d3, d2, d1, afterCopy, StackRoutines.copyStacks, localPorts] using hc _ (by simp [cleanPorts]))
  obtain ⟨nl, hnl, rl, hl⟩ := lowerCall_run (Cofactor.scan multiply) 215 240 d3 _ _ hscan
  have he : Function.extend localPorts (Function.update (Function.update s 215 []) 240 (encode value))
      d3.stacks = Function.update (Function.update d3.stacks 215 []) 240 (encode value) := by
    rw [ProgramLinking.extend_update localPorts.injective, ProgramLinking.extend_update localPorts.injective,
      lower_extend_project]
    rfl
  change Eval _ nl d3 ⟨rl, Function.extend localPorts
    (Function.update (Function.update s 215 []) 240 (encode value)) d3.stacks⟩ at hl
  rw [he] at hl
  let d4 : Data := ⟨rl, Function.update (Function.update d3.stacks 215 []) 240 (encode value)⟩
  have h4 := move_run d4 240 262 (by decide) (by decide) (by decide)
    (by simpa [d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks] using hc 319 (by simp [cleanPorts]))
    (by simpa [d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks] using hc 262 (by simp [cleanPorts]))
  have hfinal : (moved d4 240 262).stacks = Function.update d.stacks 262 (encode value) := by
    funext i
    by_cases h215 : i = 215 <;> by_cases h240 : i = 240 <;>
      simp [ d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks, Function.update_apply,
        h215, h240, hc 215 (by simp [cleanPorts]), hc 240 (by simp [cleanPorts])]
  have heq : moved d4 240 262 = (⟨(moved d4 240 262).regs,
      Function.update d.stacks 262 (encode value)⟩ : Data) := state_ext rfl hfinal
  have hrun := h1.seq (h2.seq (h3.seq (hl.seq h4)))
  rw [heq] at hrun
  refine ⟨_, ?_, _, hrun⟩
  have hrl := flatMap_length_of_width encode W hw remaining
  have hpl := flatMap_length_of_width encode W hw processed
  simp only [List.length_append] at hnl
  simp [d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks, hp, hr, hu, hw, hrl, hpl, budget]
  nlinarith

end SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter

end OAI.Algorithms
