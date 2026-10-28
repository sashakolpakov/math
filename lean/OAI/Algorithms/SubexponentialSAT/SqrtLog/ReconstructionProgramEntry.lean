import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramCalls

namespace OAI.Algorithms

/-! Physical preparation of the low scalar caches used by dense polynomial
addition. The high copies remain available to all native ring services. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Entry

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram

def prepare : Code := .seq (copy 194 5) (copy 202 10)

def prepared (s : Fin 320 → List Bool) : Fin 320 → List Bool :=
  Function.update (Function.update s 5 (s 194)) 10 (s 202)

def budget (modulusBits widthTokens : ℕ) : ℕ := 7 * modulusBits + 7 * widthTokens + 10

theorem prepare_run (d : Data) (h5 : d.stacks 5 = []) (h10 : d.stacks 10 = [])
    (h318 : d.stacks 318 = []) :
    ∃ rf, Eval prepare (budget (d.stacks 194).length (d.stacks 202).length)
      d ⟨rf, prepared d.stacks⟩ := by
  have h1 := copy_run d 194 5 (by decide) (by decide) (by decide) h318
  let d1 := afterCopy d 194 5 0 1
  have h2 := copy_run d1 202 10 (by decide) (by decide) (by decide)
    (by simpa [d1, afterCopy, StackRoutines.copyStacks] using h318)
  have h := h1.seq h2
  have he : (afterCopy d1 202 10 0 1).stacks = prepared d.stacks := by
    funext i
    simp [d1, afterCopy, StackRoutines.copyStacks, prepared, h5, h10]
  have hstate : afterCopy d1 202 10 0 1 =
      (⟨(afterCopy d1 202 10 0 1).regs, prepared d.stacks⟩ : Data) := state_ext rfl he
  rw [hstate] at h
  refine ⟨(afterCopy d1 202 10 0 1).regs, ?_⟩
  convert h using 1 <;> simp [prepare, budget, d1, afterCopy, StackRoutines.copyStacks] ; omega

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Entry

end OAI.Algorithms
