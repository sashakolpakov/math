import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchState

namespace OAI.Algorithms

/-! The literal state at a position/color boundary of the local-basis batch.
Loop counters and accumulated output are explicit caller-owned words. -/

namespace SubexponentialSAT.Subexp.LocalBasisBatchProgram

def boundaryState (ctx : Context) (width : Word) (t g : ℕ)
    (outerAcc innerAcc outerFuel innerFuel : Word) (regs : Fin 32 → Bool) : Data :=
  ⟨regs, fun j =>
    if j = 117 then List.replicate t true else
    if j = 118 then List.replicate g true else
    if j = 119 then outerFuel else
    if j = 120 then innerFuel else
    if j = 121 then outerAcc else
    if j = 122 then innerAcc else (outputState ctx width [] regs).stacks j⟩

end SubexponentialSAT.Subexp.LocalBasisBatchProgram

end OAI.Algorithms
