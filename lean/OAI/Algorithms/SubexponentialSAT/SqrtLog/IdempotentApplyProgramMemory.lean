import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramMemory

namespace OAI.Algorithms

/-! Native high-register movement used by the Horner controller. Each rule
retains the full cost of copying or reversing the actual serialized data. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open BitProgram StructuredCalls
open HashCircuitProgram.Native

theorem copy_high_high (regs : Fin 8 → Bool) (low : Fin 56 → List Bool)
    (high : Fin 40 → List Bool) (src dst tmp : Fin 40)
    (hsd : src≠dst) (hst : src≠tmp) (htd : tmp≠dst) (htmp : high tmp=[]) :
    Eval (copy (Memory.highPort src) (Memory.highPort dst) (Memory.highPort tmp))
      (7*(high src).length+5) (Memory.state regs low high)
      (Memory.state (readRegs regs 0 1 none) low
        (Function.update high dst (high src++high dst))) := by
  have h:=copy_eval (Memory.state regs low high)
    (Memory.highPort src) (Memory.highPort dst) (Memory.highPort tmp)
    (Memory.high_injective.ne hsd) (Memory.high_injective.ne hst)
    (Memory.high_injective.ne htd) (by simpa [Memory.state] using htmp)
  simpa only [copied,Memory.state,StackRoutines.copyStacks,Memory.tapes_high,
    Memory.update_high] using h

theorem transfer_high_high (regs : Fin 8 → Bool) (low : Fin 56 → List Bool)
    (high : Fin 40 → List Bool) (src dst : Fin 40) (hsd : src≠dst) :
    Eval (transfer (Memory.highPort src) (Memory.highPort dst))
      (3*(high src).length+3) (Memory.state regs low high)
      (Memory.state (readRegs regs 0 1 none) low
        (Function.update (Function.update high src []) dst ((high src).reverse++high dst))) := by
  have h:=transfer_eval (Memory.state regs low high)
    (Memory.highPort src) (Memory.highPort dst) (Memory.high_injective.ne hsd)
  simpa only [transferred,Memory.state,StackRoutines.transferStacks,Memory.tapes_high,
    Memory.update_high] using h

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
