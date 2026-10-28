import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCleanup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramExports
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramPorts

namespace OAI.Algorithms

/-! The packed layout is constructed beside the live parameter bank. These
equalities bridge the frontend's physical bank to the ring producer after
packing has changed its own registers and private scratch. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

theorem ring_bank_of_frame (a b : Data) (w : Bank.Words) (r : Bank.Regs)
    (ha : projectState Exports.bankRegs Exports.bank a=Bank.state r w)
    (hf : ∀i : Fin 768,340 ≤ i.val → i.val < 417 → b.stacks i=a.stacks i) :
    projectState (LeafRingSetupProgram.registers 8 (by decide)) LeafRingSetupProgram.parameters
      (projectState LeafRingSetupProgram.wideRegisters LeafRingSetupProgram.wideStacks b)=
      Bank.state (b.regs ∘ Exports.bankRegs) w := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    fin_cases i <;> rfl
  · funext i
    change b.stacks (Exports.bank i)=(Bank.state (b.regs ∘ Exports.bankRegs) w).stacks i
    rw [hf (Exports.bank i) (by simp [Exports.bank])
      (by have := i.isLt; simp [Exports.bank]; omega)]
    exact congrFun (congrArg StructuredProgram.State.stacks ha) i

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
