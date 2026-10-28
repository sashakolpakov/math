import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramEntryBank
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

namespace OAI.Algorithms

/-! The closed instruction table for node/head setup. The incidence entry is
the actual metadata/guard/integer program, wrapped by the paid original-owner
fiber scan and sum. There is no runtime entry-value callback in this code.
The complete semantic and quantitative refinement is proved separately. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def entry : Cmd 16 256 := LayoutFiberSumProgram.command LayoutProgram.EntryBank.command
def command : Cmd 16 768 := LeafHeadSetupProgram.command entry
def program := LeafHeadSetupProgram.program entry
def wideProgram := LeafHeadSetupProgram.wideProgram entry

theorem instruction_table_fixed : ∃ l : ℕ, Nonempty (Program 40 768 l) :=
  ⟨_,⟨wideProgram⟩⟩


theorem wide_eval (a : State 40 768) (b : LeafHeadSetupProgram.Data) {n : ℕ}
    (he : Eval command n (projectState LeafHeadSetupProgram.wideRegisters id a) b) :
    Eval (.call wideProgram) (n+1) a
        (embedState LeafHeadSetupProgram.wideRegisters id a b) ∧
      (∀ i : Fin 40,16 ≤ i.val→
        (embedState LeafHeadSetupProgram.wideRegisters id a b).regs i=a.regs i) :=
  by
    change Eval (LeafHeadSetupProgram.command entry) n
      (projectState LeafHeadSetupProgram.wideRegisters id a) b at he
    change Eval (.call (LeafHeadSetupProgram.wideProgram entry)) (n+1) a
        (embedState LeafHeadSetupProgram.wideRegisters id a b) ∧ _
    exact LeafHeadSetupProgram.wide_execution entry a b (compiled_halt_trace he 307 163)

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end OAI.Algorithms
