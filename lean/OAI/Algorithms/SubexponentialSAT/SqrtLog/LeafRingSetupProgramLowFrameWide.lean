import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramLowFrame

namespace OAI.Algorithms

/-! Low-workspace preservation for the actual wide producer call.  The
numeric premises are exactly those already used to execute that call. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.LowFrame
open BitProgram StructuredCalls LeafParametersProgram
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem producerWideCall_empty
    (base out : StructuredProgram.State 40 768) (n : ℕ)
    (he : Eval producerWideCall n base out)
    (m : Circuit.Model) (w : Bank.Words) (r : Bank.Regs)
    (hs : Circuit.Shape m w)
    (ha : projectState (registers 8 (by decide)) parameters
      (projectState wideRegisters wideStacks base)=Bank.state r w)
    (W V L : ℕ) (hinit : ∀ i,(base.stacks i).length ≤ W)
    (hv : ∀ i,(Circuit.result Serialization.code m).val i ≤ V)
    (hw : ∀ i,(Circuit.result Serialization.code m).len i ≤ L)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (i : Fin 768) (hi : i.val < 190) (hz : base.stacks i=[]) :
    out.stacks i=[] := by
  let a := projectState wideRegisters wideStacks base
  obtain ⟨nc,hnc,e,M,cache,u,hec,hp,hcollector⟩ :=
    producerCommand_eval a m w r hs ha W V L
      (fun j => hinit (wideStacks j)) hv hw ht hd
  have hrun := compiled_halt_trace hec (parameters 0) 300
  have hwide : Eval producerWideCall (nc+1) base
      (embedState wideRegisters wideStacks base e) :=
    eval_call_from_state producerProgram wideRegisters wideStacks base
      wideRegisters_injective wideStacks_injective hrun
  have heq := SubexpPrimeProgram.eval_result_unique he hwide 0 0
  rw [heq]
  let j : Fin 640 := ⟨i.val,by omega⟩
  have hj : wideStacks j=i := Fin.ext rfl
  rw [←hj,embedState_stack _ _ _ _ wideStacks_injective]
  apply (producerCommand_preservesEmpty j (by exact hi)).run hec
  change base.stacks (wideStacks j)=[]
  rw [hj]
  exact hz

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.LowFrame

end OAI.Algorithms
