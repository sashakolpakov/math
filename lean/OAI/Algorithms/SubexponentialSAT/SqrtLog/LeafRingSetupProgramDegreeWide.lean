import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramDegree
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeProgram

namespace OAI.Algorithms

/-! Exact unary degree bytes of the existing producer, attached to an
arbitrary actual execution by deterministic endpoint uniqueness. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls LeafParametersProgram
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem producerCommand_degree
    (a e : State 32 640) (n : ℕ) (he : Eval producerCommand n a e)
    (m : Circuit.Model) (w : Bank.Words) (r : Bank.Regs)
    (hs : Circuit.Shape m w)
    (ha : projectState (registers 8 (by decide)) parameters a=Bank.state r w)
    (W V L : ℕ) (hinit : ∀ i,(a.stacks i).length ≤ W)
    (hv : ∀ i,(Circuit.result Serialization.code m).val i ≤ V)
    (hw : ∀ i,(Circuit.result Serialization.code m).len i ≤ L)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34) :
    e.stacks 204=List.replicate (m.val 34) true := by
  obtain ⟨nc,hnc,e',M,cache,u,hec,hp,hcollector,hdegree⟩ :=
    producerCommand_eval_degree a m w r hs ha W V L hinit hv hw ht hd
  exact (congrArg (fun z => z.stacks 204)
    (SubexpPrimeProgram.eval_result_unique he hec (parameters 0) 300)).trans hdegree

theorem producerWideCall_degree
    (base out : StructuredProgram.State 40 768) (n : ℕ)
    (he : Eval producerWideCall n base out)
    (m : Circuit.Model) (w : Bank.Words) (r : Bank.Regs)
    (hs : Circuit.Shape m w)
    (ha : projectState (registers 8 (by decide)) parameters
      (projectState wideRegisters wideStacks base)=Bank.state r w)
    (W V L : ℕ) (hinit : ∀ i,(base.stacks i).length ≤ W)
    (hv : ∀ i,(Circuit.result Serialization.code m).val i ≤ V)
    (hw : ∀ i,(Circuit.result Serialization.code m).len i ≤ L)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34) :
    out.stacks 204=List.replicate (m.val 34) true := by
  let a := projectState wideRegisters wideStacks base
  obtain ⟨nc,hnc,e,M,cache,u,hec,hp,hcollector,hdegree⟩ :=
    producerCommand_eval_degree a m w r hs ha W V L
      (fun j => hinit (wideStacks j)) hv hw ht hd
  have hrun := compiled_halt_trace hec (parameters 0) 300
  have hwide : Eval producerWideCall (nc+1) base
      (embedState wideRegisters wideStacks base e) :=
    eval_call_from_state producerProgram wideRegisters wideStacks base
      wideRegisters_injective wideStacks_injective hrun
  have heq := SubexpPrimeProgram.eval_result_unique he hwide 0 0
  rw [heq]
  exact (embedState_stack wideRegisters wideStacks base e
    wideStacks_injective 204).trans hdegree

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
