import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendCalls

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem earlyCall_eval_bounded (a : Data) (ambient : List Bool)
    (hp : projectState r8 early a=LeafParametersProgram.Bank.state (a.regs ∘ r8)
      (EarlyThreshold.inputWords ambient)) :
    ∃ n ≤ EarlyThreshold.runtimeBound ambient, ∃ rf w,
      Eval earlyCall n a (embedState r8 early a (LeafParametersProgram.Bank.state rf w)) ∧
      BinaryArithmetic.toNat (w 16)=EarlyThreshold.threshold (BinaryArithmetic.toNat ambient) ∧
      w 0=ambient ∧ (∀ j, j≠0 → j≠13 → j≠16 → w j=[]) ∧
      (w 16).length ≤ Asymptotic.L (BinaryArithmetic.toNat ambient)+1 := by
  obtain ⟨n,rf,w,he,hn,_,hv,h0,_,hl,hz⟩ := EarlyThreshold.input_execution ambient (a.regs ∘ r8)
  have ht := compiled_halt_trace he 0 16
  rw [←hp] at ht
  have hcall := eval_call_from_state EarlyThreshold.program r8 early a
    (registers_injective ..) (block_injective ..) ht
  exact ⟨n+1,hn,rf,w,hcall,hv,h0,hz,hl⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
