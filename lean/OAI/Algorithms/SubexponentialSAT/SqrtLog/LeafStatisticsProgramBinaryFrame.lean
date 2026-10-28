import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgramBinary
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Relocation and frame contract for converting a computed unary statistic
into a binary output without disturbing the enclosing machine's data. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Binary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem lifted_eval {r s : ℕ} (rr : Fin 3 → Fin r) (ss : Fin 3 → Fin s)
    (hr : Function.Injective rr) (hs : Function.Injective ss)
    (d : State r s) (input : List Bool)
    (hp : projectState rr ss d = state (d.regs ∘ rr) input []) :
    ∃ n output, ∃ b : State r s,
      n ≤ input.length*(8*input.length+10)+5 ∧
      BinaryArithmetic.toNat output = input.length ∧ output.length ≤ input.length ∧
      b.stacks (ss 0) = [] ∧ b.stacks (ss 1) = output ∧ b.stacks (ss 2) = [] ∧
      (∀ i, i ∉ Set.range rr → b.regs i = d.regs i) ∧
      (∀ i, i ∉ Set.range ss → b.stacks i = d.stacks i) ∧
      Eval (.call (ProgramLinking.liftProgram program rr ss)) n d b := by
  obtain ⟨n,output,hn,hv,hl,he⟩ := command_eval (d.regs ∘ rr) input
  let small := state (fun _ => false) [] output
  let b := embedState rr ss d small
  have ht := compiled_halt_trace he 0 1
  rw [←hp] at ht
  have hc := eval_call_from_state program rr ss d hr hs (b := small) ht
  refine ⟨n+1,output,b,by omega,hv,hl,?_,?_,?_,?_,?_,hc⟩
  · exact embedState_stack rr ss d small hs 0
  · exact embedState_stack rr ss d small hs 1
  · exact embedState_stack rr ss d small hs 2
  · exact fun i hi => embedState_register_frame rr ss d small i hi
  · exact fun i hi => embedState_stack_frame rr ss d small i hi

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Binary

end OAI.Algorithms
