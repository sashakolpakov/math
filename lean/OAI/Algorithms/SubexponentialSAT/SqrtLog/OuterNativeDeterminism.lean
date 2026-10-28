import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SparsifyIntegrity
import OAI.Algorithms.SubexponentialSAT.SubexpSetupBoundSpec

namespace OAI.Algorithms

/-! Transfer an actual bounded execution to every observed execution of the
same fixed command. No execution oracle or input-dependent code is added. -/
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT BitProgram StructuredCalls

theorem eval_unique {r s : ℕ} (port : Fin s) {cmd : Cmd r s}
    {n m : ℕ} {a b c : State r s} (hb : Eval cmd n a b) (hc : Eval cmd m a c) :
    n=m ∧ b=c := by
  have h := SparsifyIntegrity.terminal_trace_unique
    (compiled_halt_trace hb port port) (compiled_halt_trace hc port port)
    (by simp [BitProgram.step,StructuredProgram.State.withPC])
    (by simp [BitProgram.step,StructuredProgram.State.withPC])
  refine ⟨by omega,?_⟩
  cases b with
  | mk br bs =>
    cases c with
    | mk cr cs =>
      have hr := congrArg BitProgram.Cfg.regs h.2
      have hs := congrArg BitProgram.Cfg.stacks h.2
      simp only [] at hr hs
      cases hr
      cases hs
      rfl

theorem observed_wordBound {r s : ℕ} (port : Fin s) {cmd : Cmd r s}
    {n m W bound : ℕ} {a b c : State r s}
    (ha : SubexpSetupStorage.WordBound W a)
    (hb : Eval cmd n a b) (hc : Eval cmd m a c) (hm : m ≤ bound) :
    n ≤ bound ∧ SubexpSetupStorage.WordBound (W+bound) b := by
  obtain ⟨rfl,rfl⟩ := eval_unique port hb hc
  exact ⟨hm,SubexpSetupBoundSpec.wordBound_mono
    (SubexpSetupBoundSpec.eval_wordBound ha hc) (by omega)⟩

end SubexponentialSAT.SqrtLog.OuterNativeServices

end OAI.Algorithms
