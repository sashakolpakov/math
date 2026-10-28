import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionLeafIO
import OAI.Algorithms.SubexponentialSAT.SubexpSetupBoundSpec

namespace OAI.Algorithms

/-! Linear physical overhead of the complete wide-leaf I/O wrapper. -/
namespace SubexponentialSAT.SqrtLog.Execution.LeafIO

open BitProgram StructuredCalls SubexpSetupStorage

theorem prepareCost_le (a : Data) (B : ℕ) (ha : WordBound B a) :
    prepareCost a ≤ 21*B+15 := by
  have h0 := ha 896
  have h1 := ha 897
  have h2 := ha 898
  unfold prepareCost
  omega

theorem exported_wordBound (a : Data) (B : ℕ) (ha : WordBound B a) :
    WordBound (2*B) (exported a) := by
  intro i
  by_cases h : i = 899
  · subst i
    simp [StackRoutines.clearStacks, List.length_append]
    have h0 := ha 787
    have h1 := ha 899
    omega
  · change (StackRoutines.copyStacks 787 899
      (StackRoutines.clearStacks 895 a.stacks) i).length ≤ 2 * B
    rw [StackRoutines.copyStacks_frame 787 899 i _ h]
    by_cases hi : i = 895
    · subst i
      simp
    · rw [StackRoutines.clearStacks_frame 895 i a.stacks hi]
      exact (ha i).trans (by omega)

theorem finishCost_le (a : Data) (B : ℕ) (ha : WordBound B a) :
    finishCost a ≤ 4000*(B+1) := by
  have hw := exported_wordBound a B ha
  have hs : (workerPorts.map (fun i => ((exported a).stacks i).length)).sum ≤
      workerPorts.length*(2*B) := by
    change (workerPorts.map (fun i =>
      (StackRoutines.copyStacks 787 899 (StackRoutines.clearStacks 895 a.stacks) i).length)).sum ≤
        workerPorts.length * (2 * B)
    induction workerPorts with
    | nil => simp
    | cons i is ih =>
        simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
        have hi := hw i
        change (StackRoutines.copyStacks 787 899
          (StackRoutines.clearStacks 895 a.stacks) i).length ≤ 2 * B at hi
        omega
  have hlen : workerPorts.length = 896 := by simp [workerPorts]
  have h0 := ha 895
  have h1 := ha 787
  unfold finishCost
  rw [hlen] at hs ⊢
  omega

/-- The wrapper overhead is linear in the actual core transition count and
incoming maximum word length. Dirty output storage cannot hide cleanup cost. -/
theorem command_bounded_eval (core : Cmd 40 896) (a : Data) (B : ℕ)
    (hword : WordBound B a) (ha : Ready a) {t : ℕ} {b : State 40 896}
    (hb : Eval core t (projectState id work (prepared a)) b) :
    ∃ total out, Eval (command core) total a out ∧
      total ≤ 100000*(B+t+1) ∧
      out = finished (embedState id work (prepared a) b) := by
  let middle := embedState id work (prepared a) b
  have hp := prepare_eval a ha
  have hc := eval_liftCommand_from_state core 784 787 id work (prepared a)
    Function.injective_id work_injective hb
  have hpw := SubexpSetupBoundSpec.eval_wordBound hword hp
  have hmw := SubexpSetupBoundSpec.eval_wordBound hpw hc
  have hpc := prepareCost_le a B hword
  have hfc := finishCost_le middle (B+prepareCost a+(t+1)) hmw
  refine ⟨prepareCost a+(t+1)+finishCost middle,finished middle,
    command_eval core a ha hb,?_,rfl⟩
  omega

end SubexponentialSAT.SqrtLog.Execution.LeafIO

end OAI.Algorithms
