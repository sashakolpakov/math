import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendFinish
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem eval_length_le {c : Code} {n : ℕ} {a b : Data} (he : Eval c n a b)
    (i : Fin 768) : (b.stacks i).length ≤ (a.stacks i).length+n := by
  exact Subexp.SequentialProgram.trace_stack_length_le (compiled_trace he i i) i

theorem cleanupCost_le (a : Data) (A : ℕ)
    (ha : ∀ i ∈ cleanupPorts,(a.stacks i).length ≤ A) : cleanupCost a ≤ 524*A+789 := by
  have hsum : (cleanupPorts.map (fun i => (a.stacks i).length)).sum ≤
      (cleanupPorts.map (fun _ => A)).sum := by
    apply List.sum_le_sum
    exact ha
  have hlen : cleanupPorts.length=262 := by simp [cleanupPorts]
  have hc : (cleanupPorts.map (fun _ => A)).sum=262*A := by
    rw [List.map_const',List.sum_replicate,hlen]
    simp []
  rw [hc] at hsum
  unfold cleanupCost
  omega

theorem cleanupCost_le_after_eval {c : Code} {n A : ℕ} {a b : Data}
    (he : Eval c n a b) (ha : ∀ i ∈ cleanupPorts,(a.stacks i).length ≤ A) :
    cleanupCost b ≤ 524*(A+n)+789 := by
  apply cleanupCost_le
  intro i hi
  exact (eval_length_le he i).trans (Nat.add_le_add_right (ha i hi) n)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
