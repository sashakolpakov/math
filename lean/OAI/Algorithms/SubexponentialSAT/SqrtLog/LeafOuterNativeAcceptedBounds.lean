import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeAccepted

namespace OAI.Algorithms

/-! The final query adapter has linear overhead in the actual query runtime,
including cleaning any allocated worker bits. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative
open SubexponentialSAT BitProgram StructuredCalls LeafOuterProgram SubexpSetupStorage

 theorem acceptedCost_le (k : ℕ) (a : Data) (L n : ℕ) (ha : WordBound L a)
    (b : State 40 768)
    (he : Eval (LeafProgram.Query.accepted k) n (projectState id workerStack (finalStaged a)) b) :
    acceptedCost a n b ≤ 5000*(L+n+1) := by
  have hstage := routes_wordBound masterRoutes a L ha
  have hrun := workerCall_eval (LeafProgram.Query.accepted k) (finalStaged a) b n he
  have hafter : WordBound (L+(n+1)) (workerResult (finalStaged a) b) :=
    SubexpSetupBoundSpec.eval_wordBound hstage hrun
  let e := workerResult (finalStaged a) b
  have hroute : WordBound (L+(n+1)) (routed (workerStack 323,788) e) := by
    intro i
    by_cases hi : i=788
    · subst i; simpa [routed] using hafter (workerStack 323)
    · simpa [routed,hi] using hafter i
  have hclean := cleanup_budget_le _ _ hroute
  have hc := routes_cost_bound masterRoutes a L ha
  have hsrc := hafter (workerStack 323)
  have hdst := hafter 788
  have h787 := ha 787
  change stageFinalCost a ≤ 5*(9*L+8)+3 at hc
  unfold acceptedCost exportCost routeCost
  dsimp only [e] at hclean
  dsimp only at *
  omega

theorem accepted_bounded_of_native (k : ℕ) (a : Data) (L Q n : ℕ)
    (ha : WordBound L a) (ht : a.stacks 767=[])
    (b : State 40 768)
    (he : Eval (LeafProgram.Query.accepted k) n (projectState id workerStack (finalStaged a)) b)
    (hn : n ≤ Q) (h767 : b.stacks 767=[]) :
    ∃ t c, t ≤ 5000*(L+Q+1) ∧ Eval (acceptedCount k) t a c ∧ c.stacks 787=[] ∧
      c.stacks 788=b.stacks 323 ∧ WorkerEmpty c ∧
      (∀ i : Fin 896, 768 ≤ i.val → i≠787 → i≠788 → c.stacks i=a.stacks i) := by
  obtain ⟨c,hc,h787,h788,hw,hf⟩ := accepted_eval_of_native k a ht n b he h767
  have hb := acceptedCost_le k a L n ha b he
  exact ⟨acceptedCost a n b,c,hb.trans (by omega),hc,h787,h788,hw,hf⟩

end SubexponentialSAT.SqrtLog.LeafOuterNative

end OAI.Algorithms
