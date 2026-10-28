import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryFrontend
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryBranches

namespace OAI.Algorithms

/-! The failed-guard path performs no packing or arithmetic setup. It has an
actual zero-count execution with paid cleanup. Reachable-query correctness
separately proves that its resource guard holds. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

def guarded (k : ℕ) (next : Code) : Code :=
  .seq (LeafQueryFrontend.frontend k) (.ite 8 next cleanup)

theorem guard_false_eval (k : ℕ) (next : Code) (q : LeafQueryFrontend.Query) (a : Data)
    (hv : q.Valid) (hr : q.Ready a) (ho : q.OutputEmpty a)
    (hguard : ¬Guard (q.input k)) (hzero : a.stacks 323=[])
    (W : ℕ) (hw : ∀i,(a.stacks i).length ≤ W) :
    ∃ n front counted prepared beforeClean tau l,
      Eval (guarded k next) n a (cleaned front) ∧
      n ≤ LeafQueryFrontend.frontendBudget q k counted prepared beforeClean tau l+
        cleanupBound (W+LeafQueryFrontend.frontendBudget q k counted prepared beforeClean tau l)+1 ∧
      (cleaned front).stacks 323=[] ∧
      (cleaned front).stacks 320=a.stacks 320 ∧
      (cleaned front).stacks 322=a.stacks 322 ∧
      (∀i,¬Protected i → (cleaned front).stacks i=[]) := by
  obtain ⟨nf,front,counted,prepared,beforeClean,tau,l,w,he,hn,ht,h704,h718,h338,h719,h134,
    hex,h141,hbank,hshape,hg,hclean,hframe⟩ :=
    LeafQueryFrontend.frontend_eval q k a hv hr ho
  have hfalse : front.regs 8=false := by
    cases hb : front.regs 8
    · rfl
    · exact False.elim (hguard (hg.mp hb))
  have hw' : ∀i,(front.stacks i).length ≤
      W+LeafQueryFrontend.frontendBudget q k counted prepared beforeClean tau l := by
    intro i
    exact (eval_width he W hw i).trans (Nat.add_le_add_left hn W)
  have hcost := cleanupCost_le front _ hw'
  have hf (i : Fin 768) (hi : i∈([320,322,323] : List (Fin 768))) :
      front.stacks i=a.stacks i := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl <;>
      exact hframe _ (Or.inl (by decide)) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by intro j; fin_cases j <;> decide)
  refine ⟨nf+(cleanupCost front+1),front,counted,prepared,beforeClean,tau,l,
    he.seq (.ite_false hfalse (cleanup_eval front)),?_,?_,?_,?_,cleaned_empty front⟩
  · change cleanupCost front ≤ cleanupBound _ at hcost
    omega
  · rw [cleaned_frame front 323 (by decide),hf 323 (by simp),hzero]
  · exact (cleaned_frame front 320 (by decide)).trans (hf 320 (by simp))
  · exact (cleaned_frame front 322 (by decide)).trans (hf 322 (by simp))

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
