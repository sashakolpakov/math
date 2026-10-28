import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeSpace

namespace OAI.Algorithms

/-! All costs outside the native head loop are charged from local input words. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeNative
open SubexponentialSAT BitProgram StructuredCalls LeafHeadSetupProgram
open SubexponentialSAT.SubexpSetupStorage MomentsAssembly

def localBudget (s : HeadInputs) (B K width d u J H X Y A W : ℕ) : ℕ :=
  14*(7*B+5)+1+1001*(B+1)+LeafSupportInputProgram.cost s.n J+
    Relational.denseBudget width d s.n u J
      (dictionaryCapacity (Finset.univ : Finset (Fin s.n)) u J)
      H X Y (SupportProgram.count s.n J) K A+Node.cleanupPorts.length*(2*W+3)

theorem fullBudget_le_head_add {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s a b) (ha : Ready s a) (B K width d u J H X Y A W : ℕ)
    (hb : LocalWordBound B a) (h243 : a.stacks 243=List.replicate J true)
    (hK : (pr.head.tables.map fun h=>h.buckets.length).prod ≤ K) :
    fullBudget pr width d u J H X Y A W ≤
      pr.head.steps+localBudget s B K width d u J H X Y A W := by
  have hc := pr.local_cache_budget_le ha B hb
  have hl := local_loadCost_le ha B hb
  have hs := (pr.support_cap J h243).2
  have hk : pr.bucketInputs.length ≤ K := by
    simpa [Preparation.bucketInputs,BucketTupleProgram.enumerate_length] using hK
  have hdense : Relational.denseBudget width d s.n u J
      (dictionaryCapacity (Finset.univ : Finset (Fin s.n)) u J)
      H X Y pr.supports.length pr.bucketInputs.length A ≤
    Relational.denseBudget width d s.n u J
      (dictionaryCapacity (Finset.univ : Finset (Fin s.n)) u J)
      H X Y (SupportProgram.count s.n J) K A := by
    rw [hs]
    unfold Relational.denseBudget
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hk) 2) _
  unfold fullBudget localBudget
  rw [h243,List.length_replicate]
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.NodeNative

end

end OAI.Algorithms
