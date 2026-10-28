import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeBounds

namespace OAI.Algorithms

/-! A uniform node budget derived from input words and actual table bounds. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeNative
open SubexponentialSAT BitProgram StructuredCalls LeafHeadSetupProgram
open LeafHeadSetupProgram.Bounds SubexponentialSAT.SubexpSetupStorage MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem loaded_wordBound {s : HeadInputs} {a : NodeNative.Data} (ha : Ready s a)
    (B : ℕ) (hb : WordBound B a) : WordBound B (loadedState a) := by
  intro i
  by_cases hi : i∈LayoutMasters.lowPorts
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    have hh := LayoutMasters.loaded_low (LayoutMasters.project a)
      (fun j=>ha.blank _ (low_mem_cleanup j) (by
        intro he; have hv := congrArg Fin.val he
        change 128+j.val=78 at hv
        omega)) j
    change ((LayoutMasters.loaded (LayoutMasters.project a)).stacks (LayoutMasters.low j)).length ≤ B
    rw [hh]
    exact hb _
  · change ((LayoutMasters.loaded (LayoutMasters.project a)).stacks i).length ≤ B
    rw [LayoutMasters.loaded_frame (LayoutMasters.project a) i hi]
    exact hb _

theorem cache_budget_le_sources (a : NodeNative.Data) (B : ℕ)
    (ha : ∀ q∈LeafNodeCacheProgram.copies,(a.stacks q.1).length ≤ B) :
    LeafNodeCacheProgram.budget a ≤ 1001*(B+1) := by
  have hc := copyManyCost_le LeafNodeCacheProgram.copies (LeafNodeCacheProgram.project a) B
    (by simp [LeafNodeCacheProgram.copies,LeafNodeCacheProgram.directCopies]) ha
  have hn := ha (128,340) (by simp [LeafNodeCacheProgram.copies])
  have ho := ha (207,343) (by simp [LeafNodeCacheProgram.copies])
  dsimp only [Prod.fst] at hn ho
  rw [show LeafNodeCacheProgram.copies.length=14 from rfl] at hc
  unfold LeafNodeCacheProgram.budget LeafNodeCacheProgram.localBudget
  rw [LeafNodeCacheProgram.rawOne_length]
  change _ ≤ _ at hc
  dsimp only [LeafNodeCacheProgram.project] at hc ⊢
  omega

theorem Preparation.cache_budget_le {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s a b) (ha : Ready s a) (B : ℕ) (hb : WordBound B a) :
    LeafNodeCacheProgram.budget pr.headEnd ≤ 1001*(B+1) := by
  have hl := loaded_wordBound ha B hb
  apply cache_budget_le_sources
  intro q hq
  have he : External q.1 := by
    simp only [LeafNodeCacheProgram.copies,LeafNodeCacheProgram.directCopies,
      List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hq
    rcases hq with hq|hq
    · rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        norm_num [External,Fin.ext_iff]
    · rcases hq with rfl|rfl <;> norm_num [External,Fin.ext_iff]
  rw [pr.head.frame _ he,pr.loaded_words]
  exact hl _

theorem Preparation.head_budget_le {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s a b) (ha : Ready s a) (B rCap S E K : ℕ) (hb : WordBound B a)
    (haddress : s.node.val*s.r+s.r ≤ rCap)
    (hK : (pr.head.tables.map fun h=>h.buckets.length).prod ≤ K)
    (hS : ∀ u ≤ rCap,preparationSize s.n s.N s.rows s.low (s.Q*s.r) u ≤ S)
    (hE : ∀ u ≤ rCap,matrixEnvelope ((loadedState a).stacks 141) s.columnTime s.columnLength s.D
      s.n (selectedHeads s.n s.rows s.low u).length ≤ E) :
    pr.head.steps ≤ headBudget s B rCap S E K := by
  have hl := loaded_wordBound ha B hb
  apply pr.head.steps_le B rCap S E K
  · intro i
    change (pr.loaded.stacks i).length ≤ B
    rw [pr.loaded_words]; exact hl i
  · have hx := hl 128
    change ((Native.project (loadedState a)).stacks 128).length ≤ B at hx
    rw [ha.heads.ambient] at hx
    simpa [unary] using hx
  · have hx := hl 130
    change ((Native.project (loadedState a)).stacks 130).length ≤ B at hx
    rw [ha.heads.colors] at hx
    simpa [unary] using hx
  · have hx := hl 307
    change ((Native.project (loadedState a)).stacks 307).length ≤ B at hx
    rw [ha.heads.node] at hx
    simpa [unary] using hx
  · rw [Native.Inputs.records_bytes]
    have hx := hl 136
    change ((Native.project (loadedState a)).stacks 136).length ≤ B at hx
    rw [ha.heads.plans] at hx
    exact hx
  · have hx := hl 139
    change ((Native.project (loadedState a)).stacks 139).length ≤ B at hx
    rw [ha.heads.height] at hx
    exact hx
  · have hx := hl 138
    change ((Native.project (loadedState a)).stacks 138).length ≤ B at hx
    rw [ha.heads.order] at hx
    simpa [unary] using hx
  · have hx := hl 140
    change ((Native.project (loadedState a)).stacks 140).length ≤ B at hx
    rw [ha.heads.width] at hx
    exact hx
  · exact haddress
  · exact hK
  · exact hS
  · simpa only [pr.loaded_words] using hE

def uniformBudget (s : HeadInputs) (B rCap S E K width d u J H X Y A W : ℕ) : ℕ :=
  14*(7*B+5)+1+(headBudget s B rCap S E K+(1001*(B+1)+
    (LeafSupportInputProgram.cost s.n J+
      (Relational.denseBudget width d s.n u J
        (dictionaryCapacity (Finset.univ : Finset (Fin s.n)) u J)
        H X Y (SupportProgram.count s.n J) K A+Node.cleanupPorts.length*(2*W+3)))))

theorem fullBudget_le {s : HeadInputs} {a b : NodeNative.Data} (pr : Preparation s a b)
    (ha : Ready s a) (B rCap S E K width d u J H X Y A W : ℕ) (hb : WordBound B a)
    (h243 : a.stacks 243=List.replicate J true)
    (haddress : s.node.val*s.r+s.r ≤ rCap)
    (hK : (pr.head.tables.map fun h=>h.buckets.length).prod ≤ K)
    (hS : ∀ v ≤ rCap,preparationSize s.n s.N s.rows s.low (s.Q*s.r) v ≤ S)
    (hE : ∀ v ≤ rCap,matrixEnvelope ((loadedState a).stacks 141) s.columnTime s.columnLength s.D
      s.n (selectedHeads s.n s.rows s.low v).length ≤ E) :
    fullBudget pr width d u J H X Y A W ≤ uniformBudget s B rCap S E K width d u J H X Y A W := by
  have hh := pr.head_budget_le ha B rCap S E K hb haddress hK hS hE
  have hc := pr.cache_budget_le ha B hb
  have hl := LayoutMasters.loadCost_le (LayoutMasters.project a) B (fun i=>hb (LayoutMasters.high i))
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
  unfold fullBudget uniformBudget
  rw [h243,List.length_replicate]
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.NodeNative

end

end OAI.Algorithms
