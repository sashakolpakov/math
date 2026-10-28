import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendUniform
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBoundsQuery
import OAI.Algorithms.SubexponentialSAT.SparsificationBudgetProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls LeafScopeInputBounds
attribute [local simp] Fin.coe_ofNat_eq_mod

def numericMajorant (S : ℕ) : ℕ := 16*S+11+
  conversionCost S+conversionCost S+conversionCost S+conversionCost (2*S)+conversionCost (2*S^2)
def highMajorant (S : ℕ) : ℕ :=
  7*S+5+300001*(2*S+37)^3+(7*(16*S^3)+5+7*S+5+7*(S+18)+5)+
    270000*(16*S^3+4*S+40)^3+17*S+14
def measureMajorant (S : ℕ) : ℕ :=
  7*(16*S^3)+5+7*S+5+(10*(16*S^3)+7*S+12)+
    (S*(1000*(16*S^3+S+S+1)^2+50*(S+1)+50+1)+1)+2+
    7*S+5+7*(16*S^3)+5+3+(32*(S+1)+101)*(16*S^3+1)+3*S+10
def scanMajorant (S : ℕ) : ℕ :=
  (42*S+30+21+HashScopeProgram.Complete.polynomialBound S+7*(16*S^3))+
    highMajorant S+measureMajorant S+numericMajorant S

theorem conversionCost_mono {a b : ℕ} (h : a ≤ b) : conversionCost a ≤ conversionCost b := by
  unfold conversionCost
  gcongr

theorem numericCost_bound (q : Query) (k : ℕ) (hv : q.Valid) :
    q.numericCost k ≤ numericMajorant (capacity q k) := by
  have h := query_bounds q k hv
  have hk := (SparsificationBudgetProgram.bits_length_le k).trans h.widthParameter
  have hf := conversionCost_mono h.free
  have ho := conversionCost_mono h.occurrence
  have ha := conversionCost_mono h.arity
  have hq := conversionCost_mono h.factors
  have hm := conversionCost_mono h.incidences
  have hn := h.ambientBits
  have hc := h.modulus
  unfold Query.numericCost numericCost numericMajorant
  omega

theorem scopeCopyBudget_bound (q : Query) (k : ℕ) (hv : q.Valid) :
    q.scopeCopyBudget ≤ 42*capacity q k+30 := by
  have h := query_bounds q k hv
  have h0 := h.master
  have h1 := h.rowBits
  have h2 := h.index
  have h3 := h.modulus
  have h4 := h.width
  have h5 := h.eight
  unfold Query.scopeCopyBudget
  omega

theorem log_bound (q : Query) (k : ℕ) :
    Asymptotic.L (BinaryArithmetic.toNat q.ambient) ≤ capacity q k+17 := by
  have h := Nat.log2_le_self (BinaryArithmetic.toNat q.ambient+16)
  unfold Asymptotic.L capacity
  omega

theorem highCapacity_bound (q : Query) (k : ℕ) (hv : q.Valid) :
    q.highCapacity ≤ 16*(capacity q k)^3+4*capacity q k+40 := by
  have h := query_bounds q k hv
  have hs := h.scopeBits
  have hn := h.ambient
  have hb := h.ambientBits
  have hl := log_bound q k
  have ht := Nat.sqrt_le_self (Asymptotic.L (BinaryArithmetic.toNat q.ambient))
  unfold Query.highCapacity EarlyThreshold.threshold
  omega

theorem high_stage_bound (q : Query) (k : ℕ) (hv : q.Valid) :
    7*q.ambient.length+5+EarlyThreshold.runtimeBound q.ambient+
      (7*(LeafStatisticsProgram.scopeBits q.scopeRows).length+5+7*q.ambient.length+5+
        7*(Asymptotic.L (BinaryArithmetic.toNat q.ambient)+1)+5)+
      270000*q.highCapacity^3+17*q.forward.length+14 ≤ highMajorant (capacity q k) := by
  have h := query_bounds q k hv
  have hl := log_bound q k
  have hc := highCapacity_bound q k hv
  have he : EarlyThreshold.runtimeBound q.ambient ≤ 300001*(2*capacity q k+37)^3 := by
    unfold EarlyThreshold.runtimeBound
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    have := h.ambientBits
    omega
  have hh := Nat.mul_le_mul_left 270000 (Nat.pow_le_pow_left hc 3)
  have hb := h.ambientBits
  have hs := h.scopeBits
  have hf := h.forward
  unfold highMajorant
  omega

theorem measure_stage_bound (q : Query) (k : ℕ) (hv : q.Valid) :
    7*(LeafStatisticsProgram.scopeBits q.scopeRows).length+5+7*q.forward.length+5+
      LeafStatisticsProgram.bootBudget q.scopeRows q.forward+
      LeafStatisticsProgram.variableBudget q.scopeRows 0 q.forward+2+
      7*q.forward.length+5+7*(LeafStatisticsProgram.scopeBits q.scopeRows).length+5+3+4+
      RecordPrograms.budget (LeafStatisticsProgram.Arity.cost q.forward)
        (q.scopeRows.map (Encoding.encodeList Encoding.encodeNat))+
      3*(totals q.scopeRows q.forward).uncovered+10 ≤ measureMajorant (capacity q k) := by
  have h := query_bounds q k hv
  have hb := LeafStatisticsProgram.bootBudget_le q.scopeRows q.forward
  have hvb := LeafStatisticsProgram.variableBudget_le q.scopeRows q.forward.length 0 q.forward (by omega)
  have hva : LeafStatisticsProgram.variableBudget q.scopeRows 0 q.forward ≤
      capacity q k*(1000*(16*(capacity q k)^3+capacity q k+capacity q k+1)^2+
        50*(capacity q k+1)+50+1)+1 := by
    apply hvb.trans
    unfold LeafStatisticsProgram.uniformStepBudget
    gcongr
    · exact h.forward
    · exact h.scopeBits
    · exact h.scopeCount
    · exact h.forward
    · exact h.scopeCount
  have hab := LeafStatisticsProgram.Arity.totalBudget_le q.forward q.scopeRows
  have hab' : 4+RecordPrograms.budget (LeafStatisticsProgram.Arity.cost q.forward)
      (q.scopeRows.map (Encoding.encodeList Encoding.encodeNat)) ≤
      (32*(capacity q k+1)+101)*(16*(capacity q k)^3+1) := by
    apply hab.trans
    change (32*(q.forward.length+1)+101)*((LeafStatisticsProgram.scopeBits q.scopeRows).length+1) ≤ _
    gcongr
    · exact h.forward
    · exact h.scopeBits
  have hs := h.scopeBits
  have hf := h.forward
  have hu := h.uncovered
  unfold measureMajorant
  omega

theorem coreInputBudget_bound (q : Query) (k : ℕ) (hv : q.Valid) :
    q.coreInputBudget k ≤ scanMajorant (capacity q k)+
      LeafParametersProgram.Execute.runtimeBound (q.input k) (q.inputLengths k)+1 := by
  have hr := scopeCopyBudget_bound q k hv
  have hs := scope_cost_le q k hv
  have hb := (query_bounds q k hv).scopeBits
  have hh := high_stage_bound q k hv
  have hm := measure_stage_bound q k hv
  have hn := numericCost_bound q k hv
  unfold Query.coreInputBudget scanMajorant
  dsimp only
  omega

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
