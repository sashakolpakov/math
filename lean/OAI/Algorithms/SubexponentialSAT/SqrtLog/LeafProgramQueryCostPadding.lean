import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCostEnvelope
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyDomination

namespace OAI.Algorithms

/-! Absorb the numeric query envelope while keeping original input padding,
ordinary parameter size and the assembled search counter separate. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost
open SubexponentialSAT CostAssembly

 theorem branches_le_work (k n : ℕ) (p : Resources)
    (hbase : 0 < p.labelBase) (hheads : 1 ≤ p.heads) (hbits : 1 ≤ p.bits) :
    2^p.branchVars ≤ assembledWork k n p := by
  have hc : 1 ≤ hashCalls n p.clauses
      (SparseCode.distanceDenom p.clauses p.initialOccurrence) := by unfold hashCalls; omega
  have he : 1 ≤ enumerationWork p.labelBase p.labelRows p.heads p.headSize := by
    have hh : 0 < p.heads := by omega
    change 0 < enumerationWork p.labelBase p.labelRows p.heads p.headSize
    unfold enumerationWork
    positivity
  have ho : 1 ≤ (p.ordinary+1)^8 := Nat.one_le_pow _ _ (by omega)
  have hs : 1 ≤ (SupportProgram.count n (jetOrder k n p)+1)^4 := Nat.one_le_pow _ _ (by omega)
  unfold assembledWork sparseWork
  calc
    _ = 1*2^p.branchVars*1*1*1*1 := by ring
    _ ≤ hashCalls n p.clauses (SparseCode.distanceDenom p.clauses p.initialOccurrence)*
        2^p.branchVars*enumerationWork p.labelBase p.labelRows p.heads p.headSize*
        p.bits*(p.ordinary+1)^8*(SupportProgram.count n (jetOrder k n p)+1)^4 := by gcongr
    _ ≤ _ := Nat.le_add_left _ _

 theorem queryCap_padding : ∃ C e : ℕ, ∀ (U K N input V work c a b d : ℕ),
    U ≤ c*(input+1)^a*(V+1)^b*(work+1)^d →
    K ≤ c*(input+1)^a*(V+1)^b*(work+1)^d →
    N ≤ c*(input+1)^a*(V+1)^b*(work+1)^d →
    queryCap U K N ≤ C*(c+1)^e*(input+1)^(a*e)*(V+1)^(b*e)*(work+1)^(d*e) := by
  obtain ⟨C,e,h⟩ := queryCap_polynomial
  refine ⟨C,e,?_⟩
  intro U K N input V work c a b d hU hK hN
  have hprod : 1 ≤ (input+1)^a*(V+1)^b*(work+1)^d := by
    have hx : 1 ≤ (input+1)^a := Nat.one_le_pow _ _ (by omega)
    have hy : 1 ≤ (V+1)^b := Nat.one_le_pow _ _ (by omega)
    have hz : 1 ≤ (work+1)^d := Nat.one_le_pow _ _ (by omega)
    nlinarith only [hx,hy,hz,Nat.mul_le_mul hx hy]
  apply (h U K N _ hU hK hN).trans
  calc
    _ ≤ C*((c+1)*(input+1)^a*(V+1)^b*(work+1)^d)^e := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      nlinarith only [hprod]
    _ = _ := by simp only [mul_pow,←pow_mul]; ring

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost

end OAI.Algorithms
