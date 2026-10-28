import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyUniform

namespace OAI.Algorithms

/-! Lower bounds on the assembled counter used to substitute concrete native
costs.  Positivity of actual inventories is explicit, since upper resource
bounds alone do not exclude empty, degenerate records. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

theorem enumeration_le_assembledWork (k n : ℕ) (p : Resources)
    (hbits : 1 ≤ p.bits) :
    enumerationWork p.labelBase p.labelRows p.heads p.headSize ≤
      assembledWork k n p := by
  have hc : 1 ≤ hashCalls n p.clauses
      (SparseCode.distanceDenom p.clauses p.initialOccurrence) := by
    unfold hashCalls
    omega
  have hb : 1 ≤ 2^p.branchVars := Nat.one_le_pow _ _ (by omega)
  have ho : 1 ≤ (p.ordinary+1)^8 := Nat.one_le_pow _ _ (by omega)
  have hs : 1 ≤ (SupportProgram.count n (jetOrder k n p)+1)^4 :=
    Nat.one_le_pow _ _ (by omega)
  unfold assembledWork sparseWork
  calc
    _ = 1*1*enumerationWork p.labelBase p.labelRows p.heads p.headSize*1*1*1 := by ring
    _ ≤ hashCalls n p.clauses (SparseCode.distanceDenom p.clauses p.initialOccurrence)*
        2^p.branchVars*enumerationWork p.labelBase p.labelRows p.heads p.headSize*
        p.bits*(p.ordinary+1)^8*(SupportProgram.count n (jetOrder k n p)+1)^4 := by gcongr
    _ ≤ _ := Nat.le_add_left _ _

theorem supportFourth_le_assembledWork (k n : ℕ) (p : Resources)
    (hbase : 0 < p.labelBase) (hheads : 1 ≤ p.heads) (hbits : 1 ≤ p.bits) :
    (SupportProgram.count n (jetOrder k n p)+1)^4 ≤ assembledWork k n p := by
  have hc : 1 ≤ hashCalls n p.clauses
      (SparseCode.distanceDenom p.clauses p.initialOccurrence) := by
    unfold hashCalls
    omega
  have hb : 1 ≤ 2^p.branchVars := Nat.one_le_pow _ _ (by omega)
  have ho : 1 ≤ (p.ordinary+1)^8 := Nat.one_le_pow _ _ (by omega)
  have hh : 0 < p.heads := by omega
  have he : 1 ≤ enumerationWork p.labelBase p.labelRows p.heads p.headSize := by
    change 0 < enumerationWork p.labelBase p.labelRows p.heads p.headSize
    unfold enumerationWork
    positivity
  unfold assembledWork sparseWork
  calc
    _ = 1*1*1*1*1*(SupportProgram.count n (jetOrder k n p)+1)^4 := by ring
    _ ≤ hashCalls n p.clauses (SparseCode.distanceDenom p.clauses p.initialOccurrence)*
        2^p.branchVars*enumerationWork p.labelBase p.labelRows p.heads p.headSize*
        p.bits*(p.ordinary+1)^8*(SupportProgram.count n (jetOrder k n p)+1)^4 := by gcongr
    _ ≤ _ := Nat.le_add_left _ _

theorem supportCount_le_assembledWork (k n : ℕ) (p : Resources)
    (hbase : 0 < p.labelBase) (hheads : 1 ≤ p.heads) (hbits : 1 ≤ p.bits) :
    SupportProgram.count n (jetOrder k n p) ≤ assembledWork k n p := by
  have hpow : SupportProgram.count n (jetOrder k n p)+1 ≤
      (SupportProgram.count n (jetOrder k n p)+1)^4 :=
    le_self_pow₀ (by omega) (by omega)
  exact (Nat.le_succ _).trans (hpow.trans
    (supportFourth_le_assembledWork k n p hbase hheads hbits))

theorem headAssignments_le_assembledWork (k n : ℕ) (p : Resources)
    (hbase : 0 < p.labelBase) (hheads : 1 ≤ p.heads) (hbits : 1 ≤ p.bits) :
    2^p.headSize ≤ assembledWork k n p := by
  have hp : 1 ≤ p.labelBase^p.labelRows := Nat.one_le_pow _ _ hbase
  apply le_trans _ (enumeration_le_assembledWork k n p hbits)
  unfold enumerationWork
  calc
    2^p.headSize = 1*1*2^p.headSize := by ring
    _ ≤ _ := by gcongr

/-- The quadratic head-assignment factor in native bucket grouping is paid
by a square of the assembled counter, not by an ordinary polynomial in n. -/
theorem quadratic_headAssignments_le (k n : ℕ) (p : Resources)
    (hbase : 0 < p.labelBase) (hheads : 1 ≤ p.heads) (hbits : 1 ≤ p.bits) :
    (2^p.headSize+1)^2 ≤ (assembledWork k n p+1)^2 := by
  have h := headAssignments_le_assembledWork k n p hbase hheads hbits
  gcongr

theorem ordinary_succ_le {qi ql d n : ℕ} {p : Resources}
    (hp : Bounds qi ql d n p) (hbits : 1 ≤ p.bits) :
    p.ordinary+1 ≤ (n+1)^d := by
  have hpow : p.ordinary+1 ≤ (p.ordinary+1)^8 :=
    le_self_pow₀ (by omega) (by omega)
  calc
    p.ordinary+1 ≤ (p.ordinary+1)^8 := hpow
    _ ≤ p.bits*(p.ordinary+1)^8 := by
      calc
        _ = 1*(p.ordinary+1)^8 := by ring
        _ ≤ _ := by gcongr
    _ ≤ (n+1)^d := hp.ordinary

theorem ordinary_power_le {qi ql d n : ℕ} {p : Resources}
    (hp : Bounds qi ql d n p) (hbits : 1 ≤ p.bits) (e : ℕ) :
    (p.ordinary+1)^e ≤ (n+1)^(d*e) := by
  calc
    (p.ordinary+1)^e ≤ ((n+1)^d)^e :=
      Nat.pow_le_pow_left (ordinary_succ_le hp hbits) e
    _ = (n+1)^(d*e) := by rw [pow_mul]

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
