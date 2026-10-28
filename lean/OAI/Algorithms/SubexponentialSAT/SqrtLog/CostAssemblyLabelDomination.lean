import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyDomination

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly

/-- An attained joint label inventory is paid by the assembled enumeration.
Its rank-based cardinality bound is independent of the number of raw rows. -/
theorem labelInventory_le_assembledWork (k n : ℕ) (p : Resources) (K : ℕ)
    (hK : K ≤ p.labelBase^p.labelRows) (hheads : 1 ≤ p.heads) (hbits : 1 ≤ p.bits) :
    K ≤ assembledWork k n p := by
  have he : 1 ≤ 2^p.headSize := Nat.one_le_pow _ _ (by omega)
  apply hK.trans
  apply le_trans _ (enumeration_le_assembledWork k n p hbits)
  unfold enumerationWork
  calc
    p.labelBase^p.labelRows = p.labelBase^p.labelRows*1*1 := by ring
    _ ≤ _ := by gcongr

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
