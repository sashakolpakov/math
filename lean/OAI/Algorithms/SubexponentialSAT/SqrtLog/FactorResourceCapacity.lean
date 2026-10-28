import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorReadySize
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeSupportCount
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyDomination
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesFinal

namespace OAI.Algorithms

/-! Sparse Good accumulators are paid by the support factor of assembled
work, independently of the number of original input bits. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorResource
open IdempotentApplyProgram.Bounds

theorem capacity_eq_count (n u J : ℕ) :
    capacity (Finset.univ : Finset (Fin n)) u J=u*J*SupportProgram.count n J := by
  simp [capacity,Squarefree.Sparse.supportUniverse_card,SupportProgram.count]

theorem count_mono_order (n : ℕ) {J K : ℕ} (h : J ≤ K) :
    SupportProgram.count n J ≤ SupportProgram.count n K := by
  unfold SupportProgram.count
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem capacity_le_work (k n u J : ℕ) (p : CostAssembly.Resources)
    (hJ : J ≤ CostAssembly.jetOrder k n p)
    (hbase : 0 < p.labelBase) (hheads : 1 ≤ p.heads) (hbits : 1 ≤ p.bits) :
    capacity (Finset.univ : Finset (Fin n)) u J ≤ u*J*CostAssembly.assembledWork k n p := by
  rw [capacity_eq_count]
  exact Nat.mul_le_mul_left _ ((count_mono_order n hJ).trans
    (CostAssembly.supportCount_le_assembledWork k n p hbase hheads hbits))

theorem seedBound_le_work (k n B d u J V : ℕ) (p : CostAssembly.Resources)
    (hJ : J ≤ CostAssembly.jetOrder k n p)
    (hbase : 0 < p.labelBase) (hheads : 1 ≤ p.heads) (hbits : 1 ≤ p.bits)
    (hn : n ≤ V) (hB : B ≤ V) (hd : d ≤ V) (hu : u ≤ V) (hj : J ≤ V) :
    FactorReady.seedBound n B d u J ≤ 10*(V+1)^4*(CostAssembly.assembledWork k n p+1) := by
  have hc := capacity_le_work k n u J p hJ hbase hheads hbits
  have hdiag : FactorReady.seedBound n B d u J ≤
      V*V*CostAssembly.assembledWork k n p*(2*(V+V+V)+2*(V*V)+2) := by
    unfold FactorReady.seedBound byteCapacity
    calc
      _ ≤ (u*J*CostAssembly.assembledWork k n p)*(2*(n+u+J)+2*(d*B)+2) :=
        Nat.mul_le_mul_right _ hc
      _ ≤ _ := by gcongr
  have hp : V*V*(2*(V+V+V)+2*(V*V)+2) ≤ 10*(V+1)^4 := by nlinarith
  calc
    _ ≤ V*V*CostAssembly.assembledWork k n p*(2*(V+V+V)+2*(V*V)+2) := hdiag
    _ = (V*V*(2*(V+V+V)+2*(V*V)+2))*CostAssembly.assembledWork k n p := by ring
    _ ≤ (10*(V+1)^4)*(CostAssembly.assembledWork k n p+1) := Nat.mul_le_mul hp (Nat.le_succ _)

/-- Concrete produced-query resources discharge inventory positivity. The
remaining order inequality is the source parameter's schedule identity. -/
theorem produced_seedBound_le (query : LeafQueryFrontend.Query) (k occurrence qi B d u J V : ℕ)
    (hg : LeafParametersProgram.Guard (query.input k))
    (a : SubexponentialSAT.MulticolorTypes.Word (ProducedQueryResources.problem query k hg).r
      (ProducedQueryResources.problem query k hg).Q)
    (tail : List (SubexponentialSAT.MulticolorTypes.Word (ProducedQueryResources.problem query k hg).r
      (ProducedQueryResources.problem query k hg).Q))
    (hJ : J ≤ CostAssembly.jetOrder k (ProducedQueryResources.ambient query)
      (ProducedQueryResources.resources query k occurrence qi hg a tail))
    (hn : ProducedQueryResources.ambient query ≤ V) (hB : B ≤ V) (hd : d ≤ V)
    (hu : u ≤ V) (hj : J ≤ V) :
    FactorReady.seedBound (ProducedQueryResources.ambient query) B d u J ≤
      10*(V+1)^4*(CostAssembly.assembledWork k (ProducedQueryResources.ambient query)
        (ProducedQueryResources.resources query k occurrence qi hg a tail)+1) := by
  apply seedBound_le_work k _ B d u J V _ hJ _ _ _ hn hB hd hu hj
  · change 0 < 2*ProducedQueryResources.ambient query*ProducedQueryResources.matrixHeight query k+1
    omega
  · exact ProducedQueryResources.make_heads_pos query k occurrence _ _ _ _ _ _
  · exact ProducedQueryResources.make_bits_pos query k occurrence _ _ _ _ _ _

end SubexponentialSAT.SqrtLog.LeafProgram.FactorResource

end OAI.Algorithms
