import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyRankBudget
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyLabelDomination

namespace OAI.Algorithms

/-! Numerical endpoint for the actual attained bucket product. The semantic
identification of each produced matrix and table is supplied separately. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open scoped BigOperators

theorem jointInventory_le_rankSum {G : Type*} [Fintype G]
    (base : ℕ) (count rank : G → ℕ) (h : ∀ g, count g ≤ base^rank g) :
    (∏ g, count g) ≤ base^(∑ g, rank g) := by
  calc
    _ ≤ ∏ g, base^rank g := Finset.prod_le_prod (fun g _ => h g)
    _ = _ := Finset.prod_pow_eq_pow_sum Finset.univ rank base

theorem listInventory_le_rankSum {G : Type*} (heads : List G)
    (base : ℕ) (count rank : G → ℕ) (h : ∀ g∈heads, count g ≤ base^rank g) :
    (heads.map count).prod ≤ base^(heads.map rank).sum := by
  induction heads with
  | nil => simp
  | cons g gs ih =>
    have hg := h g (by simp)
    have ht := ih (fun i hi => h i (by simp [hi]))
    simp only [List.map_cons,List.prod_cons,List.sum_cons,pow_add]
    exact Nat.mul_le_mul hg ht

theorem inventory_le_maxTotalRank {X G : Type*} [Fintype G]
    (base K : ℕ) (nodes : Finset X) (rank : X → G → ℕ) {x : X}
    (hbase : 1 ≤ base) (hx : x∈nodes) (hK : K ≤ base^(∑ g,rank x g)) :
    K ≤ base^maxTotalRank nodes rank :=
  hK.trans (Nat.pow_le_pow_right hbase (totalRank_le_max nodes rank hx))

theorem jointInventory_le_maxTotalRank {X G : Type*} [Fintype G]
    (base : ℕ) (count : G → ℕ) (nodes : Finset X) (rank : X → G → ℕ) {x : X}
    (hbase : 1 ≤ base) (hx : x∈nodes) (h : ∀ g,count g ≤ base^rank x g) :
    (∏ g,count g) ≤ base^maxTotalRank nodes rank :=
  inventory_le_maxTotalRank base _ nodes rank hbase hx
    (jointInventory_le_rankSum base count (rank x) h)

theorem inventory_le_assembledWork_of_node {X G : Type*} [Fintype G]
    (k n : ℕ) (p : Resources) (K : ℕ) (nodes : Finset X) (rank : X → G → ℕ) {x : X}
    (hbase : 1 ≤ p.labelBase) (hx : x∈nodes)
    (hK : K ≤ p.labelBase^(∑ g,rank x g))
    (hrank : maxTotalRank nodes rank ≤ p.labelRows)
    (hheads : 1 ≤ p.heads) (hbits : 1 ≤ p.bits) : K ≤ assembledWork k n p := by
  apply labelInventory_le_assembledWork k n p K _ hheads hbits
  exact (inventory_le_maxTotalRank p.labelBase K nodes rank hbase hx hK).trans
    (Nat.pow_le_pow_right hbase hrank)

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
