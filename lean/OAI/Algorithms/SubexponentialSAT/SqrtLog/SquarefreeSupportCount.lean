import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeSparseBounds

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree.Sparse

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
private theorem powersetCard_pairwiseDisjoint (vars : Finset V) (J : ℕ) :
    (↑(Finset.range J) : Set ℕ).PairwiseDisjoint (fun j => vars.powersetCard j) := by
  intro i _ j _ hij
  exact vars.pairwise_disjoint_powersetCard hij

omit [DecidableEq V] in
theorem supportUniverse_eq_disjiUnion (vars : Finset V) (J : ℕ) :
    supportUniverse vars J = (Finset.range J).disjiUnion
      (fun j => vars.powersetCard j)
      (powersetCard_pairwiseDisjoint vars J) := by
  ext s
  rw [Finset.mem_disjiUnion]
  simp only [supportUniverse, Finset.mem_filter, Finset.mem_powerset,
    Finset.mem_range, Finset.mem_powersetCard]
  constructor
  · rintro ⟨hs, hc⟩
    exact ⟨s.card, hc, hs, rfl⟩
  · rintro ⟨j, hj, hs, hc⟩
    exact ⟨hs, hc.trans_lt hj⟩

omit [DecidableEq V] in
theorem supportUniverse_card (vars : Finset V) (J : ℕ) :
    (supportUniverse vars J).card = ∑ j ∈ Finset.range J, vars.card.choose j := by
  rw [supportUniverse_eq_disjiUnion, Finset.card_disjiUnion]
  simp

theorem finite_support_count (n J : ℕ) :
    (supportUniverse (Finset.univ : Finset (Fin n)) J).card =
      ∑ j ∈ Finset.range J, n.choose j := by
  simp [supportUniverse_card]

end SubexponentialSAT.SqrtLog.Squarefree.Sparse

end OAI.Algorithms
