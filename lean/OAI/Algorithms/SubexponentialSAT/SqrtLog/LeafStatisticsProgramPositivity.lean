import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsSemanticsArity

namespace OAI.Algorithms

/-! Elementary nondegeneracy conditions for the measured native statistics. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
open scoped BigOperators
open LeafStatisticsSemantics

def measured (scopes : List (List ℕ)) (mask : List Bool) : Totals :=
  variableTotals scopes 0 mask LeafStatisticsSemantics.zero

theorem free_le_ambient (scopes : List (List ℕ)) (mask : List Bool) :
    (measured scopes mask).free ≤ mask.length := by
  rw [measured, free_exact]
  simp

theorem free_le_incidences (scopes : List (List ℕ)) (mask : List Bool) :
    (measured scopes mask).free ≤ (measured scopes mask).incidences := by
  simp only [measured]
  rw [free_exact, incidences_exact, HighIncidence.totalScope, ← Incidence.sum_degrees]
  calc
    Fintype.card (Free mask) = ∑ _v : Free mask, (1 : ℕ) := by simp
    _ ≤ ∑ v : Free mask, Incidence.degree (completedScope scopes mask) v := by
      apply Finset.sum_le_sum
      intro v _
      rw [completed_degree]
      exact le_max_left 1 _

theorem occurrence_pos_of_free_pos (scopes : List (List ℕ)) (mask : List Bool)
    (hfree : 0 < (measured scopes mask).free) :
    0 < (measured scopes mask).occurrence := by
  have hc : 0 < Fintype.card (Free mask) := by simpa [measured, free_exact] using hfree
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hc
  rw [measured, occurrence_exact]
  have hd : 1 ≤ Incidence.degree (completedScope scopes mask) v := by
    rw [completed_degree]
    exact le_max_left 1 _
  exact lt_of_lt_of_le (by decide : 0 < 1)
    (hd.trans (Finset.le_sup (f := Incidence.degree (completedScope scopes mask)) (Finset.mem_univ v)))

theorem arity_pos_of_free_pos (scopes : List (List ℕ)) (mask : List Bool)
    (hn : ∀ row ∈ scopes, row.Nodup)
    (hfree : 0 < (measured scopes mask).free) :
    0 < max (Arity.arity mask scopes 0)
      (if (measured scopes mask).uncovered = 0 then 0 else 1) := by
  have hc : 0 < Fintype.card (Free mask) := by simpa [measured, free_exact] using hfree
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hc
  obtain ⟨e,he⟩ := HighIncidence.neutralScope_covers (residualScope scopes mask) v
  have hcard : 0 < (completedScope scopes mask e).card :=
    Finset.card_pos.mpr ⟨v,he⟩
  rw [measured, completed_arity_exact mask scopes hn]
  exact lt_of_lt_of_le hcard
    (Finset.le_sup (f := fun e => (completedScope scopes mask e).card) (Finset.mem_univ e))

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

#print axioms SubexponentialSAT.SqrtLog.LeafStatisticsProgram.arity_pos_of_free_pos

end OAI.Algorithms
