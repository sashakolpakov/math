import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence

namespace OAI.Algorithms

/-! Neutral unary factors cover exactly the otherwise unused coordinates. -/
namespace SubexponentialSAT.SqrtLog.HighIncidence

open scoped BigOperators

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def uncovered (scope : E → Finset V) : Finset V :=
  Finset.univ.filter fun v => Incidence.degree scope v = 0

def neutralScope (scope : E → Finset V) : E ⊕ uncovered scope → Finset V
  | .inl e => scope e
  | .inr v => {v.val}

omit [DecidableEq E] in
theorem neutralScope_covers (scope : E → Finset V) (v : V) :
    ∃ e, v ∈ neutralScope scope e := by
  by_cases h : Incidence.degree scope v = 0
  · exact ⟨.inr ⟨v, by simp [uncovered, h]⟩, by simp [neutralScope]⟩
  · have hn : (Incidence.incident scope v).Nonempty :=
      Finset.card_pos.mp (Nat.pos_of_ne_zero h)
    obtain ⟨e, he⟩ := hn
    exact ⟨.inl e, (Incidence.mem_incident scope v e).mp he⟩

omit [DecidableEq E] in
theorem degree_neutralScope_le (scope : E → Finset V) (v : V) :
    Incidence.degree (neutralScope scope) v ≤ Incidence.degree scope v + 1 := by
  classical
  have hc : (Finset.univ.filter fun u : uncovered scope => v = u.val).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    apply Subtype.ext
    exact (Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2
  rw [Incidence.degree_eq_sum, Fintype.sum_sum_type]
  simp only [neutralScope, Finset.mem_singleton]
  have hs : (∑ u : uncovered scope, if v = u.val then 1 else 0) ≤ 1 := by
    simpa using hc
  apply Nat.add_le_add
  · exact (Incidence.degree_eq_sum scope v).symm.le
  · exact hs

omit [DecidableEq E] in
theorem arity_neutralScope_le (scope : E → Finset V) (a : ℕ)
    (ha : ∀ e, (scope e).card ≤ a) (e : E ⊕ uncovered scope) :
    (neutralScope scope e).card ≤ max a 1 := by
  cases e with
  | inl e => exact (ha e).trans (le_max_left _ _)
  | inr v => simp [neutralScope]

omit [DecidableEq E] in
theorem neutral_factor_count (scope : E → Finset V) :
    Fintype.card (uncovered scope) ≤ Fintype.card V := by
  simpa using (Finset.card_le_univ (uncovered scope))

omit [DecidableEq E] in
theorem totalScope_neutralScope_le (scope : E → Finset V) :
    totalScope (neutralScope scope) ≤ totalScope scope + Fintype.card V := by
  rw [totalScope, Fintype.sum_sum_type]
  simp only [neutralScope, Finset.card_singleton, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one]
  exact Nat.add_le_add_left (neutral_factor_count scope) _

def neutralValues {R : Type*} [One R] (scope : E → Finset V)
    (f : E → R) : E ⊕ uncovered scope → R
  | .inl e => f e
  | .inr _ => 1

omit [DecidableEq E] in
theorem prod_neutralValues {R : Type*} [CommMonoid R] (scope : E → Finset V)
    (f : E → R) : ∏ e, neutralValues scope f e = ∏ e, f e := by
  simp [Fintype.prod_sum_type, neutralValues]

end SubexponentialSAT.SqrtLog.HighIncidence

end OAI.Algorithms
