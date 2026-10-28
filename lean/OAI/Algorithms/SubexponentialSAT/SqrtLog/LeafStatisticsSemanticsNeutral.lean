import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceNeutral

namespace OAI.Algorithms

/-! Exact statistics for the neutral completion of the residual factor family. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open HighIncidence

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
theorem neutral_degree_eq (scope : E → Finset V) (v : V) :
    Incidence.degree (neutralScope scope) v = max 1 (Incidence.degree scope v) := by
  classical
  rw [Incidence.degree_eq_sum, Fintype.sum_sum_type]
  have hsplit :
      ((∑ e : E, if v ∈ neutralScope scope (Sum.inl e) then 1 else 0) +
        ∑ w : uncovered scope, if v ∈ neutralScope scope (Sum.inr w) then 1 else 0) =
      ((∑ e : E, if v ∈ scope e then 1 else 0) +
        ∑ w : uncovered scope, if v = w.val then 1 else 0) := by
    apply congrArg₂ (· + ·)
    · exact Finset.sum_congr rfl (fun e _ => by rfl)
    · exact Finset.sum_congr rfl (fun w _ => by
        change (if v ∈ ({w.val} : Finset V) then 1 else 0) = _
        simp only [Finset.mem_singleton])
  rw [hsplit]
  rw [← Incidence.degree_eq_sum]
  by_cases hv : Incidence.degree scope v = 0
  · let u : uncovered scope := ⟨v, by simp [uncovered, hv]⟩
    have hs : (∑ w : uncovered scope, if v = w.val then 1 else 0 : ℕ) = 1 := by
      rw [Finset.sum_eq_single u]
      · simp [u]
      · intro w _ hwu
        have hne : v ≠ w.val := by
          intro h
          apply hwu
          exact Subtype.ext h.symm
        simp [hne]
      · simp
    rw [hv, hs]
    decide
  · have hs : (∑ w : uncovered scope, if v = w.val then 1 else 0 : ℕ) = 0 := by
      apply Finset.sum_eq_zero
      intro w _
      have hne : v ≠ w.val := by
        intro h
        apply hv
        have hw : Incidence.degree scope w.val = 0 := by
          exact (Finset.mem_filter.mp w.property).2
        simpa [h] using hw
      simp [hne]
    rw [hs, Nat.add_zero, max_eq_right (Nat.one_le_iff_ne_zero.mpr hv)]

omit [DecidableEq E] in
theorem neutral_totalScope_eq (scope : E → Finset V) :
    totalScope (neutralScope scope) = ∑ v, max 1 (Incidence.degree scope v) := by
  rw [totalScope, ← Incidence.sum_degrees]
  simp only [neutral_degree_eq]

omit [DecidableEq E] in
theorem neutral_factor_card_eq (scope : E → Finset V) :
    Fintype.card (E ⊕ uncovered scope) = Fintype.card E + (uncovered scope).card := by
  simp

omit [DecidableEq E] in
theorem neutral_arity_eq (scope : E → Finset V) :
    (Finset.univ.sup fun e => (neutralScope scope e).card) =
      max (Finset.univ.sup fun e => (scope e).card)
        (if (uncovered scope).Nonempty then 1 else 0) := by
  classical
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro e _
    cases e with
    | inl e =>
      exact (Finset.le_sup (f := fun e => (scope e).card) (Finset.mem_univ e)).trans
        (le_max_left _ _)
    | inr v =>
      have hn : (uncovered scope).Nonempty := ⟨v.val, v.property⟩
      simp [neutralScope, hn]
  · apply max_le
    · apply Finset.sup_le
      intro e _
      exact Finset.le_sup (f := fun e => (neutralScope scope e).card)
        (Finset.mem_univ (Sum.inl e))
    · split_ifs with hn
      · obtain ⟨v, hv⟩ := hn
        simpa [neutralScope] using
          (Finset.le_sup (f := fun e => (neutralScope scope e).card)
            (Finset.mem_univ (Sum.inr ⟨v, hv⟩)))
      · exact Nat.zero_le _

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
