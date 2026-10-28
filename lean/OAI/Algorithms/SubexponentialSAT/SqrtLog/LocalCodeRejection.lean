import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCodeSearch

namespace OAI.Algorithms

/-! The all-word rejection scan is independent of the enumeration order. -/

namespace SubexponentialSAT.SqrtLog.LocalCode

open SparseCode

theorem complete_list_any_rejection_eq_false_iff
    {D t d : ℕ} (values : List (Fin D → F3))
    (hcomplete : ∀ w, w ∈ values) (Q : CheckMatrix (Fin t) (Fin D)) :
    (values.any (fun w => decide (IsCodeword Q w ∧ w ≠ 0 ∧ weight w < d)) = false) ↔
      HasDistance Q d := by
  rw [List.any_eq_false]
  simp only [decide_eq_true_eq]
  constructor
  · intro h w hw hw0
    by_contra hn
    exact h w (hcomplete w) ⟨hw,hw0,Nat.lt_of_not_ge hn⟩
  · intro h w _
    rintro ⟨hw, hw0, hlt⟩
    exact (not_lt_of_ge (h w hw hw0)) hlt

theorem localWords_any_rejection_eq_false_iff (D t d : ℕ)
    (Q : CheckMatrix (Fin t) (Fin D)) :
    ((localWords D).any (fun w => decide (IsCodeword Q w ∧ w ≠ 0 ∧ weight w < d))
      = false) ↔ HasDistance Q d :=
  complete_list_any_rejection_eq_false_iff (localWords D) (localWords_complete D) Q

theorem localWords_any_rejection_eq_not_test (D t d : ℕ)
    (Q : CheckMatrix (Fin t) (Fin D)) :
    (localWords D).any (fun w => decide (IsCodeword Q w ∧ w ≠ 0 ∧ weight w < d)) =
      !localCodeTest D t d Q := by
  have ha := localWords_any_rejection_eq_false_iff D t d Q
  have ht := localCodeTest_spec D t d Q
  cases hbad : (localWords D).any
      (fun w => decide (IsCodeword Q w ∧ w ≠ 0 ∧ weight w < d)) with
  | false =>
    have hgood := ht.mpr (ha.mp hbad)
    simp only [hgood,Bool.not_true]
  | true =>
    cases hgood : localCodeTest D t d Q with
    | false => rfl
    | true =>
      have hf := ha.mpr (ht.mp hgood)
      rw [hbad] at hf
      cases hf

end SubexponentialSAT.SqrtLog.LocalCode

end OAI.Algorithms
