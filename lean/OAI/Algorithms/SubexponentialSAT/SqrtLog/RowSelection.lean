import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionEnumeration
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRowSelection

namespace OAI.Algorithms

/-! The executable maximal-minor search returns exactly the rational rank many
independent original integer rows, with unchanged entry bounds. -/

namespace SubexponentialSAT.SqrtLog.RowSelection

variable {a b : ℕ}

theorem select_independent (P : Fin a → Fin b → ℤ) (cap : ℕ) :
    LinearIndependent ℚ (fun i => qmatrix P ((select P cap).rows i)) :=
  independent_of_minor P _ _ (select_good P cap)

theorem select_injective (P : Fin a → Fin b → ℤ) (cap : ℕ) :
    Function.Injective (select P cap).rows :=
  rows_injective_of_minor P _ _ (select_good P cap)

theorem select_span (P : Fin a → Fin b → ℤ) (cap : ℕ)
    (hrank : Module.finrank ℚ (Submodule.span ℚ (Set.range (qmatrix P))) ≤ cap) :
    Submodule.span ℚ (Set.range (fun i => qmatrix P ((select P cap).rows i))) =
      Submodule.span ℚ (Set.range (qmatrix P)) := by
  have hc : (select P cap).size ≤ cap :=
    (select_le P cap).trans (min_le_left _ _)
  by_cases heq : (select P cap).size = cap
  · apply span_eq_of_rank_le_size P _ _ (select_good P cap)
    simpa only [heq] using hrank
  · apply span_eq_of_borders_zero P _ _ (select_good P cap)
    intro i j
    by_contra hn
    have hi := rows_injective_of_minor P _ _ hn
    have hj := cols_injective_of_minor P _ _ hn
    have ha : (select P cap).size + 1 ≤ a := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hi
    have hb : (select P cap).size + 1 ≤ b := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hj
    have hs : (select P cap).size + 1 ≤ limit a b cap :=
      le_min (by omega) (le_min ha hb)
    have hm := select_maximal P cap _ _ hs hn
    omega

/-- The output uses the actual rank, without rounding up the search cap. -/
theorem select_rank (P : Fin a → Fin b → ℤ) (cap : ℕ)
    (hrank : Module.finrank ℚ (Submodule.span ℚ (Set.range (qmatrix P))) ≤ cap) :
    (select P cap).size = Module.finrank ℚ
      (Submodule.span ℚ (Set.range (qmatrix P))) := by
  rw [← select_span P cap hrank, finrank_span_eq_card (select_independent P cap)]
  exact (Fintype.card_fin _).symm

/-- The exact integer-kernel interface consumed by the layout. -/
theorem select_rationalRowSpan (P : Fin a → Fin b → ℤ) (cap : ℕ)
    (hrank : Module.finrank ℚ (Submodule.span ℚ (Set.range (qmatrix P))) ≤ cap) :
    LayoutExactBuckets.RationalRowSpan P (fun i => P ((select P cap).rows i)) := by
  apply LayoutRowSelection.rationalRowSpan_of_span_eq
  change Submodule.span ℚ
      (Set.range fun i => qmatrix P ((select P cap).rows i)) =
    Submodule.span ℚ (Set.range (qmatrix P))
  exact select_span P cap hrank

/-- Output entries are original integer entries, not rational combinations. -/
theorem select_bound (P : Fin a → Fin b → ℤ) (cap : ℕ) (W : ℤ)
    (hP : ∀ i j, |P i j| ≤ W) :
    ∀ i j, |P ((select P cap).rows i) j| ≤ W :=
  fun _i _j => hP _ _

end SubexponentialSAT.SqrtLog.RowSelection

end OAI.Algorithms
