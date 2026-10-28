import OAI.Analysis.PDE.Elliptic.Superlevel

open Set _root_.MeasureTheory
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {X : Type*} [MeasurableSpace X]

theorem sublevel_add_superlevel (μ : Measure X) {S : Set X} (hS : MeasurableSet S)
    (hfinite : μ S ≠ ⊤) {u : X → ℝ} (hu : Measurable u) (t : ℝ) :
    μ.real (S ∩ {x | u x ≤ t}) + μ.real (S ∩ {x | t < u x}) = μ.real S := by
  have hd : Disjoint (S ∩ {x | u x ≤ t}) (S ∩ {x | t < u x}) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact not_lt_of_ge (show u x ≤ t from hx.2) (show t < u x from hy.2)
  have hU : (S ∩ {x | u x ≤ t}) ∪ (S ∩ {x | t < u x}) = S := by
    ext x
    constructor
    · rintro (hx | hx) <;> exact hx.1
    · intro hx
      by_cases ht : t < u x
      · exact Or.inr ⟨hx, ht⟩
      · exact Or.inl ⟨hx, le_of_not_gt ht⟩
  have hlow : μ (S ∩ {x | u x ≤ t}) ≠ ⊤ :=
    ne_of_lt ((measure_mono inter_subset_left).trans_lt (lt_top_iff_ne_top.mpr hfinite))
  have hhigh : μ (S ∩ {x | t < u x}) ≠ ⊤ :=
    ne_of_lt ((measure_mono inter_subset_left).trans_lt (lt_top_iff_ne_top.mpr hfinite))
  have h := measureReal_union hd (hS.inter (measurableSet_lt measurable_const hu)) hlow hhigh
  rw [hU] at h
  exact h.symm

theorem sublevel_lt_of_superlevel_gt (μ : Measure X) {S T : Set X}
    (hS : MeasurableSet S) (hfinite : μ S ≠ ⊤) (hTS : T ⊆ S)
    {u : X → ℝ} (hu : Measurable u) {t eta : ℝ}
    (hhigh : (1 - eta) * μ.real S < μ.real (S ∩ {x | t < u x})) :
    μ.real (T ∩ {x | u x ≤ t}) < eta * μ.real S := by
  have hadd := sublevel_add_superlevel μ hS hfinite hu t
  have hlow : μ (S ∩ {x | u x ≤ t}) ≠ ⊤ :=
    ne_of_lt ((measure_mono inter_subset_left).trans_lt (lt_top_iff_ne_top.mpr hfinite))
  have hmono := measureReal_mono (inter_subset_inter_left _ hTS) hlow
  linarith

end OAI.Analysis.PDE.Elliptic
