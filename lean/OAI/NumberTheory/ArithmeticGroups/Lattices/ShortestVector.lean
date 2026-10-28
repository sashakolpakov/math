import Mathlib

/-! # Shortest Vector -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ShortestVector.Construction

noncomputable section

/-! Shortest vectors and integral points on their real lines. -/

open scoped Classical
open Set _root_.Metric

theorem exists_shortest_lattice_vector
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (y : E) (hy : y ∈ Λ) (hy0 : y ≠ 0) :
    ∃ v ∈ Λ, v ≠ 0 ∧ ∀ x ∈ Λ, x ≠ 0 → ‖v‖ ≤ ‖x‖ := by
  have hclosed : IsClosed (Λ : Set E) :=
    show IsClosed (Λ.toAddSubgroup : Set E) from AddSubgroup.isClosed_of_discreteTopology
  have hdisc : IsDiscrete (Λ : Set E) := isDiscrete_iff_discreteTopology.mpr inferInstance
  let S : Set E := ((Λ : Set E) ∩ closedBall 0 ‖y‖) \ {0}
  have hfinite : S.Finite :=
    ((isCompact_closedBall 0 ‖y‖).inter_left hclosed).finite
      (hdisc.mono inter_subset_left) |>.sdiff
  have hyS : y ∈ S := ⟨⟨hy, by simp⟩, hy0⟩
  obtain ⟨v, hv, hmin⟩ := Set.exists_min_image S (fun x : E => ‖x‖) hfinite ⟨y, hyS⟩
  refine ⟨v, hv.1.1, hv.2, fun x hx hx0 => ?_⟩
  by_cases hxy : ‖x‖ ≤ ‖y‖
  · exact hmin x ⟨⟨hx, by simpa using hxy⟩, hx0⟩
  · exact (hmin y hyS).trans (le_of_not_ge hxy)

theorem shortest_vector_scalar_is_integer
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Λ : Submodule ℤ E) {v : E} (hv : v ∈ Λ) (hv0 : v ≠ 0)
    (hmin : ∀ x ∈ Λ, x ≠ 0 → ‖v‖ ≤ ‖x‖)
    (t : ℝ) (ht : t • v ∈ Λ) : ∃ m : ℤ, t = m := by
  let m := round t
  have hzmem : (t - (m : ℝ)) • v ∈ Λ := by
    rw [sub_smul]
    exact Λ.sub_mem ht (by simpa only [Int.cast_smul_eq_zsmul] using Λ.smul_mem m hv)
  have hnorm : ‖(t - (m : ℝ)) • v‖ < ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have hround : |t - (m : ℝ)| ≤ 1 / 2 := abs_sub_round t
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    nlinarith
  have hz : (t - (m : ℝ)) • v = 0 := by
    by_contra hne
    exact (not_lt_of_ge (hmin _ hzmem hne)) hnorm
  have he : t - (m : ℝ) = 0 := (smul_eq_zero.mp hz).resolve_right hv0
  exact ⟨m, sub_eq_zero.mp he⟩

theorem shortest_vector_line_intersection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Λ : Submodule ℤ E) {v : E} (hv : v ∈ Λ) (hv0 : v ≠ 0)
    (hmin : ∀ x ∈ Λ, x ≠ 0 → ‖v‖ ≤ ‖x‖) :
    (Submodule.span ℝ ({v} : Set E)).restrictScalars ℤ ⊓ Λ = Submodule.span ℤ {v} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx.1
    obtain ⟨m, rfl⟩ := shortest_vector_scalar_is_integer Λ hv hv0 hmin t hx.2
    exact Submodule.mem_span_singleton.mpr ⟨m, by simp only [Int.cast_smul_eq_zsmul]⟩
  · apply Submodule.span_le.mpr
    intro x hx
    have he : x = v := Set.mem_singleton_iff.mp hx
    rw [he]
    exact ⟨Submodule.mem_span_singleton_self v, hv⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ShortestVector.Construction
