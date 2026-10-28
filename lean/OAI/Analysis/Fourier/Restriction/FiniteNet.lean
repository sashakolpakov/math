import OAI.Analysis.Fourier.Restriction.Coloring
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset

noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- A finite set admits a separated net with centers in the set, without
ambient compactness or a pre-existing covering-number estimate. -/
theorem finite_separated_cover {X : Type*} [PseudoMetricSpace X]
    (S : Finset X) {r : ℝ} (hr : 0 < r) :
    ∃ T : Finset X, T ⊆ S ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → r ≤ dist x y) ∧
      ∀ x ∈ S, ∃ y ∈ T, dist x y < r := by
  classical
  let separated (T : Finset X) : Prop := ∀ x ∈ T, ∀ y ∈ T, x ≠ y → r ≤ dist x y
  let candidates := S.powerset.filter separated
  have hne : candidates.Nonempty := ⟨∅, by simp [candidates, separated]⟩
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image candidates Finset.card hne
  have hsub : T ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
  have hsep : separated T := (Finset.mem_filter.mp hT).2
  refine ⟨T, hsub, hsep, ?_⟩
  intro x hx
  by_contra! hfar
  have hxT : x ∉ T := by
    intro h
    have H := hfar x h
    exact hr.not_ge (by simpa using H)
  have hins : separated (insert x T) := by
    intro y hy z hz hyz
    by_cases hyx : y = x
    · subst y
      exact hfar z ((Finset.mem_insert.mp hz).resolve_left hyz.symm)
    · by_cases hzx : z = x
      · subst z
        simpa [dist_comm] using hfar y (Finset.mem_of_mem_insert_of_ne hy hyx)
      · exact hsep y (Finset.mem_of_mem_insert_of_ne hy hyx)
          z (Finset.mem_of_mem_insert_of_ne hz hzx) hyz
  have hinc : insert x T ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset hx hsub), hins⟩
  have H := hmax (insert x T) hinc
  rw [Finset.card_insert_of_notMem hxT] at H
  omega

end OAI.Analysis.Fourier.Restriction
