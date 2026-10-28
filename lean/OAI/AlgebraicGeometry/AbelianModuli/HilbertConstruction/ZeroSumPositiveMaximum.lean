import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SumHighWeightCount
import Mathlib.Data.Finset.Max

/-! # Zero Sum Positive Maximum -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroSumPositiveMaximum

noncomputable section

/-! A nonzero finite real weighting with total zero has a positive maximum. -/
open scoped BigOperators Classical
universe u

theorem zeroSum_nonzero_exists_positive_maximum {ι : Type u} [Fintype ι]
    (a : ι → ℝ) (ha : ∑ i, a i = 0) (hne : a ≠ 0) :
    ∃ i₀, 0 < a i₀ ∧ ∀ i, a i ≤ a i₀ := by
  obtain ⟨i, _⟩ := Function.ne_iff.mp hne
  obtain ⟨i₀, _, hmax⟩ := Finset.exists_max_image Finset.univ a ⟨i, Finset.mem_univ _⟩
  refine ⟨i₀, ?_, fun i => hmax i (Finset.mem_univ _)⟩
  by_contra hh
  have hnonpos : ∀ i ∈ (Finset.univ : Finset ι), a i ≤ 0 :=
    fun i hi => (hmax i hi).trans (le_of_not_gt hh)
  have hz := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp ha
  apply hne
  funext i
  exact hz i (Finset.mem_univ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroSumPositiveMaximum
