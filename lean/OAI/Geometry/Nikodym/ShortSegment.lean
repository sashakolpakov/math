import OAI.MeasureTheory.Kakeya.Geometry

open OAI.Analysis.Fourier.Wave

noncomputable section
open Set

namespace OAI.Geometry.Nikodym

/-- A nondegenerate Euclidean segment of length at most one is contained
in a centered unit segment. This lets a chart straighten geodesics
without requiring their Euclidean lengths to be identical. -/
theorem short_segment_subset_unitSegment {n : ℕ} {a b : Space n}
    (hab : a ≠ b) (hlen : dist a b ≤ 1) :
    ∃ v c : Space n, ‖v‖ = 1 ∧ segment ℝ a b ⊆ OAI.MeasureTheory.Kakeya.unitSegment v c := by
  have hnorm : 0 < ‖b-a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  have hnorm1 : ‖b-a‖ ≤ 1 := by simpa only [dist_eq_norm,norm_sub_rev] using hlen
  refine ⟨‖b-a‖⁻¹ • (b-a),(1/2 : ℝ) • (a+b),?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hnorm,inv_mul_cancel₀ hnorm.ne']
  · rw [segment_eq_image']
    rintro _ ⟨θ,hθ,rfl⟩
    refine ⟨(θ-1/2)*‖b-a‖,⟨?_,?_⟩,?_⟩
    · nlinarith [mul_nonneg hθ.1 hnorm.le]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hθ.2) hnorm.le]
    · rw [smul_smul]
      have hc : (θ-1/2)*‖b-a‖*‖b-a‖⁻¹ = θ-1/2 := by field_simp
      rw [hc]
      module

end OAI.Geometry.Nikodym
