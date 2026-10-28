import OAI.Analysis.PDE.Schauder.Calculus.Interior.Interpolation
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.UniformCutoff

/-! Actual global Hölder lower jets with arbitrarily small top-order cost. -/

noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem fullspace_lower_jet_holder {m : ℕ} (k : Fin m) {α ε : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hε : 0 < ε) :
    ∃ B > 0, ∀ (u : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
      ∀ H M, 0 ≤ H → 0 ≤ M → (∀ x, |u x| ≤ M) →
      (∀ x y, ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ H*‖x-y‖^α) →
      ∃ (U : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
        (V : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α),
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value U x = u x) ∧ (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ u x) ∧
        ‖U‖ ≤ ε*H+B*M ∧ ‖V‖ ≤ ε*H+B*M := by
  obtain ⟨B, hB, hb⟩ := fullspace_lower_jet_interpolation k hα hα1 hε
  refine ⟨B+1, by positivity, ?_⟩
  intro u hu huc H M hH hM hbound hh
  obtain ⟨_, hg, hhu, hhv⟩ := hb u hu huc H M hH hM hbound hh
  let U := compactC1Holder u (hu.of_le (by norm_num)) huc hα.le hα1
  let V := compactC1Holder (fderiv ℝ u) (hu.fderiv_right (by norm_num)) (huc.fderiv ℝ) hα.le hα1
  refine ⟨U, V, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · apply OAI.Analysis.Normed.Function.Holder.HolderMap.norm_le_of_bounds hα.le (by positivity)
    · intro x
      change ‖u x‖ ≤ _
      rw [Real.norm_eq_abs]
      exact (hbound x).trans (by nlinarith)
    · intro x y
      change ‖u x-u y‖ ≤ _
      rw [Real.norm_eq_abs, dist_eq_norm]
      exact (hhu x y).trans (mul_le_mul_of_nonneg_right (by nlinarith) (Real.rpow_nonneg (norm_nonneg _) _))
  · apply OAI.Analysis.Normed.Function.Holder.HolderMap.norm_le_of_bounds hα.le (by positivity)
    · intro x
      change ‖fderiv ℝ u x‖ ≤ _
      exact (hg x).trans (by nlinarith)
    · intro x y
      change ‖fderiv ℝ u x-fderiv ℝ u y‖ ≤ _
      rw [dist_eq_norm]
      exact (hhv x y).trans (mul_le_mul_of_nonneg_right (by nlinarith) (Real.rpow_nonneg (norm_nonneg _) _))

end OAI.Analysis.PDE.Schauder
