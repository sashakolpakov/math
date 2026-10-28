import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Cutoff
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.NearField

/-! The near contribution with a smooth cutoff has the expected r^α bound. -/

noncomputable section
open _root_.MeasureTheory Set Metric
namespace OAI.Analysis.PDE.Schauder

def nearSingularPart {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (v w : EuclideanSpace ℝ (Fin m)) (r : ℝ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∫ y, radialCutoff r y * compensatedNewtonianEntry f x v w y

theorem integrable_nearSingularPart {m : ℕ} (hm : 1 ≤ m) (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : Measurable f) (x v w : EuclideanSpace ℝ (Fin m)) {r H α : ℝ}
    (hr : 0 < r) (hH : 0 ≤ H) (hα : 0 < α) (hh : ∀ y, |f (x - y) - f x| ≤ H * ‖y‖ ^ α) :
    Integrable (fun y => radialCutoff r y * compensatedNewtonianEntry f x v w y) := by
  have hloc := locallyIntegrable_compensatedNewtonianEntry f x v w (by simpa using hm) hf hH hα hh volume
  simpa only [smul_eq_mul] using hloc.integrable_smul_left_of_hasCompactSupport
    (contDiff_radialCutoff r).continuous (hasCompactSupport_radialCutoff hr)

theorem nearSingularPart_bound {m : ℕ} (hm : 1 ≤ m) (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (x v w : EuclideanSpace ℝ (Fin m)) {r H α : ℝ}
    (hr : 0 < r) (hH : 0 ≤ H) (hα : 0 < α) (hh : ∀ y, |f (x - y) - f x| ≤ H * ‖y‖ ^ α) :
    |nearSingularPart f v w r x| ≤ H * newtonianSizeConstant m *
      rieszBallMass (volume : Measure (EuclideanSpace ℝ (Fin m))) α * (3 * r) ^ α * ‖v‖ * ‖w‖ := by
  have : Nontrivial (EuclideanSpace ℝ (Fin m)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have he : nearSingularPart f v w r x =
      ∫ y in ball 0 (3 * r), radialCutoff r y * compensatedNewtonianEntry f x v w y := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hn : 2 * r ≤ ‖y‖ := by
      have : 3 * r ≤ ‖y‖ := le_of_not_gt (by simpa using hy)
      linarith
    rw [radialCutoff_zero hr hn, zero_mul]
  rw [he, ← Real.norm_eq_abs]
  have hi := (integrableOn_riesz_majorant (volume : Measure (EuclideanSpace ℝ (Fin m)))
    (by simpa using hm) hα (3 * r)).const_mul
    (H * newtonianSizeConstant m * ‖v‖ * ‖w‖)
  have hz : ∀ᵐ y : EuclideanSpace ℝ (Fin m) ∂volume.restrict (ball 0 (3 * r)), y ≠ 0 := by
    apply ae_restrict_of_ae
    rw [ae_iff]; simp
  have hb : ∀ᵐ y : EuclideanSpace ℝ (Fin m) ∂volume.restrict (ball 0 (3 * r)),
      ‖radialCutoff r y * compensatedNewtonianEntry f x v w y‖ ≤
      (H * newtonianSizeConstant m * ‖v‖ * ‖w‖) * ‖y‖ ^ (α - (m : ℝ)) := by
    filter_upwards [hz] with y hy
    calc
      _ = radialCutoff r y * ‖compensatedNewtonianEntry f x v w y‖ := by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (radialCutoff_nonneg r y)]
      _ ≤ 1 * ‖compensatedNewtonianEntry f x v w y‖ :=
        mul_le_mul_of_nonneg_right (radialCutoff_le_one r y) (norm_nonneg _)
      _ ≤ _ := by simpa using compensatedNewtonianEntry_bound f x v w hH hh hy
  have h := norm_integral_le_of_norm_le hi (by simpa only [finrank_euclideanSpace_fin] using hb)
  rw [integral_const_mul, integral_riesz_majorant_ball volume α (by positivity : 0 < 3 * r)] at h
  simpa only [finrank_euclideanSpace_fin, mul_assoc, mul_comm, mul_left_comm] using h

end OAI.Analysis.PDE.Schauder
