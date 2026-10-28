import OAI.Analysis.PDE.Elliptic.Boundary.EllipticRecovery
import OAI.Analysis.PDE.Dirichlet.NormalRemainder

/-! Tangential and mixed bilinear bounds give an operator-norm bound for
the remainder after removing the unknown normal-normal coefficient. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open InnerProductSpace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem normal_remainder_operator_norm (H : E →L[ℝ] E) {ν : E}
    (hν : ‖ν‖ = 1) (hH : H.toLinearMap.IsSymmetric) {T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M)
    (ht : ∀ v w, inner ℝ ν v = 0 → inner ℝ ν w = 0 →
      |inner ℝ (H v) w| ≤ T * ‖v‖ * ‖w‖)
    (hm : ∀ v, inner ℝ ν v = 0 → |inner ℝ (H ν) v| ≤ M * ‖v‖) :
    ‖H - inner ℝ (H ν) ν • rankOne ℝ ν ν‖ ≤ 4 * T + 4 * M := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := (toDual ℝ E).toContinuousLinearMap.comp H
  let R := H - inner ℝ (H ν) ν • rankOne ℝ ν ν
  have hB (v w : E) : B v w = inner ℝ (H v) w := rfl
  have hs (v w : E) : B v w = B w v := by
    rw [hB, hB]
    exact (hH v w).trans (real_inner_comm v (H w)).symm
  have he (v w : E) : inner ℝ (R v) w =
      B v w - B ν ν * inner ℝ ν v * inner ℝ ν w := by
    simp only [R, sub_apply, smul_apply, rankOne_apply, inner_sub_left,
      real_inner_smul_left, hB]
    ring
  have hunit (v w : E) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
      |inner ℝ (R v) w| ≤ 4 * T + 4 * M := by
    rw [he]
    exact OAI.Analysis.PDE.Dirichlet.normal_remainder_abs_bound B hν hv hw hs hT hM ht hm
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  change ‖R v‖ ≤ 4 * T + 4 * M
  by_cases hz : R v = 0
  · rw [hz, norm_zero]; positivity
  have hp : 0 < ‖R v‖ := norm_pos_iff.mpr hz
  let w := (‖R v‖⁻¹ : ℝ) • R v
  have hw : ‖w‖ = 1 := by
    simp [w, norm_smul, hp.ne']
  have hi : inner ℝ (R v) w = ‖R v‖ := by
    rw [show w = (‖R v‖⁻¹ : ℝ) • R v from rfl, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    field_simp
  have hb := hunit v w hv.le hw.le
  rwa [hi, abs_of_nonneg (norm_nonneg _)] at hb

end OAI.Analysis.PDE.Elliptic
