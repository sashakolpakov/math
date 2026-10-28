import OAI.Analysis.PDE.Schauder.Calculus.Boundary.SchauderZero

/-! On a fixed compact support, the halfspace Hölder seminorm controls Hessian size. -/

noncomputable section
open Set Metric
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem hessian_zero_outside_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℝ) (x : E) (hx : x ∉ tsupport u) : fderiv ℝ (fderiv ℝ u) x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hh
  exact hx ((tsupport_fderiv_subset ℝ) ((tsupport_fderiv_subset ℝ) hh))

local instance supportFirstGroup (m : ℕ) : NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance supportFirstSpace (m : ℕ) : NormedSpace ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance supportSecondGroup (m : ℕ) :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance supportSecondSpace (m : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance

theorem halfspace_hessian_bound_of_support {m : ℕ} (k : Fin m)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) {R α H : ℝ} (hR : 0 ≤ R)
    (hα : 0 ≤ α) (hH : 0 ≤ H) (hs : tsupport u ⊆ closedBall 0 R)
    (hh : ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x - y‖ ^ α)
    (x : EuclideanSpace ℝ (Fin m)) (hx : 0 ≤ x k) :
    ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ H * (2 * R + 1) ^ α := by
  have hzero (y : EuclideanSpace ℝ (Fin m)) (hy : R < ‖y‖) : fderiv ℝ (fderiv ℝ u) y = 0 := by
    apply hessian_zero_outside_support u y
    intro ht
    have hz : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hs ht
    linarith
  by_cases hnx : ‖x‖ ≤ R
  · let z : EuclideanSpace ℝ (Fin m) := (R + 1) • EuclideanSpace.single k 1
    have hnz : ‖z‖ = R + 1 := by simp [z, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ R + 1)]
    have hzk : 0 ≤ z k := by simp [z]; linarith
    have hHz : fderiv ℝ (fderiv ℝ u) z = 0 := hzero z (by rw [hnz]; linarith)
    have hdist : ‖x - z‖ ≤ 2 * R + 1 := (norm_sub_le x z).trans (by rw [hnz]; linarith)
    have hb := hh x hx z hzk
    rw [hHz, sub_zero] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hdist hα) hH)
  · rw [hzero x (lt_of_not_ge hnx)]
    rw [norm_zero]
    exact mul_nonneg hH (Real.rpow_nonneg (by linarith : 0 ≤ 2 * R + 1) α)

end OAI.Analysis.PDE.Schauder
