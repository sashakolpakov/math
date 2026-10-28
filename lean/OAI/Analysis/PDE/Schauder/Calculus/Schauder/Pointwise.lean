import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Freeze
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Unscale

/-! A normalized elliptic equation with Hölder coefficients improves every C² solution locally. -/

noncomputable section
open Set Metric
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem normalized_pointwise_schauder {m : ℕ} (hm : 3 ≤ m) {α ρ : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (F : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u)
    (x₀ : EuclideanSpace ℝ (Fin m)) (hA₀ : OAI.Analysis.Normed.Function.Holder.HolderMap.value A x₀ = 1)
    (hPD : ∀ x ∈ ball x₀ ρ, (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x).PosDef)
    (heq : ∀ x ∈ ball x₀ ρ, nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) u x = OAI.Analysis.Normed.Function.Holder.HolderMap.value F x) :
    ∃ s > 0, ∃ C > 0, ∀ x ∈ ball x₀ s, ∀ y ∈ ball x₀ s,
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ C * ‖x - y‖ ^ α := by
  let K := 2 * ((m : ℝ) * m) * ‖poissonHolderOperator hm hα hα1 2‖
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  obtain ⟨ε, hε, hεK⟩ := exists_pos_mul_lt (show (0 : ℝ) < 1 by norm_num) K
  obtain ⟨r, hr, hrρ, B, hBval, hBnorm, hBsupport⟩ :=
    exists_small_localized_difference hα hα1 hε (show 0 < ρ / 4 by positivity) A x₀
  have hsmall : 2 * ((m : ℝ) * m * ‖B‖) * ‖poissonHolderOperator hm hα hα1 2‖ < 1 := by
    calc
      _ = K * ‖B‖ := by dsimp only [K]; ring
      _ ≤ K * ε := mul_le_mul_of_nonneg_left hBnorm.le hK
      _ < 1 := hεK
  let φ := fun y : EuclideanSpace ℝ (Fin m) => x₀ + r • y
  have hnear (y : EuclideanSpace ℝ (Fin m)) (hy : ‖y‖ ≤ 2) : φ y ∈ ball x₀ ρ := by
    change ‖x₀ + r • y - x₀‖ < ρ
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    calc
      _ ≤ r * 2 := mul_le_mul_of_nonneg_left hy hr.le
      _ < ρ := by linarith
  have hBPD (y : EuclideanSpace ℝ (Fin m)) : (1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y).PosDef := by
    rw [hBval]
    simp only [dilatedDifference, hA₀]
    apply posDef_identity_cutoff _ (radialCutoff_nonneg 1 y) (radialCutoff_le_one 1 y)
    intro hy
    apply hPD _ (hnear y ?_)
    by_contra hh
    exact hy (radialCutoff_zero zero_lt_one (by linarith [lt_of_not_ge hh]))
  let χ : EuclideanSpace ℝ (Fin m) → ℝ := radialCutoff (1 / 4)
  have hχ : ContDiff ℝ 3 χ := (contDiff_radialCutoff _).of_le (by simp)
  have hχc : HasCompactSupport χ := hasCompactSupport_radialCutoff (by norm_num)
  have hχnorm (y : EuclideanSpace ℝ (Fin m)) (hy : y ∈ Function.support χ) : ‖y‖ ≤ 1 / 2 := by
    change χ y ≠ 0 at hy
    by_contra hh
    exact hy (radialCutoff_zero (show (0 : ℝ) < 1 / 4 by norm_num) (by linarith [lt_of_not_ge hh]))
  have hχR : tsupport χ ⊆ closedBall 0 2 := by
    apply closure_minimal _ isClosed_closedBall
    intro y hy
    simp only [mem_closedBall, dist_zero_right]
    linarith [hχnorm y hy]
  let v := fun y => u (φ y)
  have hv : ContDiff ℝ 2 v := hu.comp (contDiff_const.add (contDiff_id.const_smul r))
  let G : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α := r ^ 2 • holderAffinePullback hα.le F x₀ r
  have hveq (y) (hy : y ∈ Function.support χ) :
      nondivergenceOperator (fun z => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B z) v y = OAI.Analysis.Normed.Function.Holder.HolderMap.value G y := by
    have hBid : 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y = OAI.Analysis.Normed.Function.Holder.HolderMap.value A (φ y) := by
      rw [hBval, radialCutoff_one zero_lt_one (by linarith [hχnorm y hy]), one_smul]
      simp only [dilatedDifference, hA₀, sub_sub_cancel]
      rfl
    calc
      _ = nondivergenceOperator (fun z => OAI.Analysis.Normed.Function.Holder.HolderMap.value A (φ z)) v y := by
        exact congrArg (fun M : Matrix (Fin m) (Fin m) ℝ => ∑ i, ∑ j,
          M i j * fderiv ℝ (fderiv ℝ v) y (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) hBid
      _ = r ^ 2 * nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) u (φ y) := nondivergence_dilate _ u hu x₀ y r
      _ = r ^ 2 * OAI.Analysis.Normed.Function.Holder.HolderMap.value F (φ y) := by rw [heq _ (hnear y (by linarith [hχnorm y hy]))]
      _ = OAI.Analysis.Normed.Function.Holder.HolderMap.value G y := rfl
  obtain ⟨C, hC, hh⟩ := local_small_coefficient_holder hm hα hα1 B hBsupport hsmall hBPD
    G χ v hχ hχc hχR hv hveq (ball 0 (1 / 4)) isOpen_ball (by
      intro y hy
      exact radialCutoff_one (by norm_num)
        (le_of_lt (by simpa only [mem_ball, dist_zero_right] using hy)))
  obtain ⟨D, hD, hhD⟩ := hessian_holder_of_dilate u hu x₀ hr (show (0 : ℝ) < 1 / 4 by norm_num) hC hh
  exact ⟨r * (1 / 4), by positivity, D, hD, hhD⟩

end OAI.Analysis.PDE.Schauder
