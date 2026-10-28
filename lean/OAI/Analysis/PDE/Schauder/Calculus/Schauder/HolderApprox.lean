import OAI.Analysis.PDE.Schauder.Calculus.Schauder.MollificationDerivatives

/-! Quantitative convergence of positive mollification in every strictly lower Hölder exponent. -/

noncomputable section
open _root_.MeasureTheory Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem holder_lower_exponent_of_uniform_bound {E : Type*} [NormedAddCommGroup E]
    (g : E → ℝ) {α β ρ H U : ℝ} (hβ : 0 < β) (hβα : β ≤ α) (hρ : 0 < ρ)
    (hH : 0 ≤ H) (hU : 0 ≤ U) (hu : ∀ x, |g x| ≤ U)
    (hh : ∀ x y, |g x - g y| ≤ H * ‖x - y‖ ^ α) :
    ∀ x y, |g x - g y| ≤ (H * ρ ^ (α - β) + 2 * U / ρ ^ β) * ‖x - y‖ ^ β := by
  intro x y
  by_cases hxy : x = y
  · subst y
    simp [Real.zero_rpow hβ.ne']
  have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hpow : ‖x - y‖ ^ α = ‖x - y‖ ^ (α - β) * ‖x - y‖ ^ β := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  by_cases hsmall : ‖x - y‖ ≤ ρ
  · calc
      _ ≤ H * ‖x - y‖ ^ α := hh x y
      _ = H * (‖x - y‖ ^ (α - β) * ‖x - y‖ ^ β) := by rw [hpow]
      _ ≤ H * (ρ ^ (α - β) * ‖x - y‖ ^ β) := by
        gcongr
      _ ≤ _ := by
        have hb : 0 ≤ 2 * U / ρ ^ β := by positivity
        nlinarith [mul_nonneg hb (Real.rpow_nonneg hd.le β)]
  · have hlarge : ρ ^ β ≤ ‖x - y‖ ^ β :=
      Real.rpow_le_rpow hρ.le (le_of_not_ge hsmall) hβ.le
    have hb : |g x - g y| ≤ 2 * U := (abs_sub _ _).trans (by linarith [hu x, hu y])
    have hrpow : 0 < ρ ^ β := Real.rpow_pos_of_pos hρ β
    have hquot : 2 * U ≤ (2 * U / ρ ^ β) * ‖x - y‖ ^ β := by
      calc
        2 * U = (2 * U / ρ ^ β) * ρ ^ β := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hlarge (by positivity)
    exact hb.trans (hquot.trans (by
      have : 0 ≤ (H * ρ ^ (α - β)) * ‖x - y‖ ^ β := by positivity
      nlinarith))

theorem smoothData_lower_holder_error {m : ℕ}
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f)
    {α β H : ℝ} (hβ : 0 < β) (hβα : β ≤ α) (hH : 0 ≤ H)
    (hh : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) :
    ∀ x y, |(smoothData φ f x - f x) - (smoothData φ f y - f y)| ≤
      (4 * H * φ.rOut ^ (α - β)) * ‖x - y‖ ^ β := by
  have ha : 0 ≤ α := hβ.le.trans hβα
  have hρ : 0 < φ.rOut := φ.rIn_pos.trans φ.rIn_lt_rOut
  have herror := holder_lower_exponent_of_uniform_bound (fun x => smoothData φ f x - f x)
    hβ hβα hρ (by positivity : 0 ≤ 2 * H) (by positivity : 0 ≤ H * φ.rOut ^ α)
    (smoothData_error φ f hf hH ha hh) (fun x y => ?_)
  · intro x y
    have hp : φ.rOut ^ α = φ.rOut ^ (α - β) * φ.rOut ^ β := by
      rw [← Real.rpow_add hρ]
      congr 1
      ring
    have he : 2 * H * φ.rOut ^ (α - β) + 2 * (H * φ.rOut ^ α) / φ.rOut ^ β =
        4 * H * φ.rOut ^ (α - β) := by
      rw [hp]
      field_simp
      ; ring
    simpa only [he] using herror x y
  · have hg := smoothData_holder φ f hf hh x y
    have hid : (smoothData φ f x - f x) - (smoothData φ f y - f y) =
        (smoothData φ f x - smoothData φ f y) - (f x - f y) := by ring
    rw [hid]
    exact (abs_sub _ _).trans (by linarith [hh x y])

theorem smoothData_lower_holder_rate_tendsto (m : ℕ) {α β H : ℝ} (hβα : β < α) :
    Tendsto (fun k => 4 * H * (standardMollifier m k).rOut ^ (α - β)) atTop (𝓝 0) := by
  simpa using (standardMollifier_radius_tendsto m).rpow_const_nhds_zero (sub_pos.mpr hβα) |>.const_mul (4 * H)

end OAI.Analysis.PDE.Schauder
