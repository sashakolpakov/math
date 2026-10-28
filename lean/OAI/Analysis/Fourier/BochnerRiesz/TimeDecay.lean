import OAI.Analysis.Fourier.BochnerRiesz.Kernel
import OAI.Analysis.Fourier.BochnerRiesz.TimeHolder

open _root_.MeasureTheory
open scoped ENNReal

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

def timeDensity (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((1 + |t|) ^ (-2 : ℝ))

theorem measurable_timeDensity : Measurable timeDensity := by
  unfold timeDensity
  fun_prop

theorem timeDensity_le_one (t : ℝ) : timeDensity t ≤ 1 := by
  change ENNReal.ofReal _ ≤ _
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) (by norm_num)

theorem lintegral_timeDensity_lt_top : (∫⁻ t : ℝ, timeDensity t) < ⊤ := by
  have hi : Integrable (fun t : ℝ ↦ (1 + ‖t‖) ^ (-2 : ℝ)) := by
    apply integrable_one_add_norm
    norm_num
  have hn : ∀ t : ℝ, 0 ≤ (1 + |t|) ^ (-2 : ℝ) := by intro t; positivity
  have hi' : Integrable (fun t : ℝ ↦ (1 + |t|) ^ (-2 : ℝ)) := by
    simpa only [Real.norm_eq_abs] using hi
  exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hn)).mp hi'.hasFiniteIntegral

/-- Any Schwartz cutoff has enough temporal decay to leave a fixed
integrable density after extracting the local-smoothing time weight. -/
theorem schwartz_time_decay (φ : SchwartzMap ℝ ℂ) (M : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ,
      ‖φ t‖ ≤ A * (1 + |t|) ^ (-2 : ℝ) * (1 + |t|) ^ (-M) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (M + 2)
  let B : ℝ := 2 ^ N * (Finset.Iic (N, 0)).sup (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) φ
  have hB : 0 ≤ B := by positivity
  refine ⟨B + 1, by positivity, ?_⟩
  intro t
  have hb : (1 + |t|) ^ N * ‖φ t‖ ≤ B := by
    simpa [B] using SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℝ) (m := (N, 0)) (k := N) (n := 0) le_rfl le_rfl φ t
  have ht : 0 < 1 + |t| := by positivity
  have hb' : ‖φ t‖ ≤ (B + 1) * (1 + |t|) ^ (-(N : ℝ)) := by
    rw [Real.rpow_neg ht.le, Real.rpow_natCast, ← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos ht N)).mpr
    nlinarith
  calc
    _ ≤ (B + 1) * (1 + |t|) ^ (-(N : ℝ)) := hb'
    _ ≤ (B + 1) * (1 + |t|) ^ ((-2 : ℝ) + (-M)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) (by linarith)
    _ = _ := by rw [Real.rpow_add ht]; ring

end OAI.Analysis.Fourier.BochnerRiesz
