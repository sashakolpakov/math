import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.Profile

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff

def phase (v : ℝ) : ℂ := Complex.exp (Complex.I * (v : ℂ))

@[simp] theorem norm_phase (v : ℝ) : ‖phase v‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal v

theorem phase_mul (u v : ℝ) : phase u * phase v = phase (u+v) := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integrable_phase_weight {g : ℝ → ℝ} (hg : Continuous g)
    (hc : HasCompactSupport g) (t : ℝ) {K : ℝ → ℂ} (hK : Continuous K) :
    Integrable (fun σ => phase (-t*σ) * (g σ : ℂ) * K σ) := by
  have hp : Continuous (fun σ : ℝ => phase (-t*σ)) := by unfold phase; fun_prop
  have hcg : Continuous (fun σ => (g σ : ℂ)) := Complex.continuous_ofReal.comp hg
  have hsc0 : HasCompactSupport (fun σ => (g σ : ℂ)) := by
    apply hc.mono'
    intro σ hσ
    apply subset_tsupport g
    intro hz
    apply hσ
    simp only [hz,Complex.ofReal_zero]
  have hsc1 : HasCompactSupport (fun σ => phase (-t*σ) * (g σ : ℂ)) := hsc0.mul_left
  have hsc : HasCompactSupport (fun σ => phase (-t*σ) * (g σ : ℂ) * K σ) := hsc1.mul_right
  exact ((hp.mul hcg).mul hK).integrable_of_hasCompactSupport hsc

theorem integral_two_phases {g : ℝ → ℝ} (hg : Continuous g)
    (hc : HasCompactSupport g) (c : ℂ) (r t : ℝ) :
    (∫ σ : ℝ, phase (-t*σ) * (g σ : ℂ) *
      (c * phase (r*σ) + star c * phase (-r*σ))) =
      c * radialProfile g (r-t) + star c * radialProfile g (-(r+t)) := by
  have hi (v : ℝ) : Integrable (fun σ : ℝ => phase (v*σ) * (g σ : ℂ)) := by
    simpa only [neg_neg,mul_one] using
      integrable_phase_weight hg hc (-v) (K := fun _ => (1:ℂ)) continuous_const
  have he (σ : ℝ) :
      phase (-t*σ) * (g σ : ℂ) * (c*phase (r*σ)+star c*phase (-r*σ)) =
      c*(phase ((r-t)*σ)*(g σ:ℂ)) + star c*(phase ((-(r+t))*σ)*(g σ:ℂ)) := by
    calc
      _ = c*(phase (-t*σ)*phase (r*σ))*(g σ:ℂ) +
          star c*(phase (-t*σ)*phase (-r*σ))*(g σ:ℂ) := by ring
      _ = _ := by
        rw [phase_mul,phase_mul]
        rw [show -t*σ+r*σ=(r-t)*σ by ring,
          show -t*σ + -r*σ=(-(r+t))*σ by ring]
        ring
  simp_rw [he]
  rw [integral_add ((hi _).const_mul c) ((hi _).const_mul (star c)),
    integral_const_mul,integral_const_mul]
  rfl

/-- Integrating a pointwise two-phase expansion against a compact radial
amplitude preserves its explicit error. -/
theorem integral_two_phase_error {g : ℝ → ℝ} (hg : Continuous g)
    (hc : HasCompactSupport g) {K : ℝ → ℂ} (hK : Continuous K)
    (c : ℂ) (r t E : ℝ) (_ : 0 ≤ E)
    (herr : ∀ σ ∈ tsupport g,
      ‖K σ - (c*phase (r*σ)+star c*phase (-r*σ))‖ ≤ E) :
    ‖(∫ σ : ℝ, phase (-t*σ)*(g σ:ℂ)*K σ) -
      (c*radialProfile g (r-t)+star c*radialProfile g (-(r+t)))‖ ≤
        E * ∫ σ, ‖g σ‖ := by
  let Q : ℝ → ℂ := fun σ => c*phase (r*σ)+star c*phase (-r*σ)
  have hQ : Continuous Q := by unfold Q phase; fun_prop
  rw [← integral_two_phases hg hc c r t,
    ← integral_sub (integrable_phase_weight hg hc t hK)
      (integrable_phase_weight hg hc t hQ), ← integral_const_mul]
  apply norm_integral_le_of_norm_le ((hg.integrable_of_hasCompactSupport hc).norm.const_mul E)
  filter_upwards [] with σ
  change ‖phase (-t*σ)*(g σ:ℂ)*K σ - phase (-t*σ)*(g σ:ℂ)*Q σ‖ ≤ E*‖g σ‖
  rw [← mul_sub,norm_mul,norm_mul,norm_phase,one_mul,Complex.norm_real]
  by_cases hs : σ ∈ tsupport g
  · exact (mul_le_mul_of_nonneg_left (herr σ hs) (norm_nonneg _)).trans_eq (mul_comm _ _)
  · rw [image_eq_zero_of_notMem_tsupport hs]
    simp

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
