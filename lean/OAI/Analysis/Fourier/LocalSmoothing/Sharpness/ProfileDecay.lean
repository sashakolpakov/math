import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.Profile

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Set Filter _root_.MeasureTheory FourierTransform
open scoped Topology ContDiff FourierTransform

/-- Every polynomial decay bound for the actual compact smooth radial
Fourier profile. The proof uses the Schwartz Fourier transform. -/
theorem radialProfile_polynomial_decay {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, |s|^k * ‖radialProfile g (-s)‖ ≤ C := by
  have hcg : ContDiff ℝ ∞ (fun x => (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have hsc : HasCompactSupport (fun x => (g x : ℂ)) := by
    apply hc.mono'
    intro x hx
    apply subset_tsupport g
    intro hz
    apply hx
    simp only [hz,Complex.ofReal_zero]
  let q : SchwartzMap ℝ ℂ := hsc.toSchwartzMap hcg
  let Q : SchwartzMap ℝ ℂ := 𝓕 q
  let C := (2*Real.pi)^k * SchwartzMap.seminorm ℝ k 0 Q
  refine ⟨C,mul_nonneg (by positivity) (apply_nonneg _ _),fun s => ?_⟩
  have he : radialProfile g (-s) = Q (s/(2*Real.pi)) := by
    rw [radialProfile_eq_fourier]
    change _ = (𝓕 q : SchwartzMap ℝ ℂ) (s/(2*Real.pi))
    rw [SchwartzMap.fourier_coe]
    rfl
  rw [he]
  have h := SchwartzMap.norm_pow_mul_le_seminorm ℝ Q k (s/(2*Real.pi))
  have hp : 0 < 2*Real.pi := by positivity
  have hp0 : 2*Real.pi ≠ 0 := hp.ne'
  have hh := mul_le_mul_of_nonneg_left h (pow_nonneg hp.le k)
  dsimp [C]
  convert hh using 1
  rw [Real.norm_eq_abs,abs_div,abs_of_pos hp,div_pow]
  field_simp

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
