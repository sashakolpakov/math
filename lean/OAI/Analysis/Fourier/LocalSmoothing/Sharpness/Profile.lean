import OAI.Analysis.Fourier.WavePackets.Oscillatory
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff FourierTransform

def radialProfile (g : ℝ → ℝ) (v : ℝ) : ℂ :=
  ∫ σ : ℝ, Complex.exp (Complex.I * ((v*σ : ℝ) : ℂ)) * (g σ : ℂ)

theorem continuous_radialProfile {g : ℝ → ℝ} (hg : Integrable g) :
    Continuous (radialProfile g) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  apply tendsto_integral_filter_of_dominated_convergence (fun σ => ‖g σ‖)
  · exact Eventually.of_forall (fun w =>
      ((by fun_prop : Continuous (fun σ : ℝ => Complex.exp (Complex.I * ((w*σ : ℝ) : ℂ)))).aestronglyMeasurable.mul
        (Complex.ofRealCLM.continuous.comp_aestronglyMeasurable hg.aestronglyMeasurable)))
  · exact Eventually.of_forall (fun w => Eventually.of_forall (fun σ => by
      simp only [norm_mul,Complex.norm_exp_I_mul_ofReal,one_mul,Complex.norm_real]
      exact le_rfl))
  · exact hg.norm
  · exact Eventually.of_forall (fun σ => (by fun_prop :
      Continuous (fun w : ℝ => Complex.exp (Complex.I * ((w*σ : ℝ) : ℂ)) * (g σ : ℂ))).tendsto v)

theorem radialProfile_zero {g : ℝ → ℝ} (hg : Integrable g) :
    radialProfile g 0 = ((∫ σ, g σ : ℝ) : ℂ) := by
  simp only [radialProfile,zero_mul,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul]
  exact Complex.ofRealCLM.integral_comp_comm hg

theorem radialProfile_lower_near_zero {g : ℝ → ℝ} (hg : Integrable g)
    (hpos : 0 < ∫ σ, g σ) :
    ∃ η c : ℝ, 0 < η ∧ 0 < c ∧ ∀ v, |v| ≤ η → c ≤ ‖radialProfile g v‖ := by
  have hzero : 0 < ‖radialProfile g 0‖ := by
    rw [radialProfile_zero hg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpos]
    exact hpos
  let c := ‖radialProfile g 0‖/2
  have hc : 0 < c := half_pos hzero
  have he : ∀ᶠ v in 𝓝 (0:ℝ), c < ‖radialProfile g v‖ :=
    continuousAt_const.eventually_lt ((continuous_radialProfile hg).norm.continuousAt) (by
      dsimp [c]
      linarith)
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨ε/2,c,half_pos hε,hc,?_⟩
  intro v hv
  have hlt : |v| < ε := hv.trans_lt (by linarith)
  exact (hsub (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hlt)).le

theorem radialProfile_eq_fourier (g : ℝ → ℝ) (s : ℝ) :
    radialProfile g (-s) =
      𝓕 (fun x => (g x : ℂ)) (s/(2*Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul]
  congr 2
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp


/-- The incoming radial profile tends to zero. This is the actual
Riemann--Lebesgue theorem, not a nonstationary-phase assumption. -/
theorem radialProfile_negative_tendsto (g : ℝ → ℝ) :
    Tendsto (fun s : ℝ => radialProfile g (-s)) atTop (𝓝 0) := by
  simp_rw [radialProfile_eq_fourier]
  apply (Real.zero_at_infty_fourier (fun x => (g x : ℂ))).comp
  exact ((tendsto_div_const_atTop_of_pos (by positivity : 0 < 2*Real.pi)).2 tendsto_id).mono_right
    atTop_le_cocompact

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
