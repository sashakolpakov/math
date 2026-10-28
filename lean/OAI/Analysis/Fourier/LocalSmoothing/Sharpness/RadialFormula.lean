import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.Polar
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.RadialAsymptotic
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.AnnularPacket

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff

def radialWave (n : ℕ) (t : ℝ) (x : Space n) : ℂ :=
  ∫ σ : ℝ, ((σ^(n-1)*radialBump σ : ℝ):ℂ) * phase (-t*σ) *
    OAI.Analysis.Fourier.Restriction.sphericalExtension (fun _ : Space n => (1:ℂ)) (σ • x)

theorem normalizedRadialWave_eq {n : ℕ} (hn : 1 ≤ n) (t : ℝ) (x : Space n) :
    normalizedRadialWave n (weightedRadialBump (radialOrder n)) t x =
      (‖x‖ ^ radialOrder n : ℝ) * radialWave n t x := by
  unfold normalizedRadialWave radialWave
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with σ
  by_cases hσ : radialBump σ = 0
  · simp only [weightedRadialBump,hσ,mul_zero,Complex.ofReal_zero,zero_mul]
  · have hσp : 0 < σ := lt_of_lt_of_le zero_lt_one
      (radialBump_support (subset_tsupport _ hσ)).1
    have hm : radialOrder n + radialOrder n = ((n-1:ℕ):ℝ) := by
      rw [Nat.cast_sub hn]
      simp only [radialOrder,Nat.cast_one]
      ring
    have hpow : σ ^ radialOrder n * ‖σ • x‖ ^ radialOrder n =
        ‖x‖ ^ radialOrder n * σ^(n-1) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hσp,
        Real.mul_rpow hσp.le (norm_nonneg x)]
      calc
        _ = (σ ^ radialOrder n * σ ^ radialOrder n) * ‖x‖ ^ radialOrder n := by ring
        _ = _ := by rw [← Real.rpow_add hσp,hm,Real.rpow_natCast]; ring
    simp only [weightedRadialBump,normalizedSphere,Complex.ofReal_mul]
    calc
      _ = (↑(σ ^ radialOrder n * ‖σ • x‖ ^ radialOrder n) : ℂ) *
          (radialBump σ : ℝ) * phase (-t*σ) *
          OAI.Analysis.Fourier.Restriction.sphericalExtension (fun _ : Space n => (1:ℂ)) (σ • x) := by
            push_cast
            ring
      _ = _ := by rw [hpow]; push_cast; ring

theorem radialWave_shell_lower {n : ℕ} (hn : 1 ≤ n) :
    ∃ η k R : ℝ, 0 < η ∧ 0 < k ∧ 1 ≤ R ∧ ∀ t : ℝ, ∀ x : Space n,
      R ≤ ‖x‖ → |‖x‖-t| ≤ η → k * ‖x‖ ^ (-radialOrder n) ≤ ‖radialWave n t x‖ := by
  obtain ⟨η,k,R,hη,hk,hR,h⟩ := normalizedRadialWave_shell_lower hn
  refine ⟨η,k,R,hη,hk,hR,fun t x hx ht => ?_⟩
  have hr : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one (hR.trans hx)
  have hh := h t x hx ht
  rw [normalizedRadialWave_eq hn,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hr _)] at hh
  rw [Real.rpow_neg hr.le,← div_eq_mul_inv]
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hr _)).2 (by simpa only [mul_comm] using hh)

theorem angularInverse_radial_formula {n : ℕ} (hn : 1 ≤ n) (t : ℝ) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ : Space n => phase (-t*‖ξ‖)*radialSymbol n ξ) x =
      (((2*Real.pi)^n)⁻¹ : ℝ) • radialWave n t x := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.angularInverse
  congr 1
  let F : Space n → ℂ := fun ξ => phase (inner ℝ x ξ) * (phase (-t*‖ξ‖)*radialSymbol n ξ)
  have hFc : Continuous F := by
    unfold F phase
    have h1 : Continuous (fun ξ : Space n => Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))) := by fun_prop
    have h2 : Continuous (fun ξ : Space n => Complex.exp (Complex.I * ((-t*‖ξ‖:ℝ):ℂ))) := by fun_prop
    exact h1.mul (h2.mul (radialSymbol_contDiff n).continuous)
  have haux : HasCompactSupport (fun ξ : Space n => phase (-t*‖ξ‖)*radialSymbol n ξ) :=
    (radialSymbol_hasCompactSupport n).mul_left
  have hFh : HasCompactSupport F := haux.mul_left
  change (∫ ξ, F ξ) = radialWave n t x
  rw [integral_polar_sphereMeasure hn hFc (hFc.integrable_of_hasCompactSupport hFh)]
  have hangular (σ : ℝ) (hσ : 0 < σ) :
      (∫ z : Space n, F (σ • z) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) =
      (radialBump σ : ℝ) * phase (-t*σ) *
        OAI.Analysis.Fourier.Restriction.sphericalExtension (fun _ : Space n => (1:ℂ)) (σ • x) := by
    unfold OAI.Analysis.Fourier.Restriction.sphericalExtension
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [OAI.MeasureTheory.Kakeya.ae_sphereMeasure_norm n] with z hz
    have hs : ‖σ • z‖ = σ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hσ,hz,mul_one]
    dsimp only [F,radialSymbol]
    rw [hs]
    have he : inner ℝ x (σ • z) = inner ℝ (σ • x) z := by
      rw [inner_smul_right,real_inner_smul_left]
    rw [he]
    change phase (inner ℝ (σ • x) z)*(phase (-t*σ)*(radialBump σ:ℝ)) = _
    change _ = (radialBump σ:ℝ)*phase (-t*σ)*(phase (inner ℝ (σ • x) z)*1)
    ring
  calc
    _ = ∫ σ in Ioi (0:ℝ), ((σ^(n-1)*radialBump σ:ℝ):ℂ) * phase (-t*σ) *
        OAI.Analysis.Fourier.Restriction.sphericalExtension (fun _ : Space n => (1:ℂ)) (σ • x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro σ hσ
      dsimp only
      rw [hangular σ hσ]
      simp only [Complex.real_smul,Complex.ofReal_mul]
      ring
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro σ hσ
      have hb : radialBump σ = 0 := image_eq_zero_of_notMem_tsupport (by
        intro hm
        have := (radialBump_support hm).1
        have : ¬ 0 < σ := hσ
        linarith)
      simp only [hb,mul_zero,Complex.ofReal_zero,zero_mul]

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
