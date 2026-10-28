import OAI.Analysis.PDE.WaveEquation.VelocityBound
import OAI.Analysis.PDE.WaveEquation.Formula

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter FourierTransform
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.Dispersion

def complexAngularSchwartzMultiplier {n : ℕ} (m : Space n → ℂ)
    (f : SchwartzMap (Space n) ℂ) : SchwartzMap (Space n) ℂ :=
  SchwartzMap.fourierMultiplierCLM ℂ (fun ξ ↦ m ((2*Real.pi) • ξ)) f

theorem complexAngularSchwartzMultiplier_eq_integral {n : ℕ} {m : Space n → ℂ}
    (hm : m.HasTemperateGrowth) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    complexAngularSchwartzMultiplier m f x =
      OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ m ξ * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ) x := by
  have ht : (fun ξ : Space n ↦ m ((2*Real.pi) • ξ)).HasTemperateGrowth := hm.comp (by fun_prop)
  rw [complexAngularSchwartzMultiplier,SchwartzMap.fourierMultiplierCLM_apply,
    SchwartzMap.fourierInv_coe,OAI.Analysis.Fourier.Wave.angularInverse_eq_fourierInv_scaled]
  apply Real.fourierInv_congr_ae
  exact Filter.Eventually.of_forall fun ξ ↦ by
    rw [SchwartzMap.smulLeftCLM_apply_apply ht]
    dsimp only
    rw [OAI.Analysis.Fourier.Wave.angularFourier_scaled,SchwartzMap.fourier_coe]
    rfl

theorem angularFourier_complexAngularSchwartzMultiplier {n : ℕ} {m : Space n → ℂ}
    (hm : m.HasTemperateGrowth) (f : SchwartzMap (Space n) ℂ) (ξ : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (complexAngularSchwartzMultiplier m f) ξ = m ξ * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ := by
  have hp : (2*Real.pi:ℝ) ≠ 0 := by positivity
  have ht : (fun ξ : Space n ↦ m ((2*Real.pi) • ξ)).HasTemperateGrowth := hm.comp (by fun_prop)
  have he : (2*Real.pi) • ((2*Real.pi)⁻¹ • ξ) = ξ := by
    rw [smul_smul,mul_inv_cancel₀ hp,one_smul]
  conv_lhs => rw [← he]
  rw [OAI.Analysis.Fourier.Wave.angularFourier_scaled]
  change (𝓕 (complexAngularSchwartzMultiplier m f) : SchwartzMap (Space n) ℂ)
    ((2*Real.pi)⁻¹ • ξ) = _
  rw [complexAngularSchwartzMultiplier,SchwartzMap.fourierMultiplierCLM_apply,
    FourierTransform.fourier_fourierInv_eq,SchwartzMap.smulLeftCLM_apply_apply ht,he]
  change m ξ * _ = _
  congr 1
  rw [SchwartzMap.fourier_coe,← OAI.Analysis.Fourier.Wave.angularFourier_scaled,he]

theorem complexAngularSchwartzMultiplier_sub_one {n : ℕ} {m : Space n → ℂ}
    (hm : m.HasTemperateGrowth) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    complexAngularSchwartzMultiplier (fun ξ ↦ m ξ-1) f x =
      complexAngularSchwartzMultiplier m f x - f x := by
  have hd : (fun ξ ↦ m ξ-1).HasTemperateGrowth := hm.sub (Function.HasTemperateGrowth.const 1)
  have hi : Integrable (fun ξ ↦ m ξ * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ) := by
    rw [← funext (angularFourier_complexAngularSchwartzMultiplier hm f)]
    exact OAI.Analysis.Fourier.Restriction.integrable_angularFourier_schwartz (complexAngularSchwartzMultiplier m f)
  rw [complexAngularSchwartzMultiplier_eq_integral hd,
    complexAngularSchwartzMultiplier_eq_integral hm,
    ← OAI.Analysis.Fourier.Restriction.angularInverse_angularFourier_schwartz f x,
    ← OAI.Analysis.Fourier.LocalSmoothing.angularInverse_sub_of_integrable hi (OAI.Analysis.Fourier.Restriction.integrable_angularFourier_schwartz f)]
  congr 1
  funext ξ
  ring

/-- A uniform multiplier bound obtained by summing a genuine order-minus-one
dyadic defect of the identity. No multiplier theorem is assumed. -/
theorem complex_multiplier_bound_of_dyadic_defect {n : ℕ}
    {m : ℝ → Space n → ℂ} (hm : ∀ t, (m t).HasTemperateGrowth)
    {a : (ℝ × ℝ) × Space n → ℂ} {l : ℝ × Space n → ℂ}
    (ha : ContDiff ℝ ∞ a) (hl : ContDiff ℝ ∞ l)
    (has : tsupport a ⊆ univ ×ˢ tsupport (@OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff n))
    (hls : tsupport l ⊆ univ ×ˢ tsupport (@OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff n))
    (hle : ∀ t ξ, (m t ξ-1)*OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff ξ = l (t,ξ))
    (hae : ∀ t h : ℝ, 0<h → h≤1 → ∀ ξ,
      (m t ξ-1)*OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff (h•ξ) = (h:ℂ)*a ((t,h),h•ξ)) :
    ∃ C : ℝ, 0<C ∧ ∀ t ∈ Icc (1:ℝ) 2, ∀ f : SchwartzMap (Space n) ℂ,
      ∀ p : ℝ≥0∞, 1≤p → p≠⊤ →
      eLpNorm (complexAngularSchwartzMultiplier (m t) f) p volume ≤
        ENNReal.ofReal C * eLpNorm f p volume := by
  obtain ⟨A,hA,hAb⟩ := OAI.Analysis.Fourier.BochnerRiesz.uniform_frequencyHalfWave_zero_bound
    (K := Icc (1:ℝ) 2 ×ˢ Icc (0:ℝ) 1) (isCompact_Icc.prod isCompact_Icc)
    (OAI.Analysis.Fourier.LocalSmoothing.hasCompactSupport_smoothingAnnularCutoff n) ha has
  obtain ⟨B,hB,hBb⟩ := OAI.Analysis.Fourier.BochnerRiesz.uniform_frequencyHalfWave_zero_bound
    (K := Icc (1:ℝ) 2) isCompact_Icc
    (OAI.Analysis.Fourier.LocalSmoothing.hasCompactSupport_smoothingLowCutoff n) hl hls
  let w : ℕ → ℝ := OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale
  have hw0 : ∀ j, 0 ≤ w j := fun j ↦ (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_pos j).le
  have hw : Summable w := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  let D : ℝ := B + A * ∑' j, w j
  have hD : 0 ≤ D := add_nonneg hB (mul_nonneg hA (tsum_nonneg hw0))
  refine ⟨1+D,by linarith,fun t ht f p hp hpt ↦ ?_⟩
  let u := complexAngularSchwartzMultiplier (fun ξ ↦ m t ξ-1) f
  have hd : (fun ξ ↦ m t ξ-1).HasTemperateGrowth :=
    (hm t).sub (Function.HasTemperateGrowth.const 1)
  have hu : eLpNorm u p volume ≤ ENNReal.ofReal D * eLpNorm f p volume := by
    apply OAI.Analysis.PDE.WaveEquation.schwartz_norm_le_of_dyadic_bounds u hp hw0 hw hB hA
    · have he : OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff 1 0 u =
          OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave (fun ξ ↦ l (t,ξ)) 1 0 f := by
        funext x
        simpa only [one_smul] using OAI.Analysis.PDE.WaveEquation.frequencyHalfWave_zero_transfer f u
          OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff (fun ξ ↦ l (t,ξ)) 1 1 (fun ξ ↦ by
            simp only [u,angularFourier_complexAngularSchwartzMultiplier hd,
              Complex.ofReal_one,one_mul,one_smul]
            rw [← mul_assoc,mul_comm (OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff ξ),hle]) x
      rw [he]
      exact hBb t ht 1 (by norm_num) f f.integrable p hp hpt
    · intro j
      have he : OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff (w j) 0 u =
          (w j) • OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave (fun ξ ↦ a ((t,w j),ξ)) (w j) 0 f := by
        funext x
        apply OAI.Analysis.PDE.WaveEquation.frequencyHalfWave_zero_transfer
        intro ξ
        simp only [u,angularFourier_complexAngularSchwartzMultiplier hd]
        rw [← mul_assoc,mul_comm (OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff _),
          hae t (w j) (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_pos j) (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_le_one j)]
      rw [he,eLpNorm_const_smul,Real.enorm_eq_ofReal (hw0 j)]
      have hb := hAb (t,w j) ⟨ht,(OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_pos j).le,OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_le_one j⟩
        (w j) (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_pos j) f f.integrable p hp hpt
      apply (mul_le_mul_right hb _).trans_eq
      rw [ENNReal.ofReal_mul hA]
      ac_rfl
  have he : (complexAngularSchwartzMultiplier (m t) f : Space n → ℂ) =
      fun x ↦ f x + u x := by
    funext x
    have hx := complexAngularSchwartzMultiplier_sub_one (hm t) f x
    change u x = _ at hx
    rw [hx]
    ring
  rw [he]
  calc
    _ ≤ eLpNorm f p volume + eLpNorm u p volume := eLpNorm_add_le hp
    _ ≤ eLpNorm f p volume + ENNReal.ofReal D * eLpNorm f p volume := add_le_add le_rfl hu
    _ = _ := by rw [ENNReal.ofReal_add (by norm_num) hD,ENNReal.ofReal_one,add_mul,one_mul]

end OAI.Analysis.Fourier.Dispersion
