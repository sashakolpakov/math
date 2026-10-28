import OAI.Analysis.Fourier.BochnerRiesz.Annular
import OAI.Analysis.Fourier.BesselPotential.AnnularLog
import OAI.Analysis.Fourier.Restriction.FourierProduct
import OAI.Analysis.Fourier.BochnerRiesz.Cutoff

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory
open scoped ContDiff ENNReal

namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

/-- A cutoff equal to one on the Fourier support fixes the function. -/
theorem annularProject_eq_self_of_support {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {h : ℝ} (hh : 0 < h) (f : SchwartzMap (Space n) ℂ)
    (hcut : ∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ (h • ξ) = 1) :
    (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ h f : Space n → ℂ) = f := by
  funext x
  rw [OAI.Analysis.Fourier.BochnerRiesz.annularProject_eq_frequencyHalfWave hχ hc hh]
  simp only [OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave, zero_mul, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul]
  calc
    _ = OAI.Analysis.Fourier.LocalSmoothing.angularInverse (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) x := by
      apply congrArg (fun g : Space n → ℂ => OAI.Analysis.Fourier.LocalSmoothing.angularInverse g x)
      funext ξ
      by_cases hz : OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ = 0
      · simp [hz]
      · rw [hcut ξ hz, one_mul]
    _ = _ := OAI.Analysis.Fourier.Restriction.angularInverse_angularFourier_schwartz f x

/-- Opposite differential and logarithmic orders cancel exactly on Schwartz
functions, with the manuscript's inhomogeneous logarithmic multiplier. -/
theorem logBesselPotential_neg_cancel {n : ℕ} (s B : ℝ)
    (f : SchwartzMap (Space n) ℂ) :
    OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential (-s) (-B) (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential s B f) = f := by
  have hweight (ξ : Space n) :
      ((1 + ‖ξ‖^2)^((-s)/2) * Real.log (2+Real.sqrt (1+‖ξ‖^2))^(-B)) *
      ((1 + ‖ξ‖^2)^(s/2) * Real.log (2+Real.sqrt (1+‖ξ‖^2))^B) = (1:ℝ) := by
    have hr : 0 < 1 + ‖ξ‖^2 := by positivity
    have hl : 0 < Real.log (2+Real.sqrt (1+‖ξ‖^2)) :=
      Real.log_pos (by linarith [Real.sqrt_nonneg (1+‖ξ‖^2)])
    rw [show (-s)/2 = -(s/2) by ring, Real.rpow_neg hr.le, Real.rpow_neg hl.le]
    have ha := (Real.rpow_pos_of_pos hr (s/2)).ne'
    have hb := (Real.rpow_pos_of_pos hl B).ne'
    field_simp
  funext x
  change OAI.Analysis.Fourier.LocalSmoothing.angularInverse _ x = f x
  calc
    _ = OAI.Analysis.Fourier.LocalSmoothing.angularInverse (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) x := by
      apply congrArg (fun g : Space n → ℂ => OAI.Analysis.Fourier.LocalSmoothing.angularInverse g x)
      funext ξ
      rw [OAI.Analysis.Fourier.BesselPotential.angularFourier_logBesselPotential, smul_smul, hweight, one_smul]
    _ = _ := OAI.Analysis.Fourier.Restriction.angularInverse_angularFourier_schwartz f x

/-- Matching upper annular estimate for the logarithmically weighted Sobolev
norm. This holds for either sign of both orders, uniformly in the scale. -/
theorem annular_logBesselPotential_bound {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (haway : ∀ ξ ∈ tsupport χ, 1 < ‖ξ‖) (s B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ (h • ξ) = 1) →
      ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential s B f) p volume ≤
        ENNReal.ofReal (C * h^(-s) * (1+Real.log (1/h))^B) *
          eLpNorm f p volume := by
  obtain ⟨C,hC,hbound⟩ := OAI.Analysis.Fourier.BesselPotential.annularProject_inverse_log_bessel_bound hχ hc haway (-s) (-B)
  refine ⟨C,hC,?_⟩
  intro h hh hone f hcut p hp hptop
  let g := OAI.Analysis.Fourier.BesselPotential.logBesselPotentialSchwartz s B f
  have hg : (g : Space n → ℂ) = OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential s B f :=
    OAI.Analysis.Fourier.BesselPotential.logBesselPotentialSchwartz_eq s B f
  have hcutg : ∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier g ξ ≠ 0 → χ (h • ξ) = 1 := by
    intro ξ hξ
    apply hcut ξ
    intro hz
    apply hξ
    rw [hg, OAI.Analysis.Fourier.BesselPotential.angularFourier_logBesselPotential, hz, smul_zero]
  have hfix := annularProject_eq_self_of_support hχ hc hh g hcutg
  have hcancel : OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential (-s) (-B) g = f := by
    rw [hg]
    exact logBesselPotential_neg_cancel s B f
  have hb := hbound h hh hone g p hp hptop
  rw [hfix, hcancel, neg_neg] at hb
  simpa only [hg] using hb

/-- A single fixed cutoff covers the frequency annuli `N ≤ |ξ| ≤ 2N`
after the normalization `h = 4/N`. -/
theorem exists_sharpness_annular_cutoff (n : ℕ) :
    ∃ χ : Space n → ℂ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (0 : Space n) ∉ tsupport χ ∧
      (∀ ξ ∈ tsupport χ, 1 < ‖ξ‖) ∧
      ∀ N : ℝ, 0 < N → ∀ ξ : Space n,
        N ≤ ‖ξ‖ → ‖ξ‖ ≤ 2*N → χ ((4/N) • ξ) = 1 := by
  obtain ⟨χ,hχ,hc,hzero,hone,hband⟩ := OAI.Analysis.Fourier.BochnerRiesz.exists_annular_cutoff (n := n)
    (a := 3) (b := 4) (c := 8) (d := 9)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨χ,hχ,hc,hzero,?_,?_⟩
  · intro ξ hξ
    apply OAI.Analysis.Fourier.BesselPotential.norm_gt_one_of_mem_tsupport_vanishing_two (χ := χ) _ hξ
    intro η hη
    by_contra hn
    have := (hband η hn).1
    linarith
  · intro N hN ξ hlo hhi
    apply hone
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 4/N)]
      have ht := mul_le_mul_of_nonneg_left hlo (show 0 ≤ 4/N by positivity)
      simpa only [div_mul_cancel₀ 4 hN.ne'] using ht
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 4/N)]
      have ht := mul_le_mul_of_nonneg_left hhi (show 0 ≤ 4/N by positivity)
      have he : (4/N)*(2*N) = 8 := by field_simp; ring
      simpa only [he] using ht

/-- Ordinary Sobolev norms on the literal annulus in the sharpness examples. -/
theorem sharpness_annular_bessel_bound (n : ℕ) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 4 ≤ N →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → N ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2*N) →
      ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential s f) p volume ≤
        ENNReal.ofReal (C * N^s) * eLpNorm f p volume := by
  obtain ⟨χ,hχ,hc,hzero,_,hcut⟩ := exists_sharpness_annular_cutoff n
  obtain ⟨C,hC,hbound⟩ := OAI.Analysis.Fourier.BochnerRiesz.annular_besselPotential_bound hχ hc hzero s
  refine ⟨C * (4:ℝ)^(-s),by positivity,?_⟩
  intro N hN f hf p hp hptop
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hb := hbound (4/N) (by positivity) ((div_le_one hN0).mpr hN) f
    f.integrable (fun ξ hξ => hcut N hN0 ξ (hf ξ hξ).1 (hf ξ hξ).2) p hp hptop
  have he : (4/N)^(-s) = (4:ℝ)^(-s) * N^s := by
    rw [Real.div_rpow (by norm_num) hN0.le, Real.rpow_neg hN0.le, div_inv_eq_mul]
  simpa only [he, mul_assoc] using hb

/-- Logarithmic Sobolev norms on the same literal annulus. The shifted
logarithm is uniformly comparable to `log N` at large `N`. -/
theorem sharpness_annular_log_bessel_bound (n : ℕ) (s B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 4 ≤ N →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → N ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2*N) →
      ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential s B f) p volume ≤
        ENNReal.ofReal (C * N^s * (1+Real.log (N/4))^B) *
          eLpNorm f p volume := by
  obtain ⟨χ,hχ,hc,_,haway,hcut⟩ := exists_sharpness_annular_cutoff n
  obtain ⟨C,hC,hbound⟩ := annular_logBesselPotential_bound hχ hc haway s B
  refine ⟨C * (4:ℝ)^(-s),by positivity,?_⟩
  intro N hN f hf p hp hptop
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hb := hbound (4/N) (by positivity) ((div_le_one hN0).mpr hN) f
    (fun ξ hξ => hcut N hN0 ξ (hf ξ hξ).1 (hf ξ hξ).2) p hp hptop
  have he : (4/N)^(-s) = (4:ℝ)^(-s) * N^s := by
    rw [Real.div_rpow (by norm_num) hN0.le, Real.rpow_neg hN0.le, div_inv_eq_mul]
  have hr : 1/(4/N) = N/4 := by field_simp
  simpa only [he, hr, mul_assoc] using hb

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
