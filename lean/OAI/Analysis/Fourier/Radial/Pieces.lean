import OAI.Analysis.Fourier.Radial.Summation
import OAI.Analysis.Fourier.BochnerRiesz.Kernel
import OAI.Analysis.Fourier.BochnerRiesz.RadialPartition

/-! Exact rescaling and uniform Fourier estimates for the smooth pieces of
an endpoint power. The amplitude may be any smooth function; compact support
is supplied by the fixed annular profile. -/

open _root_.MeasureTheory Set
open scoped ContDiff

noncomputable section
namespace OAI.Analysis.Fourier.Radial

def endpointPiece (a : ℝ) (φ b : ℝ → ℂ) (δ t : ℝ) : ℂ :=
  (δ ^ a : ℝ) • (φ (δ⁻¹ * t) * b t)

theorem integral_rescale_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) {δ : ℝ} (hδ : 0 < δ) :
    ∫ t, F t = δ • ∫ u, F (δ * u) := by
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure ℝ) F δ (hR := hδ.le)
  simp only [Module.finrank_self, pow_one, smul_eq_mul] at h
  rw [h, smul_smul, mul_inv_cancel₀ hδ.ne', one_smul]

theorem endpointPiece_integrable {a δ : ℝ} (hδ : 0 < δ)
    {φ b : ℝ → ℂ} (hφ : Continuous φ) (hc : HasCompactSupport φ) (hb : Continuous b) :
    Integrable (endpointPiece a φ b δ) := by
  apply Continuous.integrable_of_hasCompactSupport
  · unfold endpointPiece
    fun_prop
  · have hs : HasCompactSupport (fun t : ℝ => φ (δ⁻¹ * t)) := by
      simpa only [smul_eq_mul] using hc.comp_smul (inv_ne_zero hδ.ne')
    have hm : HasCompactSupport (fun t : ℝ => φ (δ⁻¹ * t) * b t) := hs.mul_right
    apply hm.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport _)
    intro t ht
    apply subset_tsupport (fun t : ℝ => φ (δ⁻¹ * t) * b t)
    intro he
    exact ht (by simp only [endpointPiece, he, smul_zero])

theorem endpointPiece_fourier_rescale (a : ℝ) (φ b : ℝ → ℂ) {δ : ℝ}
    (hδ : 0 < δ) (x : ℝ) :
    (∫ t, Complex.exp (Complex.I * (x * t : ℝ)) * endpointPiece a φ b δ t) =
      (δ ^ (a + 1) : ℝ) •
        ∫ u, Complex.exp (Complex.I * ((δ * x) * u : ℝ)) * (φ u * b (δ * u)) := by
  rw [integral_rescale_real _ hδ]
  have he (u : ℝ) :
      Complex.exp (Complex.I * (x * (δ * u) : ℝ)) * endpointPiece a φ b δ (δ * u) =
      (δ ^ a : ℝ) •
        (Complex.exp (Complex.I * ((δ * x) * u : ℝ)) * (φ u * b (δ * u))) := by
    rw [show x * (δ * u) = (δ * x) * u by ring]
    simp only [endpointPiece, inv_mul_cancel_left₀ hδ.ne', mul_smul_comm]
  simp_rw [he]
  rw [integral_smul, smul_smul, Real.rpow_add hδ, Real.rpow_one, mul_comm δ]

theorem uniform_endpointPiece_bounds {φ b : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hb : ContDiff ℝ ∞ b)
    (a : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ, 0 < δ → δ ≤ 1 →
      (∫ t, ‖endpointPiece a φ b δ t‖) ≤ C * δ ^ (a + 1) ∧
      ∀ x : ℝ,
        ‖∫ t, Complex.exp (Complex.I * (x * t : ℝ)) * endpointPiece a φ b δ t‖ ≤
          C * δ ^ (a + 1) * (1 + δ * |x|) ^ (-(N : ℝ)) := by
  let A : ℝ × ℝ → ℂ := fun q => φ q.2 * b (q.1 * q.2)
  have hA : ContDiff ℝ ∞ A :=
    (hφ.comp contDiff_snd).mul (hb.comp (contDiff_fst.mul contDiff_snd))
  have hS : tsupport A ⊆ univ ×ˢ tsupport φ := by
    apply closure_minimal _ (isClosed_univ.prod (isClosed_tsupport φ))
    intro q hq
    refine ⟨mem_univ _, subset_tsupport φ ?_⟩
    intro he
    exact hq (by simp [A, he])
  obtain ⟨D, hD, hd⟩ := OAI.Analysis.Fourier.BochnerRiesz.uniform_fourier_integral_polynomial_decay
    (μ := (volume : Measure ℝ)) (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)) hc hA hS N
  obtain ⟨B, hB, hbound⟩ :=
    (((isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).prod hc).image hA.continuous).isBounded.exists_pos_norm_le
  let L := B * volume.real (tsupport φ)
  have hL : 0 ≤ L := mul_nonneg hB.le ENNReal.toReal_nonneg
  refine ⟨L + D + 1, by linarith, ?_⟩
  intro δ hδ hδ1
  have hnorm : (∫ u, ‖A (δ, u)‖) ≤ L := by
    apply OAI.Analysis.Fourier.WavePackets.integral_norm_le_of_compact_support_bound hc
    · intro u hu
      exact subset_tsupport φ (fun he => hu (by simp [A, he]))
    · intro u hu
      exact hbound _ ⟨(δ, u), ⟨⟨hδ.le, hδ1⟩, hu⟩, rfl⟩
  constructor
  · rw [integral_rescale_real _ hδ]
    have he (u : ℝ) : ‖endpointPiece a φ b δ (δ * u)‖ = δ ^ a * ‖A (δ, u)‖ := by
      simp only [endpointPiece, inv_mul_cancel_left₀ hδ.ne', norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hδ a), A]
    simp_rw [he]
    rw [integral_const_mul, smul_eq_mul, ← mul_assoc]
    have hp : δ * δ ^ a = δ ^ (a + 1) := by rw [Real.rpow_add hδ, Real.rpow_one]; ring
    rw [hp]
    calc
      _ ≤ δ ^ (a + 1) * L := mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ ≤ _ := by nlinarith [Real.rpow_pos_of_pos hδ (a + 1)]
  · intro x
    rw [endpointPiece_fourier_rescale a φ b hδ, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hδ (a + 1))]
    have H := hd δ ⟨hδ.le, hδ1⟩ (δ * x)
    simp only [RCLike.inner_apply, conj_trivial, Real.norm_eq_abs, abs_mul, abs_of_pos hδ, A] at H
    simp only [mul_comm _ (δ * x)] at H
    calc
      _ ≤ δ ^ (a + 1) * (D * (1 + δ * |x|) ^ (-(N : ℝ))) :=
        mul_le_mul_of_nonneg_left H (by positivity)
      _ ≤ _ := by
        have hp : 0 ≤ δ ^ (a + 1) * (1 + δ * |x|) ^ (-(N : ℝ)) := by positivity
        nlinarith

end OAI.Analysis.Fourier.Radial
