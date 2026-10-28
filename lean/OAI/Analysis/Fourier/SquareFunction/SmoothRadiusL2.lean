import OAI.Analysis.Fourier.SquareFunction.SmoothRadiusPlancherel
import OAI.Analysis.Fourier.SquareFunction.KernelDilation
import OAI.Analysis.Fourier.SquareFunction.FourierDilation

open OAI.Analysis.Fourier.Wave

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform Set
open scoped ENNReal

theorem hasCompactSupport_radius_frequency_dilate {n : ℕ} {A : ℝ × Space n → ℂ}
    (hc : HasCompactSupport A) {a : ℝ} (ha : a ≠ 0) :
    HasCompactSupport (fun z : ℝ × Space n => A (z.1, a⁻¹ • z.2)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hc.image (show Continuous (fun z : ℝ × Space n => (z.1, a • z.2)) by fun_prop))
  intro z hz
  refine ⟨(z.1, a⁻¹ • z.2), subset_tsupport A hz, ?_⟩
  simp only [smul_inv_smul₀ ha]

theorem smoothRadiusKernel_dilate {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) {a : ℝ} (ha : 0 < a) (x : Space n) :
    smoothRadiusKernel (fun z : ℝ × Space n => A (z.1, a⁻¹ • z.2)) (by fun_prop) x =
      dilatedKernel (smoothRadiusKernel A hA) a x := by
  change radiusToL2 (𝓕⁻ (fun ξ => smoothRadiusSymbol A hA (a⁻¹ • ξ)) x) = _
  rw [fourierInv_dilate_cycles _ (inv_pos.mpr ha), inv_pow, inv_inv, inv_inv]
  change (radiusToL2.restrictScalars ℝ) (a ^ n • 𝓕⁻ (smoothRadiusSymbol A hA) (a • x)) = _
  rw [map_smul]
  rfl

theorem smoothRadiusKernel_family_two_bound {n : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → ℝ × Space n → ℂ) (hA : ∀ i, Continuous (A i))
    (hc : ∀ i, HasCompactSupport (A i)) (M : ℝ≥0∞)
    (hM : ∀ ξ : Space n,
      ∑ i, ∫⁻ r in Icc (1 : ℝ) 2, ‖A i (r, ξ)‖ₑ ^ (2 : ℝ) ≤ M)
    {f : Space n → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    eLpNorm (fun x => vectorNorm (fun i => convolveKernel (smoothRadiusKernel (A i) (hA i)) f x))
      2 volume ≤ M ^ (1 / 2 : ℝ) * eLpNorm f 2 volume := by
  classical
  let : MeasurableSpace RadiusHilbert := borel RadiusHilbert
  let : BorelSpace RadiusHilbert := ⟨rfl⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let V (i : ι) := convolveKernel (smoothRadiusKernel (A i) (hA i)) f
  have hV (i : ι) : Continuous (V i) := continuous_convolve_smoothRadiusKernel (A i) (hA i) (hc i) hf
  have hv : Measurable (fun x => vectorNorm (fun i => V i x)) := measurable_vectorNorm V (fun i => (hV i).measurable)
  have he (i : ι) : (∫⁻ x : Space n, ‖V i x‖ₑ ^ (2 : ℝ)) =
      ∫⁻ ξ : Space n, (∫⁻ r in Icc (1 : ℝ) 2, ‖A i (r, ξ)‖ₑ ^ (2 : ℝ)) *
        ‖𝓕 f ξ‖ₑ ^ (2 : ℝ) := by
    simp only [V, convolve_smoothRadiusKernel (A i) (hA i) (hc i) hf]
    exact smoothRadiusOutput_energy (A i) (hA i) (hc i) hf
  have hm (i : ι) : Measurable (fun ξ : Space n =>
      (∫⁻ r in Icc (1 : ℝ) 2, ‖A i (r, ξ)‖ₑ ^ (2 : ℝ)) * ‖𝓕 f ξ‖ₑ ^ (2 : ℝ)) := by
    exact ((((hA i).measurable.comp measurable_swap).enorm.pow_const (2 : ℝ)).lintegral_prod_right).mul
      ((OAI.Analysis.Fourier.BochnerRiesz.continuous_fourier_of_integrable hf).measurable.enorm.pow_const (2 : ℝ))
  have hb : eLpNorm (fun x => vectorNorm (fun i => V i x)) 2 volume ^ (2 : ℝ) ≤
      M * eLpNorm f 2 volume ^ (2 : ℝ) := by
    rw [eLpNorm_two_rpow_general volume hv.aestronglyMeasurable]
    have hev (x : Space n) : ‖vectorNorm (fun i => V i x)‖ₑ ^ (2 : ℝ) =
        ∑ i, ‖V i x‖ₑ ^ (2 : ℝ) := by
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (vectorNorm_nonneg _),
        enorm_vectorNorm_sq]
    simp_rw [hev]
    rw [lintegral_finsetSum _ (fun i _ => ((hV i).measurable.enorm.pow_const (2 : ℝ)))]
    simp_rw [he]
    rw [← lintegral_finsetSum _ (fun i _ => hm i)]
    calc
      _ ≤ ∫⁻ ξ : Space n, M * ‖𝓕 f ξ‖ₑ ^ (2 : ℝ) := by
        apply lintegral_mono
        intro ξ
        dsimp only
        rw [← Finset.sum_mul]
        exact mul_le_mul' (hM ξ) le_rfl
      _ = M * eLpNorm f 2 volume ^ (2 : ℝ) := by
        rw [lintegral_const_mul _ ((OAI.Analysis.Fourier.BochnerRiesz.continuous_fourier_of_integrable hf).measurable.enorm.pow_const (2 : ℝ)),
          ← eLpNorm_two_rpow_general volume (OAI.Analysis.Fourier.BochnerRiesz.continuous_fourier_of_integrable hf).aestronglyMeasurable,
          eLpNorm_fourier_cycles hf hf2]
  have H := ENNReal.rpow_le_rpow hb (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one, V] using H

theorem dyadic_smoothRadiusKernel_two_bound {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (hc : HasCompactSupport A) (s : Finset ℤ) (M : ℝ≥0∞)
    (hM : ∀ ξ : Space n, ∑ k ∈ s, ∫⁻ r in Icc (1 : ℝ) 2,
      ‖A (r, ((2 : ℝ) ^ k)⁻¹ • ξ)‖ₑ ^ (2 : ℝ) ≤ M)
    {f : Space n → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    eLpNorm (fun x => vectorNorm (fun i : s =>
      convolveKernel (dilatedKernel (smoothRadiusKernel A hA) ((2 : ℝ) ^ i.val)) f x)) 2 volume ≤
        M ^ (1 / 2 : ℝ) * eLpNorm f 2 volume := by
  let B (i : s) (z : ℝ × Space n) := A (z.1, ((2 : ℝ) ^ i.val)⁻¹ • z.2)
  have hB (i : s) : Continuous (B i) := by dsimp [B]; fun_prop
  have hcB (i : s) : HasCompactSupport (B i) :=
    hasCompactSupport_radius_frequency_dilate hc (by positivity)
  have hMB (ξ : Space n) : ∑ i : s, ∫⁻ r in Icc (1 : ℝ) 2,
      ‖B i (r, ξ)‖ₑ ^ (2 : ℝ) ≤ M := by
    exact (Finset.sum_coe_sort s (fun k => ∫⁻ r in Icc (1 : ℝ) 2,
      ‖A (r, ((2 : ℝ) ^ k)⁻¹ • ξ)‖ₑ ^ (2 : ℝ))).le.trans (hM ξ)
  have H := smoothRadiusKernel_family_two_bound B hB hcB M hMB hf hf2
  have he (i : s) : smoothRadiusKernel (B i) (hB i) =
      dilatedKernel (smoothRadiusKernel A hA) ((2 : ℝ) ^ i.val) := by
    funext x
    exact smoothRadiusKernel_dilate A hA (by positivity) x
  simpa only [he] using H

end OAI.Analysis.Fourier.SquareFunction
