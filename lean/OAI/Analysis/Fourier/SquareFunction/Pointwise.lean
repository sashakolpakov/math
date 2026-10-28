import OAI.Analysis.Fourier.SquareFunction.Plancherel
import OAI.Analysis.Fourier.Wave.Compatibility
import OAI.Analysis.Fourier.Estimates
import OAI.Analysis.Fourier.Wave.AngularTransform

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform Set
open scoped ENNReal

noncomputable section
namespace OAI.Analysis.Fourier.SquareFunction

/-- The classical differentiated multiplier, using cycles per unit frequency. -/
def radiusDerivativeCycles {n : ℕ} (α r : ℝ) (f : SchwartzMap (Space n) ℂ) :
    Space n → ℂ :=
  𝓕⁻ (fun ξ => (radiusMultiplier α ‖ξ‖ r : ℂ) * (𝓕 f) ξ)

theorem integrable_radius_symbol {n : ℕ} (α r : ℝ) (g : Space n → ℂ)
    (hg : MemLp (fun ξ => (radiusMultiplier α ‖ξ‖ r : ℂ) * g ξ) 2) :
    Integrable (fun ξ => (radiusMultiplier α ‖ξ‖ r : ℂ) * g ξ) := by
  have hs : Function.support (fun ξ => (radiusMultiplier α ‖ξ‖ r : ℂ) * g ξ) ⊆
      Metric.closedBall (0 : Space n) r := by
    intro ξ hξ
    by_contra hn
    have hgt : r < ‖ξ‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hn
    have hnr : ¬ ‖ξ‖ < r := by
      exact not_lt_of_ge hgt.le
    exact hξ (by simp [radiusMultiplier, hnr])
  exact (integrableOn_iff_integrable_of_support_subset hs).1
    ((hg.locallyIntegrable (by norm_num)).integrableOn_isCompact (isCompact_closedBall 0 r))

private theorem classical_multiplier_coe {n : ℕ} (m : Space n → ℂ) (f : OAI.Analysis.Fourier.Wave.WaveL2 n)
    (hdom : MemLp (fun ξ => m ξ * ((Lp.fourierTransformₗᵢ (Space n) ℂ) f) ξ) 2)
    (hi : Integrable (fun ξ => m ξ * ((Lp.fourierTransformₗᵢ (Space n) ℂ) f) ξ)) :
    (fun x => OAI.Analysis.Fourier.Wave.fourierMultiplierL2 m f hdom x) =ᵐ[volume]
      𝓕⁻ (fun ξ => m ξ * ((Lp.fourierTransformₗᵢ (Space n) ℂ) f) ξ) := by
  let g : OAI.Analysis.Fourier.Wave.WaveL2 n := hdom.toLp _
  have hcoe : (g : Space n → ℂ) =ᵐ[volume]
      (fun ξ => m ξ * ((Lp.fourierTransformₗᵢ (Space n) ℂ) f) ξ) :=
    hdom.coeFn_toLp
  have hg : Integrable (g : Space n → ℂ) := hi.congr hcoe.symm
  have hInv := OAI.Analysis.Fourier.Wave.inverseFourierL2_coe g hg
  filter_upwards [hInv] with x hx
  change ((Lp.fourierTransformₗᵢ (Space n) ℂ).symm g) x = _
  rw [hx, Real.fourierInv_congr_ae hcoe x]

theorem differentiatedBochnerRieszL2_classical_coe {n : ℕ} (α r : ℝ) (f : OAI.Analysis.Fourier.Wave.WaveL2 n)
    (hdom : MemLp (fun ξ : Space n => (radiusMultiplier α ‖ξ‖ r : ℂ) *
      ((Lp.fourierTransformₗᵢ (Space n) ℂ) f) ξ) 2) :
    (fun x => differentiatedBochnerRieszL2 α r f x) =ᵐ[volume]
      𝓕⁻ (fun ξ : Space n => (radiusMultiplier α ‖ξ‖ r : ℂ) *
        ((Lp.fourierTransformₗᵢ (Space n) ℂ) f) ξ) := by
  simp only [differentiatedBochnerRieszL2, dite_eq_left hdom]
  exact classical_multiplier_coe (n := n) (fun ξ => (radiusMultiplier α ‖ξ‖ r : ℂ))
    f hdom (integrable_radius_symbol (n := n) α r
      ((Lp.fourierTransformₗᵢ (Space n) ℂ) f) hdom)

theorem differentiatedBochnerRieszL2_schwartz_coe {n : ℕ} (α r : ℝ)
    (f : SchwartzMap (Space n) ℂ)
    (hdom : MemLp (fun ξ : Space n => (radiusMultiplier α ‖ξ‖ r : ℂ) *
      ((Lp.fourierTransformₗᵢ (Space n) ℂ) (f.toLp 2)) ξ) 2) :
    (fun x => differentiatedBochnerRieszL2 α r (f.toLp 2) x) =ᵐ[volume]
      radiusDerivativeCycles α r f := by
  let f₂ : OAI.Analysis.Fourier.Wave.WaveL2 n := f.toLp 2 volume
  change MemLp (fun ξ : Space n => (radiusMultiplier α ‖ξ‖ r : ℂ) *
    ((Lp.fourierTransformₗᵢ (Space n) ℂ) f₂) ξ) 2 at hdom
  change (fun x => differentiatedBochnerRieszL2 α r f₂ x) =ᵐ[volume] _
  have hF : (Lp.fourierTransformₗᵢ (Space n) ℂ) f₂ = (𝓕 f).toLp 2 := by
    change 𝓕 (f.toLp 2) = (𝓕 f).toLp 2
    exact SchwartzMap.toLp_fourier_eq f
  have hbase := differentiatedBochnerRieszL2_classical_coe (n := n) α r f₂ hdom
  have hcoe : (fun ξ : Space n => (radiusMultiplier α ‖ξ‖ r : ℂ) *
      ((Lp.fourierTransformₗᵢ (Space n) ℂ) f₂) ξ) =ᵐ[volume]
      (fun ξ => (radiusMultiplier α ‖ξ‖ r : ℂ) * (𝓕 f) ξ) := by
    rw [hF]
    filter_upwards [(𝓕 f).coeFn_toLp 2 volume] with ξ hξ
    rw [hξ]
  filter_upwards [hbase] with x hx
  rw [hx, Real.fourierInv_congr_ae hcoe x]
  rfl

theorem measurable_radiusDerivativeCycles {n : ℕ} (α : ℝ)
    (f : SchwartzMap (Space n) ℂ) :
    Measurable (fun z : ℝ × Space n => radiusDerivativeCycles α z.1 f z.2) := by
  have hm : Measurable (fun z : (ℝ × Space n) × Space n =>
      radiusMultiplier α ‖z.2‖ z.1.1) :=
    (measurable_radiusMultiplier α).comp
      ((continuous_norm.measurable.comp measurable_snd).prodMk
        (measurable_fst.comp measurable_fst))
  have hi : StronglyMeasurable (fun z : (ℝ × Space n) × Space n =>
      Complex.exp ((2 * Real.pi * (inner ℝ z.1.2 z.2) : ℝ) * Complex.I) *
        ((radiusMultiplier α ‖z.2‖ z.1.1 : ℂ) * (𝓕 f) z.2)) := by
    apply Measurable.stronglyMeasurable
    have hf := (𝓕 f).continuous.measurable
    fun_prop
  have h := (hi.integral_prod_right' (ν := (volume : Measure (Space n)))).measurable
  simpa only [radiusDerivativeCycles, Real.fourierInv_eq', smul_eq_mul,
    real_inner_comm] using h

theorem radiusDerivativeCycles_energy {n : ℕ} (α r : ℝ) (hr : 0 < r)
    (f : SchwartzMap (Space n) ℂ)
    (hdom : MemLp (fun ξ : Space n => (radiusMultiplier α ‖ξ‖ r : ℂ) *
      ((Lp.fourierTransformₗᵢ (Space n) ℂ) (f.toLp 2)) ξ) 2) :
    (∫⁻ x : Space n, ‖radiusDerivativeCycles α r f x‖ₑ ^ 2 / ENNReal.ofReal r) =
      ENNReal.ofReal (‖differentiatedBochnerRieszL2 α r (f.toLp 2)‖ ^ 2 / r) := by
  let f₂ : OAI.Analysis.Fourier.Wave.WaveL2 n := f.toLp 2 volume
  let g : OAI.Analysis.Fourier.Wave.WaveL2 n := differentiatedBochnerRieszL2 α r f₂
  have hcoe : (fun x => g x) =ᵐ[volume] radiusDerivativeCycles α r f :=
    differentiatedBochnerRieszL2_schwartz_coe α r f hdom
  have hi : Integrable (fun x => ‖g x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).1 (Lp.memLp g)
  change _ = ENNReal.ofReal (‖g‖ ^ 2 / r)
  rw [OAI.Analysis.Fourier.Wave.waveL2_norm_sq_integral, ← integral_div,
    ofReal_integral_eq_lintegral_ofReal (hi.div_const r)
      (Filter.Eventually.of_forall (fun x => div_nonneg (sq_nonneg _) hr.le))]
  apply lintegral_congr_ae
  filter_upwards [hcoe] with x hx
  rw [← hx, ENNReal.ofReal_div_of_pos hr,
    ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]

theorem radiusDerivativeCycles_ae_energy {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1 / 2 < α) (f : SchwartzMap (Space n) ℂ) :
    ∀ᵐ r ∂volume.restrict (Ioi 0),
      (∫⁻ x : Space n, ‖radiusDerivativeCycles α r f x‖ₑ ^ 2 / ENNReal.ofReal r) =
        ENNReal.ofReal (‖differentiatedBochnerRieszL2 α r (f.toLp 2)‖ ^ 2 / r) := by
  let f₂ : OAI.Analysis.Fourier.Wave.WaveL2 n := f.toLp 2 volume
  have hdom := ae_memLp_radius_symbol hα f₂
  filter_upwards [hdom, ae_restrict_mem measurableSet_Ioi] with r hr hpos
  exact radiusDerivativeCycles_energy α r hpos f hr

private theorem complex_energy_comm {n : ℕ}
    (G : ℝ × Space n → ℂ) (hG : Measurable G) :
    (∫⁻ x : Space n, ∫⁻ r in Ioi 0,
      ‖G (r, x)‖ₑ ^ 2 / ENNReal.ofReal r) =
    (∫⁻ r in Ioi 0, ∫⁻ x : Space n,
      ‖G (r, x)‖ₑ ^ 2 / ENNReal.ofReal r) := by
  have hm : Measurable (fun z : ℝ × Space n =>
      ‖G z‖ₑ ^ 2 / ENNReal.ofReal z.1) := by
    exact (hG.enorm.pow_const (2 : ℕ)).div
      (ENNReal.measurable_ofReal.comp measurable_fst)
  have hm' : Measurable (fun z : Space n × ℝ =>
      ‖G (z.2, z.1)‖ₑ ^ 2 / ENNReal.ofReal z.2) :=
    hm.comp measurable_swap
  exact lintegral_lintegral_swap (μ := (volume : Measure (Space n)))
    (ν := volume.restrict (Ioi 0))
    (f := fun x r => ‖G (r, x)‖ₑ ^ 2 / ENNReal.ofReal r) hm'.aemeasurable

theorem radiusDerivativeCycles_energy_comm {n : ℕ} (α : ℝ)
    (f : SchwartzMap (Space n) ℂ) :
    (∫⁻ x : Space n, ∫⁻ r in Ioi 0,
      ‖radiusDerivativeCycles α r f x‖ₑ ^ 2 / ENNReal.ofReal r) =
    (∫⁻ r in Ioi 0, ∫⁻ x : Space n,
      ‖radiusDerivativeCycles α r f x‖ₑ ^ 2 / ENNReal.ofReal r) :=
  complex_energy_comm (fun z => radiusDerivativeCycles α z.1 f z.2)
    (measurable_radiusDerivativeCycles α f)

/-- Tonelli and Plancherel compute the classical, pointwise square-function energy. -/
theorem radiusDerivativeCycles_total_energy {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1 / 2 < α) (f : SchwartzMap (Space n) ℂ) :
    (∫⁻ x : Space n, ∫⁻ r in Ioi 0,
      ‖radiusDerivativeCycles α r f x‖ₑ ^ 2 / ENNReal.ofReal r) =
      ENNReal.ofReal (α / (2 * α - 1) * ‖f.toLp 2 volume‖ ^ 2) := by
  rw [radiusDerivativeCycles_energy_comm]
  have h := radiusDerivativeCycles_ae_energy hα f
  generalize hf₂ : f.toLp 2 volume = f₂ at h ⊢
  exact (lintegral_congr_ae h).trans (stein_square_function_L2 hα f₂)

end OAI.Analysis.Fourier.SquareFunction
