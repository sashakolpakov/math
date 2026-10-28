import OAI.Analysis.Fourier.Estimates
import OAI.Analysis.Fourier.Wave.Multiplier
import OAI.Analysis.Fourier.Wave.AngularTransform
import OAI.Analysis.Fourier.Wave.Compatibility

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open FourierTransform
open scoped ENNReal

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem bochnerRieszSymbol_nonneg {n : ℕ} (δ R : ℝ) (ξ : Space n) :
    0 ≤ OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ R ξ :=
  Real.rpow_nonneg (le_max_right _ _) _

theorem bochnerRieszSymbol_le_one {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (R : ℝ) (ξ : Space n) : OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ R ξ ≤ 1 := by
  apply Real.rpow_le_one (le_max_right _ _) _ hδ
  exact max_le (by nlinarith [sq_nonneg (‖ξ‖ / R)]) zero_le_one

theorem continuous_bochnerRieszSymbol {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (R : ℝ) : Continuous (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol (n := n) δ R) := by
  unfold OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol
  exact (Real.continuous_rpow_const hδ).comp (by fun_prop)

/-- The angular-frequency symbol in the cycles-frequency coordinate used by mathlib. -/
def bochnerRieszCyclesSymbol {n : ℕ} (δ R : ℝ) (ξ : Space n) : ℂ :=
  OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ R ((2 * Real.pi) • ξ)

theorem measurable_bochnerRieszCyclesSymbol {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (R : ℝ) : AEStronglyMeasurable (bochnerRieszCyclesSymbol (n := n) δ R) volume := by
  apply Continuous.aestronglyMeasurable
  exact Complex.continuous_ofReal.comp
    ((continuous_bochnerRieszSymbol hδ R).comp (by fun_prop))

theorem norm_bochnerRieszCyclesSymbol_le {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (R : ℝ) (ξ : Space n) : ‖bochnerRieszCyclesSymbol δ R ξ‖ ≤ 1 := by
  rw [bochnerRieszCyclesSymbol, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (bochnerRieszSymbol_nonneg _ _ _)]
  exact bochnerRieszSymbol_le_one hδ _ _

def bochnerRieszL2 {n : ℕ} (δ R : ℝ) (hδ : 0 ≤ δ) (f : OAI.Analysis.Fourier.Wave.WaveL2 n) : OAI.Analysis.Fourier.Wave.WaveL2 n :=
  OAI.Analysis.Fourier.Wave.fourierMultiplierL2 (bochnerRieszCyclesSymbol δ R) f
    (OAI.Analysis.Fourier.Wave.memLp_mul_bounded_symbol _ (measurable_bochnerRieszCyclesSymbol hδ R) 1
      (Filter.Eventually.of_forall (norm_bochnerRieszCyclesSymbol_le hδ R))
      ((Lp.fourierTransformₗᵢ (Space n) ℂ) f))

/-- Uniform `L²` Bochner--Riesz bound, including every positive order.
No local-smoothing hypothesis is needed for this case. -/
theorem norm_bochnerRieszL2_le {n : ℕ} (δ R : ℝ) (hδ : 0 ≤ δ) (f : OAI.Analysis.Fourier.Wave.WaveL2 n) :
    ‖bochnerRieszL2 δ R hδ f‖ ≤ ‖f‖ := by
  simpa only [bochnerRieszL2, one_mul] using OAI.Analysis.Fourier.Wave.norm_fourierMultiplierL2_le
    (bochnerRieszCyclesSymbol δ R) f (measurable_bochnerRieszCyclesSymbol hδ R)
    1 zero_le_one (Filter.Eventually.of_forall (norm_bochnerRieszCyclesSymbol_le hδ R))

theorem bochnerRiesz_eq_fourierInv {n : ℕ} (δ R : ℝ) (f : Space n → ℂ) :
    OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f =
      𝓕⁻ (fun ξ ↦ bochnerRieszCyclesSymbol δ R ξ * 𝓕 f ξ) := by
  funext x
  rw [OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz, OAI.Analysis.Fourier.Wave.angularInverse_eq_fourierInv_scaled]
  apply congrArg (fun g : Space n → ℂ ↦ 𝓕⁻ g x)
  funext ξ
  simp only [OAI.Analysis.Fourier.Wave.angularFourier_scaled, bochnerRieszCyclesSymbol, Complex.real_smul]

theorem integrable_bochnerRieszSymbol_mul {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (R : ℝ) (g : Space n → ℂ) (hg : Integrable g) :
    Integrable (fun ξ ↦ bochnerRieszCyclesSymbol δ R ξ * g ξ) := by
  apply hg.norm.mono'
  · exact (measurable_bochnerRieszCyclesSymbol hδ R).mul hg.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ξ ↦ by
      simpa only [norm_mul, one_mul] using
        mul_le_mul_of_nonneg_right (norm_bochnerRieszCyclesSymbol_le hδ R ξ) (norm_nonneg (g ξ))

/-- The `L²` realization agrees with the exact angular-frequency integral on
Schwartz functions. This checks the normalization as well as the domain. -/
theorem bochnerRieszL2_schwartz_coe {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (R : ℝ) (f : SchwartzMap (Space n) ℂ) :
    (fun x ↦ bochnerRieszL2 δ R hδ (f.toLp 2) x) =ᵐ[volume] OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f := by
  have hF : (Lp.fourierTransformₗᵢ (Space n) ℂ) (f.toLp 2) = (𝓕 f).toLp 2 := by
    change 𝓕 (f.toLp 2) = (𝓕 f).toLp 2
    exact SchwartzMap.toLp_fourier_eq f
  let hm := OAI.Analysis.Fourier.Wave.memLp_mul_bounded_symbol (bochnerRieszCyclesSymbol δ R)
    (measurable_bochnerRieszCyclesSymbol hδ R) 1
    (Filter.Eventually.of_forall (norm_bochnerRieszCyclesSymbol_le hδ R))
    ((Lp.fourierTransformₗᵢ (Space n) ℂ) (f.toLp 2))
  let g : OAI.Analysis.Fourier.Wave.WaveL2 n := hm.toLp _
  have hcoe : (g : Space n → ℂ) =ᵐ[volume]
      fun ξ ↦ bochnerRieszCyclesSymbol δ R ξ * (𝓕 f) ξ := by
    filter_upwards [hm.coeFn_toLp, (𝓕 f).coeFn_toLp 2 volume] with ξ h₁ h₂
    dsimp only [g]
    rw [h₁, hF, h₂]
  have hg : Integrable (g : Space n → ℂ) :=
    (integrable_bochnerRieszSymbol_mul hδ R (⇑(𝓕 f : SchwartzMap (Space n) ℂ))
      (𝓕 f).integrable).congr hcoe.symm
  have hInv := OAI.Analysis.Fourier.Wave.inverseFourierL2_coe g hg
  have heq : bochnerRieszL2 δ R hδ (f.toLp 2) =
      (Lp.fourierTransformₗᵢ (Space n) ℂ).symm g := rfl
  rw [heq, bochnerRiesz_eq_fourierInv]
  filter_upwards [hInv] with x hx
  rw [hx, Real.fourierInv_congr_ae hcoe x]
  simp only [SchwartzMap.fourier_coe]

/-- Uniform Bochner--Riesz bound at exponent two for the actual integral
operator, with constant exactly one and no local-smoothing assumption. -/
theorem bochnerRiesz_L2 {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (R : ℝ)
    (f : SchwartzMap (Space n) ℂ) :
    MemLp (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) 2 ∧
    eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) 2 volume ≤ eLpNorm f 2 volume := by
  let u : OAI.Analysis.Fourier.Wave.WaveL2 n := bochnerRieszL2 δ R hδ (f.toLp 2 volume)
  have hcoe : (u : Space n → ℂ) =ᵐ[volume] OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f :=
    bochnerRieszL2_schwartz_coe (n := n) (δ := δ) hδ R f
  constructor
  · have hmem : MemLp (u : Space n → ℂ) 2 := Lp.memLp u
    exact hmem.ae_eq hcoe
  · have hnorm : ‖u‖ ≤ ‖(f.toLp 2 volume : OAI.Analysis.Fourier.Wave.WaveL2 n)‖ := by
      exact norm_bochnerRieszL2_le (n := n) δ R hδ (f.toLp 2 volume)
    have henorm := ENNReal.ofReal_le_ofReal hnorm
    rw [ofReal_norm, ofReal_norm, Lp.enorm_def, Lp.enorm_def] at henorm
    rw [← eLpNorm_congr_ae hcoe]
    exact henorm.trans_eq (eLpNorm_congr_ae (f.coeFn_toLp 2 volume))

theorem enorm_bochnerRiesz_le_maximal {n : ℕ} (δ : ℝ) {R : ℝ} (hR : 0 < R)
    (f : Space n → ℂ) (x : Space n) :
    ‖OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x‖ₑ ≤ OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszMaximal δ f x :=
  le_iSup_of_le R (le_iSup_of_le hR le_rfl)

/-- The uniform bound follows from its maximal version with the same constant.
Only the ordinary measurability of the fixed-radius Fourier integral is required. -/
theorem bochnerRiesz_bound_of_maximal {n : ℕ} {p : ℝ≥0∞} {δ R C : ℝ}
    (hR : 0 < R) (f : Space n → ℂ)
    (hf : AEStronglyMeasurable (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) volume)
    (hmax : MemLp (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszMaximal δ f) p)
    (hbound : eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszMaximal δ f) p volume ≤
      ENNReal.ofReal C * eLpNorm f p volume) :
    MemLp (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) p ∧
    eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) p volume ≤ ENNReal.ofReal C * eLpNorm f p volume := by
  have hdom : ∀ᵐ x ∂volume,
      ‖OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x‖ₑ ≤ ‖OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszMaximal δ f x‖ₑ :=
    Filter.Eventually.of_forall (enorm_bochnerRiesz_le_maximal δ hR f)
  exact ⟨hmax.of_le_enorm hf hdom, (eLpNorm_mono_enorm_ae hf hdom).trans hbound⟩

theorem bochnerRieszIndex_of_two_le {n : ℕ} {p : ℝ} (hp : 2 ≤ p) :
    OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex n (ENNReal.ofReal p) = OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p := by
  have hp0 : 0 < p := by linarith
  have hinv : 1 / p ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num) hp
  unfold OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hp0.le]
  rw [← one_div p]
  rw [abs_of_nonpos (sub_nonpos.mpr hinv)]
  have heq : (n : ℝ) * -(1 / p - 1 / 2) - 1 / 2 = ((n : ℝ) - 1) / 2 - n / p := by ring
  rw [heq, max_comm]

/-- The maximal conjecture supplies every uniform Bochner--Riesz estimate
at finite exponents at least two. Measurability is proved through the `L²`
realization; it is not an extra hypothesis in this implication. -/
theorem maximalBochnerRiesz_implies_uniform_ge_two (hmax : OAI.Analysis.Fourier.BochnerRiesz.MaximalBochnerRieszConjecture)
    (n : ℕ) (hn : 2 ≤ n) (p δ : ℝ) (hp : 2 ≤ p) (hδ : OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) (ENNReal.ofReal p) ∧
      eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hCf⟩ := hmax n hn p δ hp hδ
  refine ⟨C, hC, fun R hR f ↦ ?_⟩
  have hδ0 : 0 ≤ δ := (le_max_left 0 _).trans hδ.le
  have hm := (bochnerRiesz_L2 hδ0 R f).1.aestronglyMeasurable
  exact bochnerRiesz_bound_of_maximal hR f hm (hCf f).1 (hCf f).2

end OAI.Analysis.Fourier.BochnerRiesz
