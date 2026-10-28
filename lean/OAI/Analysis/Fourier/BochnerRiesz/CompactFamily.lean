import OAI.Analysis.Fourier.SquareFunction.Maximal.BRConvergence
import OAI.Analysis.Fourier.BochnerRiesz.LpExtension
import OAI.Analysis.Fourier.SquareFunction.KernelHilbert

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform Set Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz


/-- Inverse radius, including the limiting radius at infinity. -/
abbrev InverseRadius := Icc (0 : ℝ) 1

def inverseRadiusZero : InverseRadius := ⟨0, by norm_num⟩

def brCompactSymbol {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (ξ : Space n) :
    C(InverseRadius, ℂ) where
  toFun τ := Complex.ofReal ((max (1 - ((τ : ℝ) * ‖(2 * Real.pi) • ξ‖) ^ 2) 0) ^ δ)
  continuous_toFun := Complex.continuous_ofReal.comp
    ((Real.continuous_rpow_const hδ).comp
      ((continuous_const.sub ((continuous_subtype_val.mul continuous_const).pow 2)).max continuous_const))

theorem continuous_brCompactSymbol {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) :
    Continuous (brCompactSymbol (n := n) hδ) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : Space n × InverseRadius =>
    Complex.ofReal ((max (1 - ((z.2 : ℝ) * ‖(2 * Real.pi) • z.1‖) ^ 2) 0) ^ δ))
  apply Complex.continuous_ofReal.comp
  apply (Real.continuous_rpow_const hδ).comp
  fun_prop

theorem norm_brCompactSymbol_le_one {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (ξ : Space n) :
    ‖brCompactSymbol hδ ξ‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).mpr
  intro τ
  change ‖Complex.ofReal ((max (1 - ((τ : ℝ) * ‖(2 * Real.pi) • ξ‖) ^ 2) 0) ^ δ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_max_right _ _) _)]
  apply Real.rpow_le_one (le_max_right _ _) _ hδ
  exact max_le (by nlinarith [sq_nonneg ((τ : ℝ) * ‖(2 * Real.pi) • ξ‖)]) (by norm_num)

def brCompactFrequency {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f : SchwartzMap (Space n) ℂ) (ξ : Space n) : C(InverseRadius, ℂ) :=
  (𝓕 f : SchwartzMap (Space n) ℂ) ξ • brCompactSymbol hδ ξ

theorem integrable_brCompactFrequency {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f : SchwartzMap (Space n) ℂ) : Integrable (brCompactFrequency hδ f) := by
  have hi : Integrable (𝓕 f : SchwartzMap (Space n) ℂ) (volume : Measure (Space n)) :=
    (𝓕 f).integrable
  apply hi.mono
    ((𝓕 f).continuous.smul (continuous_brCompactSymbol hδ)).aestronglyMeasurable
  apply Eventually.of_forall
  intro ξ
  change ‖(𝓕 f : SchwartzMap (Space n) ℂ) ξ • brCompactSymbol hδ ξ‖ ≤ _
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_brCompactSymbol_le_one hδ ξ)

/-- All radii at least one, together with their limit, as one continuous function. -/
def brCompactFamily {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) : C(InverseRadius, ℂ) :=
  𝓕⁻ (brCompactFrequency hδ f) x

theorem continuous_brCompactFamily {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f : SchwartzMap (Space n) ℂ) : Continuous (brCompactFamily hδ f) := by
  have hc : Continuous (𝓕 (brCompactFrequency hδ f)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (integrable_brCompactFrequency hδ f)
  have he : 𝓕⁻ (brCompactFrequency hδ f) =
      fun x : Space n => 𝓕 (brCompactFrequency hδ f) (-x) :=
    funext (Real.fourierInv_eq_fourier_neg _)
  change Continuous (𝓕⁻ (brCompactFrequency hδ f))
  rw [he]
  exact hc.comp continuous_neg

theorem brCompactFamily_apply {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) (τ : InverseRadius) :
    brCompactFamily hδ f x τ =
      𝓕⁻ (fun ξ => (brCompactSymbol hδ ξ τ) * (𝓕 f : SchwartzMap (Space n) ℂ) ξ) x := by
  unfold brCompactFamily
  rw [OAI.Analysis.Fourier.SquareFunction.fourierInv_eq_spatialPhase_smul, OAI.Analysis.Fourier.SquareFunction.fourierInv_eq_spatialPhase_smul,
    ContinuousMap.integral_apply (OAI.Analysis.Fourier.SquareFunction.integrable_spatialPhase_smul x (integrable_brCompactFrequency hδ f))]
  congr 1
  funext ξ
  simp only [brCompactFrequency, ContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem brCompactFamily_zero {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    brCompactFamily hδ f x inverseRadiusZero = f x := by
  rw [brCompactFamily_apply]
  simp only [brCompactSymbol, inverseRadiusZero, ContinuousMap.coe_mk,
    zero_mul, zero_pow (by norm_num : 2 ≠ 0), sub_zero, max_eq_left zero_le_one,
    Real.one_rpow, Complex.ofReal_one, one_mul]
  rw [← SchwartzMap.fourierInv_coe, fourierInv_fourier_eq]

theorem brCompactFamily_pos {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) (τ : InverseRadius) (_ : 0 < (τ : ℝ)) :
    brCompactFamily hδ f x τ = OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ (τ : ℝ)⁻¹ f x := by
  rw [brCompactFamily_apply, bochnerRiesz_eq_fourierInv]
  apply congrArg (fun u : Space n → ℂ => 𝓕⁻ u x)
  funext ξ
  simp only [brCompactSymbol, ContinuousMap.coe_mk, bochnerRieszCyclesSymbol,
    OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol, div_inv_eq_mul, mul_comm (τ : ℝ), SchwartzMap.fourier_coe]

end OAI.Analysis.Fourier.BochnerRiesz
