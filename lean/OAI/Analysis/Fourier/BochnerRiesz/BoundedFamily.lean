import OAI.Analysis.Fourier.BochnerRiesz.FamilyConvergence

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform Set Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz


abbrev PositiveRadius := Ioi (0 : ℝ)

theorem norm_bochnerRiesz_le_fourier_mass {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f : SchwartzMap (Space n) ℂ) (R : ℝ) (x : Space n) :
    ‖OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x‖ ≤ ∫ ξ, ‖(𝓕 f : SchwartzMap (Space n) ℂ) ξ‖ := by
  rw [bochnerRiesz_eq_fourierInv, OAI.Analysis.Fourier.SquareFunction.fourierInv_eq_spatialPhase_smul]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono
    (OAI.Analysis.Fourier.SquareFunction.integrable_spatialPhase_smul x (integrable_bochnerRieszSymbol_mul hδ R _ (𝓕 f).integrable)).norm
    (𝓕 f).integrable.norm
  intro ξ
  dsimp only
  rw [norm_smul, OAI.Analysis.Fourier.SquareFunction.norm_spatialPhase, one_mul, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_bochnerRieszCyclesSymbol_le hδ R ξ)

theorem continuous_bochnerRiesz_positive_radius {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    Continuous (fun R : PositiveRadius => OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x) := by
  apply continuous_iff_continuousAt.mpr
  intro R
  simp only [ContinuousAt, bochnerRiesz_eq_fourierInv, OAI.Analysis.Fourier.SquareFunction.fourierInv_eq_spatialPhase_smul]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun ξ => ‖(𝓕 f : SchwartzMap (Space n) ℂ) ξ‖)
  · exact Eventually.of_forall (fun S => (OAI.Analysis.Fourier.SquareFunction.integrable_spatialPhase_smul x
      (integrable_bochnerRieszSymbol_mul hδ S _ (𝓕 f).integrable)).aestronglyMeasurable)
  · exact Eventually.of_forall (fun S => Eventually.of_forall (fun ξ => by
      rw [norm_smul, OAI.Analysis.Fourier.SquareFunction.norm_spatialPhase, one_mul, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_bochnerRieszCyclesSymbol_le hδ S ξ)))
  · exact (𝓕 f).integrable.norm
  · apply Eventually.of_forall
    intro ξ
    have hc : Continuous (fun S : PositiveRadius => bochnerRieszCyclesSymbol δ S ξ) := by
      unfold bochnerRieszCyclesSymbol OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol
      apply Complex.continuous_ofReal.comp
      apply (Real.continuous_rpow_const hδ).comp
      have hi : Continuous (fun S : PositiveRadius => (S : ℝ)⁻¹) :=
        continuous_subtype_val.inv₀ (fun S => ne_of_gt S.property)
      simp only [div_eq_mul_inv]
      exact (continuous_const.sub ((continuous_const.mul hi).pow 2)).max continuous_const
    exact tendsto_const_nhds.smul (hc.continuousAt.mul tendsto_const_nhds)

def brBoundedFamily {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) : BoundedContinuousFunction PositiveRadius ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun R : PositiveRadius => OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x) (continuous_bochnerRiesz_positive_radius hδ f x)
    (∫ ξ, ‖(𝓕 f : SchwartzMap (Space n) ℂ) ξ‖)
    (fun R => norm_bochnerRiesz_le_fourier_mass hδ f R x)

def brSpatialError {n : ℕ} (f : SchwartzMap (Space n) ℂ) (x y : Space n) : ℝ :=
  ∫ ξ, ‖(OAI.Analysis.Fourier.SquareFunction.spatialPhase x ξ - OAI.Analysis.Fourier.SquareFunction.spatialPhase y ξ) * (𝓕 f : SchwartzMap (Space n) ℂ) ξ‖

theorem brSpatialError_nonneg {n : ℕ} (f : SchwartzMap (Space n) ℂ) (x y : Space n) :
    0 ≤ brSpatialError f x y := integral_nonneg (fun _ => norm_nonneg _)

theorem integrable_brSpatialError_integrand {n : ℕ} (f : SchwartzMap (Space n) ℂ) (x y : Space n) :
    Integrable (fun ξ => (OAI.Analysis.Fourier.SquareFunction.spatialPhase x ξ - OAI.Analysis.Fourier.SquareFunction.spatialPhase y ξ) *
      (𝓕 f : SchwartzMap (Space n) ℂ) ξ) := by
  have H := (OAI.Analysis.Fourier.SquareFunction.integrable_spatialPhase_mul x (𝓕 f).integrable).sub
    (OAI.Analysis.Fourier.SquareFunction.integrable_spatialPhase_mul y (𝓕 f).integrable)
  convert H using 1
  ext ξ
  simp only [Pi.sub_apply, sub_mul]

theorem norm_bochnerRiesz_sub_le_spatialError {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f : SchwartzMap (Space n) ℂ) (R : ℝ) (x y : Space n) :
    ‖OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x - OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f y‖ ≤ brSpatialError f x y := by
  let m : Space n → ℂ := fun ξ => bochnerRieszCyclesSymbol δ R ξ * (𝓕 f : SchwartzMap (Space n) ℂ) ξ
  have hi : Integrable m := integrable_bochnerRieszSymbol_mul hδ R _ (𝓕 f).integrable
  have hx := OAI.Analysis.Fourier.SquareFunction.integrable_spatialPhase_mul x hi
  have hy := OAI.Analysis.Fourier.SquareFunction.integrable_spatialPhase_mul y hi
  have he : OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x - OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f y =
      ∫ ξ, OAI.Analysis.Fourier.SquareFunction.spatialPhase x ξ * m ξ - OAI.Analysis.Fourier.SquareFunction.spatialPhase y ξ * m ξ := by
    rw [integral_sub hx hy]
    simp only [bochnerRiesz_eq_fourierInv, OAI.Analysis.Fourier.SquareFunction.fourierInv_eq_spatialPhase_smul,
      m, smul_eq_mul, SchwartzMap.fourier_coe]
  rw [he]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono (hx.sub hy).norm (integrable_brSpatialError_integrand f x y).norm
  intro ξ
  dsimp only [Pi.sub_apply]
  rw [← sub_mul]
  change ‖(OAI.Analysis.Fourier.SquareFunction.spatialPhase x ξ - OAI.Analysis.Fourier.SquareFunction.spatialPhase y ξ) *
    (bochnerRieszCyclesSymbol δ R ξ * (𝓕 f : SchwartzMap (Space n) ℂ) ξ)‖ ≤ _
  simp only [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_bochnerRieszCyclesSymbol_le hδ R ξ)

theorem tendsto_brSpatialError {n : ℕ} (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    Tendsto (fun y => brSpatialError f y x) (𝓝 x) (𝓝 0) := by
  have H : Tendsto (fun y => ∫ ξ, ‖(OAI.Analysis.Fourier.SquareFunction.spatialPhase y ξ - OAI.Analysis.Fourier.SquareFunction.spatialPhase x ξ) *
      (𝓕 f : SchwartzMap (Space n) ℂ) ξ‖) (𝓝 x) (𝓝 (∫ ξ : Space n, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun ξ => 2 * ‖(𝓕 f : SchwartzMap (Space n) ℂ) ξ‖)
    · exact Eventually.of_forall fun y => (integrable_brSpatialError_integrand f y x).norm.aestronglyMeasurable
    · apply Eventually.of_forall
      intro y
      apply Eventually.of_forall
      intro ξ
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (norm_sub_le _ _).trans_eq (by rw [OAI.Analysis.Fourier.SquareFunction.norm_spatialPhase, OAI.Analysis.Fourier.SquareFunction.norm_spatialPhase]; norm_num)
    · exact (𝓕 f).integrable.norm.const_mul 2
    · apply Eventually.of_forall
      intro ξ
      have hc : Continuous (fun y : Space n => OAI.Analysis.Fourier.SquareFunction.spatialPhase y ξ) := by
        unfold OAI.Analysis.Fourier.SquareFunction.spatialPhase
        fun_prop
      have h := (((hc.continuousAt (x := x)).tendsto.sub
        (tendsto_const_nhds (x := OAI.Analysis.Fourier.SquareFunction.spatialPhase x ξ))).mul
        (tendsto_const_nhds (x := (𝓕 f : SchwartzMap (Space n) ℂ) ξ))).norm
      simpa only [sub_self, zero_mul, norm_zero] using h
  simpa only [brSpatialError, integral_zero] using H

theorem continuous_brBoundedFamily {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f : SchwartzMap (Space n) ℂ) : Continuous (brBoundedFamily hδ f) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun y => dist_nonneg) _ (tendsto_brSpatialError f x)
  intro y
  apply (BoundedContinuousFunction.dist_le (brSpatialError_nonneg f y x)).mpr
  intro R
  change dist (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f y) (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x) ≤ _
  rw [dist_eq_norm]
  exact norm_bochnerRiesz_sub_le_spatialError hδ f R y x

theorem enorm_boundedContinuousFunction_le {X : Type*} [TopologicalSpace X]
    (u : BoundedContinuousFunction X ℂ) {B : ℝ≥0∞} (hb : ∀ x, ‖u x‖ₑ ≤ B) : ‖u‖ₑ ≤ B := by
  by_cases hB : B = ∞
  · simp [hB]
  have hu : ‖u‖ ≤ B.toReal := by
    apply (BoundedContinuousFunction.norm_le ENNReal.toReal_nonneg).mpr
    intro x
    have h := ENNReal.toReal_mono hB (hb x)
    simpa using h
  have h := ENNReal.ofReal_le_ofReal hu
  simpa only [ofReal_norm, ENNReal.ofReal_toReal hB] using h

theorem enorm_brBoundedFamily {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    ‖brBoundedFamily hδ f x‖ₑ = OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszMaximal δ f x := by
  apply le_antisymm
  · apply enorm_boundedContinuousFunction_le
    intro R
    exact le_iSup_of_le R.val (le_iSup_of_le R.property le_rfl)
  · apply iSup_le
    intro R
    apply iSup_le
    intro hR
    change ‖(brBoundedFamily hδ f x) ⟨R, hR⟩‖ₑ ≤ ‖brBoundedFamily hδ f x‖ₑ
    simpa only [ofReal_norm] using
      ENNReal.ofReal_le_ofReal ((brBoundedFamily hδ f x).norm_coe_le_norm ⟨R, hR⟩)

theorem eLpNorm_brBoundedFamily {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f : SchwartzMap (Space n) ℂ) (p : ℝ≥0∞) :
    eLpNorm (brBoundedFamily hδ f) p volume = eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszMaximal δ f) p volume := by
  apply eLpNorm_congr_enorm_ae (continuous_brBoundedFamily hδ f).aestronglyMeasurable
    (OAI.Analysis.Fourier.SquareFunction.measurable_bochnerRieszMaximal hδ f).aestronglyMeasurable
  exact Eventually.of_forall fun x => by rw [enorm_eq_self, enorm_brBoundedFamily]

end OAI.Analysis.Fourier.BochnerRiesz
