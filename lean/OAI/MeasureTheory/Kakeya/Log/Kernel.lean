import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.RadialFormula
import OAI.Analysis.Fourier.Radial.Pieces

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ContDiff RealInnerProductSpace

noncomputable section
namespace OAI.MeasureTheory.Kakeya

def narrowProfile (φ : ℝ → ℝ) (T ρ : ℝ) : ℝ := φ (T * (ρ - 1))

def narrowSymbol (n : ℕ) (φ : ℝ → ℝ) (T : ℝ) (ξ : Space n) : ℂ :=
  ((‖ξ‖ ^ (-OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder n) * narrowProfile φ T ‖ξ‖ : ℝ) : ℂ)

def narrowKernel (n : ℕ) (φ : ℝ → ℝ) (T : ℝ) : Space n → ℂ :=
  OAI.Analysis.Fourier.LocalSmoothing.angularInverse (narrowSymbol n φ T)

theorem narrowProfile_support {φ : ℝ → ℝ}
    (hφ : tsupport φ ⊆ Icc (-(1 / 4)) (1 / 4)) {T : ℝ} (hT : 1 ≤ T) :
    tsupport (narrowProfile φ T) ⊆ Icc (3 / 4) (5 / 4) := by
  apply closure_minimal ?_ isClosed_Icc
  intro ρ hρ
  have h := hφ (subset_tsupport φ hρ)
  change -(1 / 4 : ℝ) ≤ T * (ρ - 1) ∧ T * (ρ - 1) ≤ 1 / 4 at h
  constructor <;> by_contra H
  · have hh : ρ < 3 / 4 := lt_of_not_ge H
    nlinarith [mul_nonneg (sub_nonneg.mpr hT) (show 0 ≤ 1 - ρ by linarith)]
  · have hh : 5 / 4 < ρ := lt_of_not_ge H
    nlinarith [mul_nonneg (sub_nonneg.mpr hT) (show 0 ≤ ρ - 1 by linarith)]

theorem narrowProfile_hasCompactSupport {φ : ℝ → ℝ}
    (hφ : tsupport φ ⊆ Icc (-(1 / 4)) (1 / 4)) {T : ℝ} (hT : 1 ≤ T) :
    HasCompactSupport (narrowProfile φ T) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (narrowProfile_support hφ hT)

theorem narrowSymbol_support {n : ℕ} {φ : ℝ → ℝ}
    (hφ : tsupport φ ⊆ Icc (-(1 / 4)) (1 / 4)) {T : ℝ} (hT : 1 ≤ T) :
    tsupport (narrowSymbol n φ T) ⊆ {ξ | 3 / 4 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 5 / 4} := by
  apply closure_minimal ?_ ((isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const))
  intro ξ hξ
  apply narrowProfile_support hφ hT
  apply subset_tsupport
  intro he
  exact hξ (by simp [narrowSymbol, he])

theorem narrowSymbol_zero_notMem {n : ℕ} {φ : ℝ → ℝ}
    (hφ : tsupport φ ⊆ Icc (-(1 / 4)) (1 / 4)) {T : ℝ} (hT : 1 ≤ T) :
    (0 : Space n) ∉ tsupport (narrowSymbol n φ T) := by
  intro h
  have := (narrowSymbol_support hφ hT h).1
  norm_num at this

theorem narrowSymbol_hasCompactSupport {n : ℕ} {φ : ℝ → ℝ}
    (hφ : tsupport φ ⊆ Icc (-(1 / 4)) (1 / 4)) {T : ℝ} (hT : 1 ≤ T) :
    HasCompactSupport (narrowSymbol n φ T) := by
  apply (isCompact_closedBall (0 : Space n) (5 / 4)).of_isClosed_subset
    (isClosed_tsupport _)
  intro ξ hξ
  simpa only [mem_closedBall, dist_zero_right] using (narrowSymbol_support hφ hT hξ).2

theorem narrowSymbol_contDiff {n : ℕ} {φ : ℝ → ℝ} (hφc : ContDiff ℝ ∞ φ)
    (hφ : tsupport φ ⊆ Icc (-(1 / 4)) (1 / 4)) {T : ℝ} (hT : 1 ≤ T) :
    ContDiff ℝ ∞ (narrowSymbol n φ T) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ξ = 0
  · subst ξ
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp (narrowSymbol_zero_notMem hφ hT))
  · have hn : ContDiffAt ℝ ∞ (fun ξ : Space n ↦ ‖ξ‖) ξ := contDiffAt_id.norm ℝ hξ
    have hp : ContDiffAt ℝ ∞ (fun ξ : Space n ↦ narrowProfile φ T ‖ξ‖) ξ := by
      exact hφc.contDiffAt.comp ξ (contDiffAt_const.mul (hn.sub contDiffAt_const))
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp ξ
      ((hn.rpow_const_of_ne (norm_ne_zero_iff.mpr hξ)).mul hp)

/-- The polar formula for a continuous compact radial multiplier. -/
theorem angularInverse_radial_integral {n : ℕ} (hn : 1 ≤ n) {g : ℝ → ℂ}
    (hg : Continuous (fun ξ : Space n ↦ g ‖ξ‖))
    (hc : HasCompactSupport (fun ξ : Space n ↦ g ‖ξ‖))
    (hzero : ∀ ρ, ρ ≤ 0 → g ρ = 0) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ : Space n ↦ g ‖ξ‖) x =
      (((2 * Real.pi) ^ n)⁻¹ : ℝ) •
        ∫ ρ : ℝ, (ρ ^ (n - 1) : ℝ) •
          (g ρ * OAI.Analysis.Fourier.Restriction.sphericalExtension (fun _ : Space n ↦ (1 : ℂ)) (ρ • x)) := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.angularInverse
  congr 1
  let F : Space n → ℂ := fun ξ ↦
    Complex.exp (Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) * g ‖ξ‖
  have hFc : Continuous F := by
    exact (by fun_prop : Continuous (fun ξ : Space n ↦
      Complex.exp (Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)))).mul hg
  rw [OAI.Analysis.Fourier.LocalSmoothing.Sharpness.integral_polar_sphereMeasure hn hFc
    (hFc.integrable_of_hasCompactSupport hc.mul_left)]
  have hi (ρ : ℝ) (hρ : 0 < ρ) :
      (∫ z : Space n, F (ρ • z) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) =
        g ρ * OAI.Analysis.Fourier.Restriction.sphericalExtension (fun _ : Space n ↦ (1 : ℂ)) (ρ • x) := by
    unfold OAI.Analysis.Fourier.Restriction.sphericalExtension
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_sphereMeasure_norm n] with z hz
    have he : ‖ρ • z‖ = ρ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ, hz, mul_one]
    dsimp [F]
    rw [he, inner_smul_right, real_inner_smul_left]
    ring
  calc
    _ = ∫ ρ in Ioi (0 : ℝ), (ρ ^ (n - 1) : ℝ) •
        (g ρ * OAI.Analysis.Fourier.Restriction.sphericalExtension (fun _ : Space n ↦ (1 : ℂ)) (ρ • x)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro ρ hρ
      dsimp only
      rw [hi ρ hρ]
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro ρ hρ
      simp [hzero ρ (le_of_not_gt hρ)]

theorem narrowKernel_polar {n : ℕ} (hn : 1 ≤ n) {φ : ℝ → ℝ}
    (hφc : ContDiff ℝ ∞ φ) (hφ : tsupport φ ⊆ Icc (-(1 / 4)) (1 / 4))
    {T : ℝ} (hT : 1 ≤ T) (x : Space n) :
    narrowKernel n φ T x = (((2 * Real.pi) ^ n)⁻¹ : ℝ) •
      ∫ ρ : ℝ, ((ρ ^ OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder n * narrowProfile φ T ρ : ℝ) : ℂ) *
        OAI.Analysis.Fourier.Restriction.sphericalExtension (fun _ : Space n ↦ (1 : ℂ)) (ρ • x) := by
  have hz (ρ : ℝ) (hρ : ρ ≤ 0) : narrowProfile φ T ρ = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro H
    have := (narrowProfile_support hφ hT H).1
    linarith
  have h := angularInverse_radial_integral hn (narrowSymbol_contDiff hφc hφ hT).continuous
    (narrowSymbol_hasCompactSupport hφ hT)
    (g := fun ρ ↦ ((ρ ^ (-OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder n) * narrowProfile φ T ρ : ℝ) : ℂ))
    (fun ρ hρ ↦ by simp [hz ρ hρ]) x
  change narrowKernel n φ T x = _ at h
  rw [h]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ρ
  by_cases he : narrowProfile φ T ρ = 0
  · simp [he]
  · have hρ : 0 < ρ := by
      have := (narrowProfile_support hφ hT (subset_tsupport _ he)).1
      linarith
    have hpower : ρ ^ (n - 1) * ρ ^ (-OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder n) =
        ρ ^ OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder n := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hρ]
      congr 1
      rw [Nat.cast_sub hn]
      simp only [OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder, Nat.cast_one]
      ring
    simp only [Complex.real_smul, Complex.ofReal_mul]
    rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, hpower]

end OAI.MeasureTheory.Kakeya
