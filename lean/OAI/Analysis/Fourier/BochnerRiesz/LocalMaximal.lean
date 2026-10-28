import OAI.Analysis.Fourier.BochnerRiesz.Shell.Maximal
import OAI.Analysis.Fourier.BochnerRiesz.Projection

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

def dilatedShellCycles {n : ℕ} (φ : SchwartzMap ℝ ℂ) (Λ ρ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) : ℂ :=
  𝓕⁻ (fun ξ : Space n ↦ φ (Λ - ρ * ‖ξ‖) * (𝓕 f : SchwartzMap (Space n) ℂ) ξ) x

theorem dilatedShellCycles_eq_thinShellCycles {n : ℕ} (φ : SchwartzMap ℝ ℂ)
    (Λ : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    dilatedShellCycles φ Λ ρ f x = OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ (1 / ρ) f x (Λ / ρ) := by
  unfold dilatedShellCycles OAI.Analysis.Fourier.SquareFunction.thinShellCycles
  apply Real.fourierInv_congr_ae
  filter_upwards [] with ξ
  have h : (Λ / ρ - ‖ξ‖) / (1 / ρ) = Λ - ρ * ‖ξ‖ := by field_simp
  rw [h]

def dyadicShellMax {n : ℕ} (φ : SchwartzMap ℝ ℂ) (Λ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) : ℝ≥0∞ :=
  ⨆ ρ : Icc (1 : ℝ) 2, ‖dilatedShellCycles φ Λ ρ.val f x‖ₑ

theorem measurable_dyadicShellMax {n : ℕ} (φ : SchwartzMap ℝ ℂ) (Λ : ℝ)
    (f : SchwartzMap (Space n) ℂ) : Measurable (dyadicShellMax φ Λ f) := by
  apply LowerSemicontinuous.measurable
  apply lowerSemicontinuous_iSup
  intro ρ
  have hρ : ρ.val ≠ 0 := by linarith [ρ.property.1]
  have he : dilatedShellCycles φ Λ ρ.val f =
      fun x ↦ OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ (1 / ρ.val) f x (Λ / ρ.val) :=
    funext (dilatedShellCycles_eq_thinShellCycles φ Λ hρ f)
  rw [he]
  exact (continuous_thinShellCycles_space φ (1 / ρ.val) f (Λ / ρ.val)).enorm.lowerSemicontinuous

theorem dyadicShellMax_le_localThinShellMax {n : ℕ} (φ : SchwartzMap ℝ ℂ) (Λ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    dyadicShellMax φ Λ f x ≤ localThinShellMax φ f x := by
  apply iSup_le
  intro ρ
  have hρ : 0 < ρ.val := by linarith [ρ.property.1]
  have hi : 1 / ρ.val ∈ Icc (1 / 2 : ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ hρ).mpr
      linarith [ρ.property.2]
    · apply (div_le_iff₀ hρ).mpr
      linarith [ρ.property.1]
  rw [dilatedShellCycles_eq_thinShellCycles φ Λ hρ.ne']
  exact le_iSup_of_le (Λ / ρ.val) (le_iSup_of_le ⟨1 / ρ.val, hi⟩ le_rfl)

theorem dilatedShellCycles_annularProject {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) {h : ℝ} (hh : 0 < h)
    (φ : SchwartzMap ℝ ℂ) (Λ ρ : ℝ) (f : SchwartzMap (Space n) ℂ)
    (hcut : ∀ ξ : Space n, φ (Λ - ρ * ‖ξ‖) ≠ 0 → χ (h • ((2 * Real.pi) • ξ)) = 1)
    (x : Space n) :
    dilatedShellCycles φ Λ ρ (annularProject χ h f) x = dilatedShellCycles φ Λ ρ f x := by
  unfold dilatedShellCycles
  apply Real.fourierInv_congr_ae
  exact Filter.Eventually.of_forall fun ξ ↦ by
    dsimp only
    rw [fourier_annularProject hχ hc hh f]
    by_cases hz : φ (Λ - ρ * ‖ξ‖) = 0
    · simp only [hz, zero_mul]
    · rw [hcut ξ hz, one_mul]

theorem localSmoothing_dyadicShellMax (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {χ ψ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hzero : (0 : Space n) ∉ tsupport ψ) (hcover : ∀ ξ, χ ξ ≠ 0 → ψ ξ = 1)
    (φ : SchwartzMap ℝ ℂ) {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ Λ : ℝ,
      (∀ ρ ∈ Icc (1 : ℝ) 2, ∀ ξ : Space n,
        φ (Λ - ρ * ‖ξ‖) ≠ 0 → χ (h • ((2 * Real.pi) • ξ)) = 1) →
      ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (dyadicShellMax φ Λ f) (ENNReal.ofReal p) volume ∧
      eLpNorm (dyadicShellMax φ Λ f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * h ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨A, hA, hmax⟩ := localSmoothing_localThinShellMax hls hn hψ hcψ hzero φ hp hε
  obtain ⟨B, hB, hproj⟩ := annularProject_uniform_bound hχ hcχ
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  intro h hh hhone Λ hcut f
  have he : dyadicShellMax φ Λ (annularProject χ h f) = dyadicShellMax φ Λ f := by
    funext x
    unfold dyadicShellMax
    apply iSup_congr
    intro ρ
    rw [dilatedShellCycles_annularProject hχ hcχ hh φ Λ ρ.val f (hcut ρ.val ρ.property)]
  have hupper := eLpNorm_mono_enorm (measurable_dyadicShellMax φ Λ (annularProject χ h f)).aestronglyMeasurable
    (p := ENNReal.ofReal p) (μ := volume) (g := localThinShellMax φ (annularProject χ h f))
    (fun x ↦ by simpa only [enorm_eq_self] using dyadicShellMax_le_localThinShellMax φ Λ (annularProject χ h f) x)
  rw [he] at hupper
  have HM := (hmax h hh hhone (annularProject χ h f)
    (annularProject_support_cutoff hχ hcχ hh f hcover)).2
  have hp1 : 1 ≤ ENNReal.ofReal p := by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have HQ := hproj h hh f (ENNReal.ofReal p) hp1 ENNReal.ofReal_ne_top
  have H : eLpNorm (dyadicShellMax φ Λ f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (A * B * h ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) * eLpNorm f (ENNReal.ofReal p) volume := by
    calc
      _ ≤ ENNReal.ofReal (A * h ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) *
          (ENNReal.ofReal B * eLpNorm f (ENNReal.ofReal p) volume) :=
        hupper.trans (HM.trans (mul_le_mul' le_rfl HQ))
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring
  exact ⟨H.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (f.memLp _ volume).eLpNorm_lt_top), H⟩

end OAI.Analysis.Fourier.BochnerRiesz
