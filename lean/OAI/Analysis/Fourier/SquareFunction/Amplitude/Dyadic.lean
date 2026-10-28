import OAI.Analysis.Fourier.SquareFunction.Amplitude.OperatorBounds
import OAI.Analysis.Fourier.SquareFunction.Amplitude.Projection
import OAI.Analysis.Fourier.SquareFunction.AnnularCombining
import OAI.Analysis.Fourier.SquareFunction.CountableSquare
import OAI.Analysis.Fourier.SquareFunction.PowerWindow
import OAI.Analysis.Fourier.WavePackets.ShellAmplitudeHilbert

open OAI.Analysis.Fourier.Wave

/-! The all-dyadic square-function estimate with a smooth compact amplitude.
All scalar bounds and quantitative kernel assumptions are discharged. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff

noncomputable def dyadicAmplitudeShellHilbert {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ) (f : Space n → ℂ)
    (k : ℤ) : Space n → RadiusHilbert :=
  convolveKernel (dilatedKernel (amplitudeShellKernel A hA φ δ) ((2 : ℝ) ^ k)) f

noncomputable def dyadicAmplitudeShellSquare {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ) (f : Space n → ℂ) :
    Space n → ℝ≥0∞ :=
  countableSquareNorm (dyadicAmplitudeShellHilbert A hA φ δ f)

theorem localSmoothing_dyadicAmplitudeShellSquare (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n N : ℕ} (hn : 2 ≤ n) {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    (hzA : ∀ r, (r, (0 : Space n)) ∉ tsupport A)
    {χ ψ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hzψ : (0 : Space n) ∉ tsupport ψ)
    (hcut : ∀ ξ, χ ξ ≠ 0 → ψ ξ = 1)
    (hAχ : ∀ r ξ, A (r, ξ) ≠ 0 → χ ((2 * Real.pi) • ξ) = 1)
    (hband : ∀ ξ, ψ ξ ≠ 0 →
      (2 : ℝ) ^ (-(N : ℤ)) ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (2 : ℝ) ^ (N : ℤ))
    (φ : SchwartzMap ℝ ℂ) {p ε : ℝ} (hp : 2 < p) (hε : 0 < ε) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (dyadicAmplitudeShellSquare A hA.continuous φ δ f) (ENNReal.ofReal p) volume ≤
        D * ENNReal.ofReal (1 + Real.log (1 / δ)) ^ (1 / 2 - 1 / p) *
          ENNReal.ofReal (δ ^ (1 / 2 - (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) *
            eLpNorm f (ENNReal.ofReal p) volume := by
  classical
  let : NeZero n := ⟨by omega⟩
  let : MeasurableSpace RadiusHilbert := borel RadiusHilbert
  let : BorelSpace RadiusHilbert := ⟨rfl⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have hθ : 0 ≤ 1 / 2 - 1 / p := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp.le
    linarith
  have hσ : 0 ≤ OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε := by
    have : 0 ≤ OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p := le_max_left _ _
    linarith
  obtain ⟨Q, C, hC, hdecay⟩ :=
    OAI.Analysis.Fourier.WavePackets.amplitudeShellKernel_polynomial_decay hA hcA hzA φ (n + 2)
  obtain ⟨L, hL, hcombine⟩ := combining_annular_kernel_family
    (H := RadiusHilbert) hψ hcψ hband hp
  obtain ⟨P, hP, hop⟩ := localSmoothing_amplitudeShellKernel_integrable hls hn hA hcA
    hχ hcχ hψ hcψ hzψ hcut hAχ φ hp.le hε
  obtain ⟨B, hB, htwo⟩ := amplitudeShellKernel_two_integrable hA hcA φ
  let E := ENNReal.ofReal C + ENNReal.ofReal ((Q : ℝ) + 1) ^ (1 / 2 - 1 / p) * P + B
  let D := (combiningLogConstant n p ((n : ℝ) + 2) * E) * ENNReal.ofReal L
  have hE : E ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hθ ENNReal.ofReal_ne_top) hP⟩, hB⟩
  refine ⟨D, ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (combiningLogConstant_ne_top hp) hE) ENNReal.ofReal_ne_top, ?_⟩
  intro δ hδ hδone f
  let τ := δ ^ ((Q : ℝ) + 1)
  have hτ : 0 < τ := Real.rpow_pos_of_pos hδ _
  have hτone : τ ≤ 1 := (power_window_le hδ hδone (Nat.cast_nonneg Q)).trans hδone
  have hq : (n : ℝ) + 1 < (n : ℝ) + 2 := by linarith
  have hqone : 1 ≤ (n : ℝ) + 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hkernel (x : Space n) : ‖amplitudeShellKernel A hA.continuous φ δ x‖ ≤
      (C * τ ^ (-((n : ℝ) + 2))) * (‖x‖ + 1) ^ (-((n : ℝ) + 2)) := by
    have hd := (hdecay δ hδ hδone x).1
    simp only [Nat.cast_add, Nat.cast_ofNat] at hd
    rw [add_comm 1 ‖x‖] at hd
    exact hd.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (power_window_decay_nat (Q := Q) hδ hδone hqone) hC.le)
      (Real.rpow_nonneg (by positivity : 0 ≤ ‖x‖ + 1) _))
  have hderiv (x : Space n) : ‖fderiv ℝ (amplitudeShellKernel A hA.continuous φ δ) x‖ ≤
      (C * τ ^ (-((n : ℝ) + 2))) * (‖x‖ + 1) ^ (-((n : ℝ) + 2)) := by
    have hd := (hdecay δ hδ hδone x).2
    simp only [Nat.cast_add, Nat.cast_ofNat] at hd
    rw [add_comm 1 ‖x‖] at hd
    exact hd.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (power_window_decay_nat (Q := Q) hδ hδone hqone) hC.le)
      (Real.rpow_nonneg (by positivity : 0 ≤ ‖x‖ + 1) _))
  have hkd := differentiable_amplitudeShellKernel A hA.continuous hcA φ δ
  have hki : Integrable (amplitudeShellKernel A hA.continuous φ δ) := by
    apply integrable_of_polynomial_decay (a := 1) (C := C * τ ^ (-((n : ℝ) + 2)))
      (by norm_num) (show (n : ℝ) < (n : ℝ) + 2 by linarith) hkd.continuous.aestronglyMeasurable
    simpa only [one_pow, mul_one, one_mul] using hkernel
  have hmeas (k : ℤ) : Measurable (dyadicAmplitudeShellHilbert A hA.continuous φ δ f k) := by
    have hdk : Continuous (dilatedKernel (amplitudeShellKernel A hA.continuous φ δ) ((2 : ℝ) ^ k)) := by
      have hs : Continuous (fun x : Space n => ((2 : ℝ) ^ k) • x) :=
        continuous_id.const_smul ((2 : ℝ) ^ k)
      unfold dilatedKernel
      exact (hkd.continuous.comp hs).const_smul ((((2 : ℝ) ^ k) ^ n : ℝ) : ℂ)
    apply Continuous.measurable
    apply continuous_convolveKernel f.integrable hdk
    refine ⟨(C * τ ^ (-((n : ℝ) + 2))) * ((2 : ℝ) ^ k) ^ n, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact bounded_of_polynomial_decay (by positivity) (by positivity)
      (by positivity) (dilatedKernel_decay (by positivity) hkernel) x
  have hAψ : ∀ r ξ, A (r, ξ) ≠ 0 → ψ ((2 * Real.pi) • ξ) = 1 := by
    intro r ξ ha
    exact hcut _ (by rw [hAχ r ξ ha]; exact one_ne_zero)
  apply countableSquareNorm_bound _ hmeas (by linarith)
  intro s
  have htwofinite : ENNReal.ofReal δ ^ (1 / 2 : ℝ) * B ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) hB
  have hb := hcombine (amplitudeShellKernel A hA.continuous φ δ) hkd
    (fun a ha f x => convolve_dilated_amplitudeShellKernel_annularProject
      hA.continuous hcA hψ hcψ hAψ φ δ ha f x)
    s f hq hC.le hτ hτone hkernel hderiv
    (B₂ := ENNReal.ofReal δ ^ (1 / 2 : ℝ) * B)
    (Bₚ := P * ENNReal.ofReal (δ ^ (1 / 2 - (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)))) htwofinite
    (htwo δ hδ hki) (hop δ hδ hδone hki)
  have hc := shell_combining_coefficient_le hδ hδone (Nat.cast_nonneg Q) hC.le hσ hθ P B
  refine hb.trans ?_
  calc
    _ ≤ ((combiningLogConstant n p ((n : ℝ) + 2) *
        (E * (ENNReal.ofReal (1 + Real.log (1 / δ)) ^ (1 / 2 - 1 / p) *
          ENNReal.ofReal (δ ^ (1 / 2 - (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)))))) * ENNReal.ofReal L) *
          eLpNorm f (ENNReal.ofReal p) volume :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hc) le_rfl) le_rfl
    _ = _ := by dsimp [D]; ring

end OAI.Analysis.Fourier.SquareFunction
