import OAI.Analysis.Fourier.SquareFunction.Shell.Combining
import OAI.Analysis.Fourier.SquareFunction.CountableSquare
import OAI.Analysis.Fourier.SquareFunction.PowerWindow
import OAI.Analysis.Fourier.WavePackets.ShellHilbertDecay

open OAI.Analysis.Fourier.Wave

/-! The all-dyadic thin-shell square estimate obtained from local smoothing.
The kernel estimates, scalar operator bounds, and Littlewood--Paley input
estimate are all proved for the actual operators. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff

noncomputable def dyadicThinShellHilbert {n : ℕ} (χ : Space n → ℂ)
    (hχ : Continuous χ) (φ : SchwartzMap ℝ ℂ) (δ : ℝ) (f : Space n → ℂ)
    (k : ℤ) : Space n → RadiusHilbert :=
  convolveKernel (dilatedKernel (thinShellKernel χ hχ φ δ) ((2 : ℝ) ^ k)) f

noncomputable def dyadicThinShellSquare {n : ℕ} (χ : Space n → ℂ)
    (hχ : Continuous χ) (φ : SchwartzMap ℝ ℂ) (δ : ℝ) (f : Space n → ℂ) :
    Space n → ℝ≥0∞ :=
  countableSquareNorm (dyadicThinShellHilbert χ hχ φ δ f)

theorem localSmoothing_dyadicThinShellSquare (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n N : ℕ} (hn : 2 ≤ n) {χ ψ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hzχ : (0 : Space n) ∉ tsupport χ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hzψ : (0 : Space n) ∉ tsupport ψ)
    (hcut : ∀ ξ, χ ξ ≠ 0 → ψ ξ = 1)
    (hband : ∀ ξ, ψ ξ ≠ 0 →
      (2 : ℝ) ^ (-(N : ℤ)) ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (2 : ℝ) ^ (N : ℤ))
    (φ : SchwartzMap ℝ ℂ) {p ε : ℝ} (hp : 2 < p) (hε : 0 < ε) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (dyadicThinShellSquare χ hχ.continuous φ δ f) (ENNReal.ofReal p) volume ≤
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
    OAI.Analysis.Fourier.WavePackets.thinShellKernel_polynomial_decay hχ hcχ hzχ φ (n + 2)
  obtain ⟨A, hA, hcombine⟩ := combining_thinShellKernel_family hχ hcχ hψ hcψ hcut hband φ hp
  obtain ⟨P, hP, hop⟩ := localSmoothing_thinShellKernel_integrable hls hn
    hχ hcχ hψ hcψ hzψ hcut φ hp.le hε
  let B := eLpNorm φ 2 volume * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse χ) 1 volume
  have hB : B ≠ ⊤ := ENNReal.mul_ne_top (φ.memLp 2).ne
    (memLp_one_iff_integrable.mpr (OAI.Analysis.Fourier.BochnerRiesz.integrable_angularInverse_cutoff hχ hcχ)).ne
  let E := ENNReal.ofReal C + ENNReal.ofReal ((Q : ℝ) + 1) ^ (1 / 2 - 1 / p) * P + B
  let D := (combiningLogConstant n p ((n : ℝ) + 2) * E) * ENNReal.ofReal A
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
  have hkernel (x : Space n) : ‖thinShellKernel χ hχ.continuous φ δ x‖ ≤
      (C * τ ^ (-((n : ℝ) + 2))) * (‖x‖ + 1) ^ (-((n : ℝ) + 2)) := by
    have hd := (hdecay δ hδ hδone x).1
    simp only [Nat.cast_add, Nat.cast_ofNat] at hd
    rw [add_comm 1 ‖x‖] at hd
    exact hd.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (power_window_decay_nat (Q := Q) hδ hδone hqone) hC.le)
      (Real.rpow_nonneg (by positivity : 0 ≤ ‖x‖ + 1) _))
  have hderiv (x : Space n) : ‖fderiv ℝ (thinShellKernel χ hχ.continuous φ δ) x‖ ≤
      (C * τ ^ (-((n : ℝ) + 2))) * (‖x‖ + 1) ^ (-((n : ℝ) + 2)) := by
    have hd := (hdecay δ hδ hδone x).2
    simp only [Nat.cast_add, Nat.cast_ofNat] at hd
    rw [add_comm 1 ‖x‖] at hd
    exact hd.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (power_window_decay_nat (Q := Q) hδ hδone hqone) hC.le)
      (Real.rpow_nonneg (by positivity : 0 ≤ ‖x‖ + 1) _))
  have hkd := differentiable_thinShellKernel χ hχ.continuous hcχ φ δ
  have hki : Integrable (thinShellKernel χ hχ.continuous φ δ) := by
    apply integrable_of_polynomial_decay (a := 1) (C := C * τ ^ (-((n : ℝ) + 2)))
      (by norm_num) (show (n : ℝ) < (n : ℝ) + 2 by linarith) hkd.continuous.aestronglyMeasurable
    simpa only [one_pow, mul_one, one_mul] using hkernel
  have hmeas (k : ℤ) : Measurable (dyadicThinShellHilbert χ hχ.continuous φ δ f k) := by
    have hdk : Continuous (dilatedKernel (thinShellKernel χ hχ.continuous φ δ) ((2 : ℝ) ^ k)) := by
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
  apply countableSquareNorm_bound _ hmeas (by linarith)
  intro s
  have htwo : ENNReal.ofReal δ ^ (1 / 2 : ℝ) * B ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) hB
  have hb := hcombine s f hq hC.le hτ hτone hkernel hderiv
    (B₂ := ENNReal.ofReal δ ^ (1 / 2 : ℝ) * B)
    (Bₚ := P * ENNReal.ofReal (δ ^ (1 / 2 - (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)))) htwo
    (fun g hg hg2 => thinShellKernel_two_integrable hχ hcχ φ hδ hki hg hg2)
    (hop δ hδ hδone hki)
  have hc := shell_combining_coefficient_le hδ hδone (Nat.cast_nonneg Q) hC.le hσ hθ P B
  refine hb.trans ?_
  calc
    _ ≤ ((combiningLogConstant n p ((n : ℝ) + 2) *
        (E * (ENNReal.ofReal (1 + Real.log (1 / δ)) ^ (1 / 2 - 1 / p) *
          ENNReal.ofReal (δ ^ (1 / 2 - (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)))))) * ENNReal.ofReal A) *
          eLpNorm f (ENNReal.ofReal p) volume :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hc) le_rfl) le_rfl
    _ = _ := by dsimp [D]; ring

end OAI.Analysis.Fourier.SquareFunction
