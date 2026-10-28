import OAI.Analysis.Fourier.SquareFunction.Amplitude.Profile
import OAI.Analysis.Fourier.SquareFunction.BoundaryWeights
import OAI.Analysis.Fourier.SquareFunction.BoundaryPartition
import OAI.Analysis.Fourier.SquareFunction.Cutoff

open OAI.Analysis.Fourier.Wave

/-! Summation of all singular boundary shells at the strict Stein index. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff

noncomputable def boundaryShellEnvelope {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (α : ℝ) (J : ℕ) (f : SchwartzMap (Space n) ℂ)
    (x : Space n) : ℝ≥0∞ :=
  ∑' j : ℕ, ENNReal.ofReal (dyadicShellWidth J j ^ (α - 1)) *
    dyadicAmplitudeShellSquare A hA (OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile (α - 1))
      (dyadicShellWidth J j) f x

theorem localSmoothing_boundaryShellEnvelope (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    (hzA : ∀ r, (r, (0 : Space n)) ∉ tsupport A)
    (hband : ∀ r ξ, A (r, ξ) ≠ 0 → 1 / 4 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 3)
    {p α : ℝ} (hp : 2 < p) (hα : 1 / 2 + OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p < α) (J : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (boundaryShellEnvelope A hA.continuous α J f) (ENNReal.ofReal p) volume ≤
        C * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨χ, ψ, hχ, hcχ, hψ, hcψ, hzψ, hχone, hχψ, hψband⟩ :=
    exists_stein_boundary_cutoffs n
  have hAχ : ∀ r ξ, A (r, ξ) ≠ 0 → χ ((2 * Real.pi) • ξ) = 1 := by
    intro r ξ ha
    exact hχone ξ (hband r ξ ha).1 (hband r ξ ha).2
  let ε := (α - 1 / 2 - OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  let d := α - 1 / 2 - (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)
  have hd : 0 < d := by dsimp [d, ε]; linarith
  let θ := 1 / 2 - 1 / p
  have hθ : 0 ≤ θ := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp.le
    dsimp [θ]
    linarith
  obtain ⟨D, hD, hb⟩ := localSmoothing_dyadicAmplitudeShellSquare hls hn hA hcA hzA
    hχ hcχ hψ hcψ hzψ hχψ hAχ hψband (OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile (α - 1)) hp hε
  let w := fun j : ℕ => dyadicShellWidth J j ^ d *
    (1 + Real.log (1 / dyadicShellWidth J j)) ^ θ
  have hw : Summable w := summable_dyadicShellWidth_log hd hθ J
  let W := ∑' j, ENNReal.ofReal (w j)
  have hW : W ≠ ⊤ := hw.tsum_ofReal_lt_top.ne
  refine ⟨D * W, ENNReal.mul_ne_top hD hW, fun f => ?_⟩
  have hj (j : ℕ) : eLpNorm (fun x => ENNReal.ofReal (dyadicShellWidth J j ^ (α - 1)) *
      dyadicAmplitudeShellSquare A hA.continuous (OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile (α - 1))
        (dyadicShellWidth J j) f x) (ENNReal.ofReal p) volume ≤
      D * ENNReal.ofReal (w j) * eLpNorm f (ENNReal.ofReal p) volume := by
    let δ := dyadicShellWidth J j
    have hδ : 0 < δ := dyadicShellWidth_pos J j
    have hδone : δ ≤ 1 := dyadicShellWidth_le_one J j
    have hlog : 0 < 1 + Real.log (1 / δ) := by
      have := Real.log_nonneg ((one_le_div hδ).mpr hδone)
      linarith
    rw [eLpNorm_ennreal_const_mul volume
      (measurable_dyadicAmplitudeShellSquare hA.continuous hcA _ _ f) _ (by linarith : 0 < p)]
    apply (mul_le_mul' le_rfl (hb δ hδ hδone f)).trans_eq
    rw [ENNReal.ofReal_rpow_of_pos hlog]
    have he : ENNReal.ofReal (δ ^ (α - 1)) *
        ENNReal.ofReal (δ ^ (1 / 2 - (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) = ENNReal.ofReal (δ ^ d) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), ← Real.rpow_add hδ]
      congr 2
      dsimp [d]
      ring
    calc
      _ = D * (ENNReal.ofReal (δ ^ (α - 1)) *
          ENNReal.ofReal (δ ^ (1 / 2 - (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) *
          ENNReal.ofReal ((1 + Real.log (1 / δ)) ^ θ)) *
            eLpNorm f (ENNReal.ofReal p) volume := by dsimp [θ, δ]; ring
      _ = _ := by rw [he, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
  unfold boundaryShellEnvelope
  apply (ennreal_eLpNorm_tsum_le (fun j =>
    (measurable_dyadicAmplitudeShellSquare hA.continuous hcA _ _ f).const_mul _)
    (by linarith : 1 ≤ p)).trans
  apply (ENNReal.tsum_le_tsum hj).trans_eq
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]

end OAI.Analysis.Fourier.SquareFunction
