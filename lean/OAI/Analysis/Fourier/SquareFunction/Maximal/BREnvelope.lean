import OAI.Analysis.Fourier.SquareFunction.Maximal.BRShell
import OAI.Analysis.Fourier.SquareFunction.Maximal.BRSummation

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Filter
open scoped ENNReal ContDiff Topology
noncomputable section
namespace OAI.Analysis.Fourier.SquareFunction


def brMaximalShellEnvelope {n : ℕ} (δ K : ℝ) (J : ℕ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) : ℝ≥0∞ :=
  ∑' j : ℕ, ENNReal.ofReal (((2 : ℝ) ^ (J + j)) ^ (-δ)) *
    (ENNReal.ofReal K * ballMaximal volume
      (OAI.Analysis.Fourier.BochnerRiesz.maximalShellCycles (OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile δ) ((2 : ℝ) ^ (J + j)) f) x)

theorem measurable_brMaximalShellEnvelope {n : ℕ} (δ K : ℝ) (J : ℕ)
    (f : SchwartzMap (Space n) ℂ) : Measurable (brMaximalShellEnvelope δ K J f) := by
  apply Measurable.tsum
  intro j
  exact ((measurable_ballMaximal volume _).const_mul _).const_mul _

theorem bochnerRieszMaximal_le_shell_envelope {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {J : ℕ} (hJ : 2 ≤ J) {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hzero : 0 ∉ tsupport χ)
    (hone : ∀ ξ, 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ 2 → χ ξ = 1)
    {B K : ℝ}
    (hb : ∀ h : ℝ, 0 < h → ∀ f : SchwartzMap (Space n) ℂ, ∀ x,
      ‖brScaledInterior δ J h f x‖ₑ ≤ ENNReal.ofReal B * ballMaximal volume (fun y => ‖f y‖ₑ) x)
    (hk : ∀ j : ℕ, ∀ h : ℝ, 0 < h → ∀ f : SchwartzMap (Space n) ℂ, ∀ x,
      ‖brScaledPacket δ χ j h f x‖ₑ ≤ ENNReal.ofReal K *
        ballMaximal volume (OAI.Analysis.Fourier.BochnerRiesz.maximalShellCycles (OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile δ) ((2 : ℝ) ^ j) f) x)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszMaximal δ f x ≤ ENNReal.ofReal B * ballMaximal volume (fun y => ‖f y‖ₑ) x +
      brMaximalShellEnvelope δ K J f x := by
  apply iSup_le
  intro R
  apply iSup_le
  intro hR
  apply le_of_tendsto (continuous_enorm.continuousAt.tendsto.comp
    (tendsto_brScaledInterior hδ hJ hR f x))
  apply Eventually.of_forall
  intro N
  change ‖brScaledInterior δ (J + N) R⁻¹ f x‖ₑ ≤ _
  rw [brScaledInterior_finite_partition hδ hJ hχ hc hzero hone (inv_pos.mpr hR) N f]
  change ‖brScaledInterior δ J R⁻¹ f x + _‖ₑ ≤ _
  apply (enorm_add_le _ _).trans
  apply add_le_add (hb R⁻¹ (inv_pos.mpr hR) f x)
  calc
    _ ≤ ∑ j ∈ Finset.range N, ‖Complex.ofReal (((2 : ℝ) ^ (J + j)) ^ (-δ)) *
        brScaledPacket δ χ (J + j) R⁻¹ f x‖ₑ := enorm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range N, ENNReal.ofReal (((2 : ℝ) ^ (J + j)) ^ (-δ)) *
        (ENNReal.ofReal K * ballMaximal volume
          (OAI.Analysis.Fourier.BochnerRiesz.maximalShellCycles (OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile δ) ((2 : ℝ) ^ (J + j)) f) x) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← Complex.real_smul, enorm_smul, Real.enorm_eq_ofReal (by positivity)]
      exact mul_le_mul' le_rfl (hk (J + j) R⁻¹ (inv_pos.mpr hR) f x)
    _ ≤ _ := ENNReal.sum_le_tsum (Finset.range N)

theorem exists_ballMaximal_envelope_constant (n : ℕ) {p : ℝ} (hp : 1 < p) :
    ∃ D : ℝ, 0 < D ∧ ∀ G : Space n → ℝ≥0∞, Measurable G → (∀ x, G x ≠ ⊤) →
      eLpNorm (ballMaximal volume G) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal D * eLpNorm G (ENNReal.ofReal p) volume := by
  let E : ℝ≥0∞ := 2 * ENNReal.ofReal ((5 : ℝ) ^ n * p / (p - 1)) ^ (1 / p)
  have hE : E ≠ ⊤ := ENNReal.mul_ne_top (by norm_num)
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
  refine ⟨E.toReal + 1, by positivity, ?_⟩
  intro G hG hGt
  apply (eLpNorm_ballMaximal_envelope_le hG hGt hp).trans
  apply mul_le_mul' _ le_rfl
  change E ≤ _
  calc
    E = ENNReal.ofReal E.toReal := (ENNReal.ofReal_toReal hE).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)

end OAI.Analysis.Fourier.SquareFunction
