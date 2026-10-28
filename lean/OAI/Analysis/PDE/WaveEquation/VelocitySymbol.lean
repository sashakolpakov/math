import OAI.Analysis.PDE.WaveEquation.Dyadic
import OAI.Analysis.Fourier.LocalSmoothing.DyadicSupport

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology
noncomputable section

namespace OAI.Analysis.PDE.WaveEquation

/-- The low-frequency velocity cutoff, equal to one on the ball of radius four. -/
def velocityLowCutoff {n : ℕ} (ξ : Space n) : ℝ := OAI.Analysis.Fourier.LocalSmoothing.smoothingLowBump n ((2:ℝ) • ξ)

/-- A positive smooth replacement of the squared norm, agreeing with it
where the high-frequency velocity multiplier is nonzero. -/
def velocityRadiusSq {n : ℕ} (ξ : Space n) : ℝ :=
  ‖ξ‖^2 + OAI.Analysis.Fourier.LocalSmoothing.smoothingLowBump n ((4:ℝ) • ξ)

def velocityHighSymbol {n : ℕ} (ξ : Space n) : ℝ :=
  (1 - velocityLowCutoff ξ) * velocityRadiusSq ξ ^ (-(1:ℝ)/2)

def velocityShiftSymbol {n : ℕ} (ξ : Space n) : ℝ :=
  (1+‖ξ‖^2)^((1:ℝ)/2) * velocityHighSymbol ξ

theorem velocityRadiusSq_one_le {n : ℕ} (ξ : Space n) : 1 ≤ velocityRadiusSq ξ := by
  by_cases h : ‖ξ‖ ≤ 1
  · have he : OAI.Analysis.Fourier.LocalSmoothing.smoothingLowBump n ((4:ℝ) • ξ) = 1 := by
      apply (OAI.Analysis.Fourier.LocalSmoothing.smoothingLowBump n).one_of_mem_closedBall
      simp only [Metric.mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<4)]
      change 4 * ‖ξ‖ ≤ 8
      linarith
    simp only [velocityRadiusSq, he]
    nlinarith [sq_nonneg ‖ξ‖]
  · have hb := (OAI.Analysis.Fourier.LocalSmoothing.smoothingLowBump n).nonneg (x := (4:ℝ) • ξ)
    dsimp only [velocityRadiusSq]
    nlinarith [norm_nonneg ξ]

theorem temperate_velocityLowCutoff (n : ℕ) :
    (@velocityLowCutoff n).HasTemperateGrowth :=
  ((OAI.Analysis.Fourier.LocalSmoothing.smoothingLowBump n).hasCompactSupport.comp_smul (by norm_num : (2:ℝ)≠0)).hasTemperateGrowth
    ((OAI.Analysis.Fourier.LocalSmoothing.smoothingLowBump n).contDiff.comp (contDiff_id.const_smul (2:ℝ)))

theorem temperate_velocityRadiusSq (n : ℕ) :
    (@velocityRadiusSq n).HasTemperateGrowth :=
  (Function.hasTemperateGrowth_norm_sq (Space n)).add
    (((OAI.Analysis.Fourier.LocalSmoothing.smoothingLowBump n).hasCompactSupport.comp_smul (by norm_num : (4:ℝ)≠0)).hasTemperateGrowth
      ((OAI.Analysis.Fourier.LocalSmoothing.smoothingLowBump n).contDiff.comp (contDiff_id.const_smul (4:ℝ))))

theorem temperate_velocityHighSymbol (n : ℕ) :
    (@velocityHighSymbol n).HasTemperateGrowth :=
  ((Function.HasTemperateGrowth.const 1).sub (temperate_velocityLowCutoff n)).mul
    (OAI.Analysis.Fourier.BesselPotential.temperate_rpow_of_half_lt (temperate_velocityRadiusSq n)
      (fun ξ ↦ lt_of_lt_of_le (by norm_num) (velocityRadiusSq_one_le ξ)) _)

theorem temperate_velocityShiftSymbol (n : ℕ) :
    (@velocityShiftSymbol n).HasTemperateGrowth :=
  (Function.hasTemperateGrowth_one_add_norm_sq_rpow (Space n) (1/2)).mul
    (temperate_velocityHighSymbol n)

theorem velocityLowCutoff_one {n : ℕ} {ξ : Space n} (hξ : ‖ξ‖ ≤ 4) :
    velocityLowCutoff ξ = 1 := by
  apply (OAI.Analysis.Fourier.LocalSmoothing.smoothingLowBump n).one_of_mem_closedBall
  simp only [Metric.mem_closedBall, dist_zero_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<2)]
  change 2 * ‖ξ‖ ≤ 8
  linarith

theorem velocityLowCutoff_zero {n : ℕ} {ξ : Space n} (hξ : 8 ≤ ‖ξ‖) :
    velocityLowCutoff ξ = 0 := by
  apply (OAI.Analysis.Fourier.LocalSmoothing.smoothingLowBump n).zero_of_le_dist
  simp only [dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0:ℝ)<2)]
  change 16 ≤ 2 * ‖ξ‖
  linarith

theorem velocityRadiusSq_eq {n : ℕ} {ξ : Space n} (hξ : 4 ≤ ‖ξ‖) :
    velocityRadiusSq ξ = ‖ξ‖^2 := by
  have he : OAI.Analysis.Fourier.LocalSmoothing.smoothingLowBump n ((4:ℝ) • ξ) = 0 := by
    apply (OAI.Analysis.Fourier.LocalSmoothing.smoothingLowBump n).zero_of_le_dist
    simp only [dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0:ℝ)<4)]
    change 16 ≤ 4 * ‖ξ‖
    linarith
  simp only [velocityRadiusSq, he, add_zero]

theorem velocityHighSymbol_eq {n : ℕ} (ξ : Space n) :
    velocityHighSymbol ξ = (1-velocityLowCutoff ξ) / ‖ξ‖ := by
  by_cases hξ : ‖ξ‖ ≤ 4
  · simp only [velocityHighSymbol, velocityLowCutoff_one hξ, sub_self, zero_mul, zero_div]
  · rw [velocityHighSymbol, velocityRadiusSq_eq (le_of_not_ge hξ),
      show (-(1:ℝ)/2) = -(1/2) by ring,
      Real.rpow_neg (sq_nonneg ‖ξ‖), ← Real.sqrt_eq_rpow,
      Real.sqrt_sq (norm_nonneg ξ), div_eq_mul_inv]

/-- The normalized order-minus-two defect of `J/|D|` on a fixed annulus. -/
def velocityShiftAnnulus {n : ℕ} (z : ℝ × Space n) : ℂ :=
  ((‖z.2‖ * (Real.sqrt (z.1^2 + ‖z.2‖^2) + ‖z.2‖))⁻¹ : ℝ) *
    OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff z.2

theorem contDiff_velocityShiftAnnulus (n : ℕ) :
    ContDiff ℝ ∞ (@velocityShiftAnnulus n) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z.2 ∈ tsupport OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff
  · have hx : z.2 ≠ 0 := by
      intro he; exact OAI.Analysis.Fourier.LocalSmoothing.zero_notMem_tsupport_smoothingAnnularCutoff n (he ▸ hz)
    have hn : ContDiffAt ℝ ∞ (fun y : ℝ × Space n ↦ ‖y.2‖) z :=
      (contDiffAt_norm ℝ hx).comp z contDiffAt_snd
    have hp : 0 < z.1^2 + ‖z.2‖^2 := by positivity
    have hs : ContDiffAt ℝ ∞ (fun y : ℝ × Space n ↦ Real.sqrt (y.1^2+‖y.2‖^2)) z :=
      ((contDiffAt_fst.pow 2).add
      (ContDiffAt.norm_sq (𝕜 := ℝ) contDiffAt_snd)).sqrt hp.ne'
    have hd : ‖z.2‖ * (Real.sqrt (z.1^2+‖z.2‖^2)+‖z.2‖) ≠ 0 := by positivity
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((hn.mul (hs.add hn)).inv hd)).mul
        ((OAI.Analysis.Fourier.LocalSmoothing.contDiff_smoothingAnnularCutoff n).contDiffAt.comp z contDiffAt_snd)
  · have he := (notMem_tsupport_iff_eventuallyEq.mp hz).comp_tendsto
      (continuous_snd.tendsto z)
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp only [velocityShiftAnnulus, show OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff y.2 = 0 from hy, mul_zero]

theorem tsupport_velocityShiftAnnulus (n : ℕ) :
    tsupport (@velocityShiftAnnulus n) ⊆ univ ×ˢ tsupport OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff := by
  intro z hz
  exact ⟨trivial, tsupport_comp_subset_preimage _ continuous_snd
    (tsupport_mul_subset_right (f := fun z : ℝ × Space n ↦
      (((‖z.2‖ * (Real.sqrt (z.1^2 + ‖z.2‖^2) + ‖z.2‖))⁻¹ : ℝ) : ℂ)) hz)⟩

end OAI.Analysis.PDE.WaveEquation
