import OAI.MeasureTheory.Kakeya.MaximalL1

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal

noncomputable section
namespace OAI.MeasureTheory.Kakeya

theorem dyadic_rpow_sum_lt_top {η : ℝ} (hη : 0 < η) :
    (∑' k, ENNReal.ofReal (dyadicRadius k ^ η)) < ∞ := by
  have heq (k : ℕ) : ENNReal.ofReal (dyadicRadius k ^ η) =
      (ENNReal.ofReal ((1 / 2 : ℝ) ^ η)) ^ k := by
    rw [dyadicRadius, ← Real.rpow_natCast_mul (by norm_num), mul_comm,
      Real.rpow_mul_natCast (by norm_num), ENNReal.ofReal_pow (by positivity)]
  simp_rw [heq]
  apply tsum_geometric_lt_top.mpr
  apply ENNReal.ofReal_lt_one.mpr
  exact Real.rpow_lt_one (by norm_num) (by norm_num) hη

theorem cover_loss_scale_identity {n : ℕ} (hn : 0 < n) {s δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal (δ ^ (-( (n : ℝ) - s) / (2 * n))) *
        (ENNReal.ofReal (δ ^ ((n : ℝ) - s))) ^ (1 / (n : ℝ)) =
      ENNReal.ofReal (δ ^ (((n : ℝ) - s) / (2 * n))) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
  congr 2
  field_simp
  ring

theorem maximal_implies_cover_sum_bound (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture) {n : ℕ}
    (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) (hsn : s < n) :
    ∃ D : ℝ≥0∞, D < ∞ ∧ ∀ (x : ℕ → Space n) (r : ℕ → ℝ), ballCoverCost s r < ∞ →
      (∑' k, ∫⁻ ω, OAI.MeasureTheory.Kakeya.kakeyaMaximal (dyadicRadius k)
        ((dyadicExpandedSet x r k).indicator (fun _ ↦ (1 : ℂ))) ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
          D * ballCoverCost s r ^ (1 / (n : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq : 0 ≤ 1 / (n : ℝ) := by positivity
  have hH : 0 ≤ 1 - 1 / (n : ℝ) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    exact sub_nonneg.mpr ((div_le_one hnpos).mpr this)
  let η : ℝ := ((n : ℝ) - s) / (2 * n)
  have hη : 0 < η := div_pos (sub_pos.mpr hsn) (by positivity)
  obtain ⟨C, hC, hbound⟩ := maximal_indicator_L1_bound hK hn hη
  let B : ℝ≥0∞ := ENNReal.ofReal (3 ^ n * 2 ^ s) * volume (Metric.ball (0 : Space n) 1)
  let H : ℝ≥0∞ := OAI.Analysis.Fourier.Restriction.sphereMeasure n Set.univ ^ (1 - 1 / (n : ℝ))
  let D₀ : ℝ≥0∞ := ENNReal.ofReal C * B ^ (1 / (n : ℝ)) * H
  let G : ℝ≥0∞ := ∑' k, ENNReal.ofReal (dyadicRadius k ^ η)
  have hB : B < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top
  have hHfin : H < ∞ := ENNReal.rpow_lt_top_of_nonneg hH (measure_ne_top _ _)
  have hD₀ : D₀ < ∞ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.rpow_lt_top_of_nonneg hq hB.ne)) hHfin
  have hG : G < ∞ := dyadic_rpow_sum_lt_top hη
  refine ⟨D₀ * G, ENNReal.mul_lt_top hD₀ hG, ?_⟩
  intro x r hcost
  have hvol (k : ℕ) : volume (dyadicExpandedSet x r k) ≤
      (B * ballCoverCost s r) * ENNReal.ofReal (dyadicRadius k ^ ((n : ℝ) - s)) := by
    have h := volume_dyadicExpandedSet_le hs x r k
    rw [ENNReal.ofReal_mul (by positivity)] at h
    convert h using 1 ; dsimp only [B] ; ring
  have hterm (k : ℕ) :
      (∫⁻ ω, OAI.MeasureTheory.Kakeya.kakeyaMaximal (dyadicRadius k)
        ((dyadicExpandedSet x r k).indicator (fun _ ↦ (1 : ℂ))) ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
          D₀ * ENNReal.ofReal (dyadicRadius k ^ η) * ballCoverCost s r ^ (1 / (n : ℝ)) := by
    have hδ := dyadicRadius_pos k
    have hAfin : volume (dyadicExpandedSet x r k) ≠ ∞ :=
      (lt_of_le_of_lt (hvol k) (ENNReal.mul_lt_top (ENNReal.mul_lt_top hB hcost) ENNReal.ofReal_lt_top)).ne
    have hbase := hbound (dyadicRadius k) hδ (dyadicRadius_le_one k)
      (dyadicExpandedSet x r k) (isOpen_dyadicExpandedSet x r k).measurableSet hAfin
    have hpow := ENNReal.rpow_le_rpow (hvol k) hq
    calc
      _ ≤ ENNReal.ofReal (C * dyadicRadius k ^ (-η)) *
          (((B * ballCoverCost s r) * ENNReal.ofReal (dyadicRadius k ^ ((n : ℝ) - s))) ^
            (1 / (n : ℝ))) * H :=
        hbase.trans (mul_le_mul' (mul_le_mul' le_rfl hpow) le_rfl)
      _ = (ENNReal.ofReal C * B ^ (1 / (n : ℝ)) * H) *
          (ENNReal.ofReal (dyadicRadius k ^ (-η)) *
            (ENNReal.ofReal (dyadicRadius k ^ ((n : ℝ) - s))) ^ (1 / (n : ℝ))) *
          ballCoverCost s r ^ (1 / (n : ℝ)) := by
        rw [ENNReal.ofReal_mul hC.le, ENNReal.mul_rpow_of_nonneg _ _ hq,
          ENNReal.mul_rpow_of_nonneg _ _ hq]
        ring
      _ = _ := by
        have hid := cover_loss_scale_identity (show 0 < n by omega) (s := s) hδ
        have heta : -η = -((n : ℝ) - s) / (2 * n) := by dsimp [η]; ring
        rw [heta, hid]
  calc
    _ ≤ ∑' k, D₀ * ENNReal.ofReal (dyadicRadius k ^ η) * ballCoverCost s r ^ (1 / (n : ℝ)) :=
      ENNReal.tsum_le_tsum hterm
    _ = (D₀ * G) * ballCoverCost s r ^ (1 / (n : ℝ)) := by
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]

end OAI.MeasureTheory.Kakeya
