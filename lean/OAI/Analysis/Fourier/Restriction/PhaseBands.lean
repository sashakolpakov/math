import OAI.Analysis.Fourier.Restriction.Bumps
import OAI.Analysis.Fourier.Restriction.FiniteMoments

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem finitePhaseSum_const_mul {n : ℕ} (E : Finset (Space n))
    (a : Space n → ℂ) (c : ℂ) :
    finitePhaseSum E (fun z ↦ c * a z) = c • finitePhaseSum E a := by
  funext ξ
  simp only [finitePhaseSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem finitePhaseSum_band_filter {n : ℕ} (E : Finset (Space n))
    (a : Space n → ℂ) (l u : ℝ) :
    finitePhaseSum E (amplitudeBand a l u) =
      finitePhaseSum (E.filter (fun z ↦ l < ‖a z‖)) (amplitudeBand a l u) := by
  classical
  funext ξ
  unfold finitePhaseSum
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro z hz hzs
  have hz' : ‖a z‖ ≤ l := by
    exact le_of_not_gt (fun h ↦ hzs (Finset.mem_filter.mpr ⟨hz, h⟩))
  rw [amplitudeBand_eq_zero_of_le a l u hz', zero_mul]

theorem finitePhaseSum_band_bound {n : ℕ} (E : Finset (Space n))
    {p : ℝ≥0∞} {q s : ℝ} (hq : 0 < q) (hs : 0 ≤ s) {C : ℝ≥0∞}
    (hres : ∀ S : Finset (Space n), S ⊆ E → ∀ a : Space n → ℂ,
      (∀ z ∈ S, ‖a z‖ ≤ 1) → eLpNorm (finitePhaseSum S a) p (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        C * ENNReal.ofReal ((S.card : ℝ) ^ s))
    (a : Space n → ℂ) (hsum : (∑ z ∈ E, ‖a z‖ ^ q) ≤ 1)
    {l u : ℝ} (hl : 0 < l) (hu : 0 < u) :
    eLpNorm (finitePhaseSum E (amplitudeBand a l u)) p (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      C * ENNReal.ofReal (u * l ^ (-q * s)) := by
  classical
  let S := E.filter (fun z ↦ l < ‖a z‖)
  let b : Space n → ℂ := fun z ↦ (u : ℂ)⁻¹ * amplitudeBand a l u z
  have hb : ∀ z ∈ S, ‖b z‖ ≤ 1 := by
    intro z hz
    change ‖(u : ℂ)⁻¹ * amplitudeBand a l u z‖ ≤ 1
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
    calc
      _ ≤ u⁻¹ * u := mul_le_mul_of_nonneg_left (norm_amplitudeBand_le_upper a l hu.le z) (by positivity)
      _ = 1 := inv_mul_cancel₀ hu.ne'
  have H := hres S (Finset.filter_subset _ _) b hb
  have hc := finite_card_norm_gt_le E a hq hl hsum
  have hpow : (S.card : ℝ) ^ s ≤ l ^ (-q * s) := by
    calc
      _ ≤ (l ^ (-q)) ^ s := Real.rpow_le_rpow (by positivity) hc hs
      _ = _ := (Real.rpow_mul hl.le _ _).symm
  have he : amplitudeBand a l u = (fun z ↦ (u : ℂ) * b z) := by
    funext z
    dsimp [b]
    rw [← mul_assoc, mul_inv_cancel₀ (show (u : ℂ) ≠ 0 by exact_mod_cast hu.ne'), one_mul]
  rw [finitePhaseSum_band_filter, he, finitePhaseSum_const_mul, eLpNorm_const_smul]
  have hnorm : ‖(u : ℂ)‖ₑ = ENNReal.ofReal u := by
    simp only [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  rw [hnorm]
  calc
    _ ≤ ENNReal.ofReal u * (C * ENNReal.ofReal ((S.card : ℝ) ^ s)) := by gcongr
    _ ≤ ENNReal.ofReal u * (C * ENNReal.ofReal (l ^ (-q * s))) := by gcongr
    _ = _ := by rw [ENNReal.ofReal_mul hu.le]; ring

end OAI.Analysis.Fourier.Restriction
