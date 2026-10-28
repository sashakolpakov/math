import OAI.Geometry.Nikodym.HausdorffOccupancy
import OAI.Geometry.Nikodym.Measurability
import OAI.MeasureTheory.Kakeya.CoverEstimate

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set
open scoped ENNReal
namespace OAI.Geometry.Nikodym

theorem nikodym_indicator_restricted_L1_bound (hN : NikodymMaximalConjecture)
    {n : ℕ} (hn : 2 ≤ n) {η : ℝ} (hη : 0 < η) (Ω : Set (Space n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ A : Set (Space n),
      MeasurableSet A → volume A ≠ ∞ →
      (∫⁻ x in Ω, nikodymMaximal δ (A.indicator (fun _ => (1:ℂ))) x) ≤
        ENNReal.ofReal (C * δ^(-η)) * volume A^(1/(n:ℝ)) *
          volume Ω^(1-1/(n:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := hN n hn η hη
  refine ⟨C,hC,?_⟩
  intro δ hδ hδone A hA hAfin
  have hf : MemLp (A.indicator (fun _ => (1:ℂ))) n (volume : Measure (Space n)) :=
    memLp_indicator_const _ hA _ (Or.inr hAfin)
  have hm := measurable_nikodymMaximal δ (A.indicator (fun _ => (1:ℂ)))
    (measurable_const.indicator hA).aestronglyMeasurable
  obtain ⟨_,hNb⟩ := hbound δ hδ hδone _ hf
  have hcmp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := volume.restrict Ω)
    (show (1:ℝ≥0∞) ≤ n by exact_mod_cast (show 1 ≤ n by omega)) hm.aestronglyMeasurable
  have hmono : eLpNorm (nikodymMaximal δ (A.indicator (fun _ => (1:ℂ)))) n (volume.restrict Ω) ≤
      eLpNorm (nikodymMaximal δ (A.indicator (fun _ => (1:ℂ)))) n volume :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  have hn0 : (n:ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hfin : (n:ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top n
  have hfNorm : eLpNorm (A.indicator (fun _ => (1:ℂ))) n (volume : Measure (Space n)) =
      volume A^(1/(n:ℝ)) := by
    rw [eLpNorm_indicator_const hA.nullMeasurableSet hn0 hfin]
    simp
  rw [hfNorm] at hNb
  rw [eLpNorm_one_eq_lintegral_enorm hm.aestronglyMeasurable] at hcmp
  simp only [enorm_eq_self,Measure.restrict_apply_univ,ENNReal.toReal_one,
    ENNReal.toReal_natCast,div_one] at hcmp
  exact hcmp.trans (mul_le_mul' (hmono.trans hNb) le_rfl)

theorem nikodym_maximal_implies_cover_sum_bound (hN : NikodymMaximalConjecture)
    {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) (hsn : s < n)
    (Ω : Set (Space n)) (hΩ : volume Ω < ∞) :
    ∃ D : ℝ≥0∞, D < ∞ ∧ ∀ (x : ℕ → Space n) (r : ℕ → ℝ), OAI.MeasureTheory.Kakeya.ballCoverCost s r < ∞ →
      (∑' k, ∫⁻ y in Ω, nikodymMaximal (OAI.MeasureTheory.Kakeya.dyadicRadius k)
        ((OAI.MeasureTheory.Kakeya.dyadicExpandedSet x r k).indicator (fun _ => (1:ℂ))) y) ≤
          D * OAI.MeasureTheory.Kakeya.ballCoverCost s r^(1/(n:ℝ)) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq : 0 ≤ 1/(n:ℝ) := by positivity
  have hH : 0 ≤ 1-1/(n:ℝ) := by
    have : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    exact sub_nonneg.mpr ((div_le_one hnpos).mpr this)
  let η : ℝ := ((n:ℝ)-s)/(2*n)
  have hη : 0 < η := div_pos (sub_pos.mpr hsn) (by positivity)
  obtain ⟨C,hC,hbound⟩ := nikodym_indicator_restricted_L1_bound hN hn hη Ω
  let B : ℝ≥0∞ := ENNReal.ofReal (3^n * 2^s) * volume (Metric.ball (0:Space n) 1)
  let H : ℝ≥0∞ := volume Ω^(1-1/(n:ℝ))
  let D₀ : ℝ≥0∞ := ENNReal.ofReal C * B^(1/(n:ℝ)) * H
  let G : ℝ≥0∞ := ∑' k,ENNReal.ofReal (OAI.MeasureTheory.Kakeya.dyadicRadius k^η)
  have hB : B < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top
  have hHfin : H < ∞ := ENNReal.rpow_lt_top_of_nonneg hH hΩ.ne
  have hD₀ : D₀ < ∞ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.rpow_lt_top_of_nonneg hq hB.ne)) hHfin
  have hG : G < ∞ := OAI.MeasureTheory.Kakeya.dyadic_rpow_sum_lt_top hη
  refine ⟨D₀*G,ENNReal.mul_lt_top hD₀ hG,?_⟩
  intro x r hcost
  have hvol (k : ℕ) : volume (OAI.MeasureTheory.Kakeya.dyadicExpandedSet x r k) ≤
      (B * OAI.MeasureTheory.Kakeya.ballCoverCost s r) * ENNReal.ofReal (OAI.MeasureTheory.Kakeya.dyadicRadius k^((n:ℝ)-s)) := by
    have h := OAI.MeasureTheory.Kakeya.volume_dyadicExpandedSet_le hs x r k
    rw [ENNReal.ofReal_mul (by positivity)] at h
    convert h using 1 ; dsimp only [B] ; ring
  have hterm (k : ℕ) :
      (∫⁻ y in Ω, nikodymMaximal (OAI.MeasureTheory.Kakeya.dyadicRadius k)
        ((OAI.MeasureTheory.Kakeya.dyadicExpandedSet x r k).indicator (fun _ => (1:ℂ))) y) ≤
      D₀ * ENNReal.ofReal (OAI.MeasureTheory.Kakeya.dyadicRadius k^η) * OAI.MeasureTheory.Kakeya.ballCoverCost s r^(1/(n:ℝ)) := by
    have hδ := OAI.MeasureTheory.Kakeya.dyadicRadius_pos k
    have hAfin : volume (OAI.MeasureTheory.Kakeya.dyadicExpandedSet x r k) ≠ ∞ :=
      (lt_of_le_of_lt (hvol k) (ENNReal.mul_lt_top
        (ENNReal.mul_lt_top hB hcost) ENNReal.ofReal_lt_top)).ne
    have hbase := hbound (OAI.MeasureTheory.Kakeya.dyadicRadius k) hδ (OAI.MeasureTheory.Kakeya.dyadicRadius_le_one k)
      (OAI.MeasureTheory.Kakeya.dyadicExpandedSet x r k) (OAI.MeasureTheory.Kakeya.isOpen_dyadicExpandedSet x r k).measurableSet hAfin
    have hpow := ENNReal.rpow_le_rpow (hvol k) hq
    calc
      _ ≤ ENNReal.ofReal (C * OAI.MeasureTheory.Kakeya.dyadicRadius k^(-η)) *
          (((B * OAI.MeasureTheory.Kakeya.ballCoverCost s r) * ENNReal.ofReal (OAI.MeasureTheory.Kakeya.dyadicRadius k^((n:ℝ)-s)))^(1/(n:ℝ))) * H :=
        hbase.trans (mul_le_mul' (mul_le_mul' le_rfl hpow) le_rfl)
      _ = (ENNReal.ofReal C * B^(1/(n:ℝ)) * H) *
          (ENNReal.ofReal (OAI.MeasureTheory.Kakeya.dyadicRadius k^(-η)) *
            (ENNReal.ofReal (OAI.MeasureTheory.Kakeya.dyadicRadius k^((n:ℝ)-s)))^(1/(n:ℝ))) *
          OAI.MeasureTheory.Kakeya.ballCoverCost s r^(1/(n:ℝ)) := by
        rw [ENNReal.ofReal_mul hC.le,ENNReal.mul_rpow_of_nonneg _ _ hq,
          ENNReal.mul_rpow_of_nonneg _ _ hq]
        ring
      _ = _ := by
        have hid := OAI.MeasureTheory.Kakeya.cover_loss_scale_identity (show 0 < n by omega) (s := s) hδ
        have heta : -η = -((n:ℝ)-s)/(2*n) := by dsimp [η]; ring
        rw [heta,hid]
  calc
    _ ≤ ∑' k,D₀ * ENNReal.ofReal (OAI.MeasureTheory.Kakeya.dyadicRadius k^η) * OAI.MeasureTheory.Kakeya.ballCoverCost s r^(1/(n:ℝ)) :=
      ENNReal.tsum_le_tsum hterm
    _ = _ := by rw [ENNReal.tsum_mul_right,ENNReal.tsum_mul_left]

theorem nikodym_dyadic_occupancy_integral_lower {n : ℕ} (hn : 1 ≤ n)
    (x : ℕ → Space n) (r : ℕ → ℝ) (hr : ∀ j,r j ≤ 1)
    {Z F Ω : Set (Space n)} (hZ : Z.Countable) (hΩ : MeasurableSet Ω) {ell : ℝ}
    (hF : HasNikodymSegments F Ω ell)
    (hcover : F ⊆ Z ∪ ⋃ j,Metric.ball (x j) (r j)) :
    (ENNReal.ofReal (OAI.MeasureTheory.Kakeya.lineOccupancyConstant n) * ENNReal.ofReal ell) * volume Ω ≤
      ∑' k,∫⁻ y in Ω,nikodymMaximal (OAI.MeasureTheory.Kakeya.dyadicRadius k)
        ((OAI.MeasureTheory.Kakeya.dyadicExpandedSet x r k).indicator (fun _ => (1:ℂ))) y := by
  have hm (k : ℕ) : Measurable (nikodymMaximal (OAI.MeasureTheory.Kakeya.dyadicRadius k)
      ((OAI.MeasureTheory.Kakeya.dyadicExpandedSet x r k).indicator (fun _ => (1:ℂ)))) :=
    measurable_nikodymMaximal _ _ (measurable_const.indicator
      (OAI.MeasureTheory.Kakeya.isOpen_dyadicExpandedSet x r k).measurableSet).aestronglyMeasurable
  calc
    _ = ∫⁻ _ in Ω, ENNReal.ofReal (OAI.MeasureTheory.Kakeya.lineOccupancyConstant n) * ENNReal.ofReal ell := by simp
    _ ≤ ∫⁻ y in Ω,∑' k,nikodymMaximal (OAI.MeasureTheory.Kakeya.dyadicRadius k)
        ((OAI.MeasureTheory.Kakeya.dyadicExpandedSet x r k).indicator (fun _ => (1:ℂ))) y := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hΩ] with y hy
      exact nikodym_dyadic_occupancy_sum_lower hn x r hr hZ hF hcover hy
    _ = _ := lintegral_tsum (fun k => (hm k).aemeasurable)

end OAI.Geometry.Nikodym
