import OAI.MeasureTheory.Kakeya.CoverEstimate
import OAI.MeasureTheory.Kakeya.HausdorffCovers
import OAI.MeasureTheory.Kakeya.RestrictionMaximal

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace OAI.MeasureTheory.Kakeya

theorem sphereMeasure_univ_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < OAI.Analysis.Fourier.Restriction.sphereMeasure n Set.univ := by
  let v : Space n := EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (1 : ℝ)
  have hv : ‖v‖ = 1 := by simp [v]
  have hcap := OAI.Analysis.Fourier.Restriction.packetCap_real_lower hn (δ := 1) zero_lt_one le_rfl hv
  simp only [one_pow, mul_one] at hcap
  have hreal : 0 < (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap 1 v) :=
    (OAI.Analysis.Fourier.Restriction.packetCap_lower_coefficient_pos hn).trans_le hcap
  have hpos : 0 < OAI.Analysis.Fourier.Restriction.sphereMeasure n (packetCap 1 v) := (ENNReal.toReal_pos_iff.mp hreal).1
  exact hpos.trans_le (measure_mono (Set.subset_univ _))

/-- The maximal conjecture rules out zero Hausdorff measure at every
strictly subcritical positive dimension. The cover sets need not be
measurable, bounded, or closed. -/
theorem maximal_implies_hausdorffMeasure_ne_zero (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture)
    {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) (hsn : s < n)
    {F : Set (Space n)} (hF : OAI.MeasureTheory.Kakeya.IsKakeyaSet F) :
    Measure.hausdorffMeasure s F ≠ 0 := by
  intro hnull
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq : 0 < 1 / (n : ℝ) := by positivity
  obtain ⟨D, hD, hbound⟩ := maximal_implies_cover_sum_bound hK hn hs hsn
  let A : ℝ≥0∞ := (2 : ℝ≥0∞) ^ s
  have hA : A < ∞ := ENNReal.rpow_lt_top_of_nonneg hs.le (by norm_num)
  have hsmall (m : ℕ) :
      ENNReal.ofReal (lineOccupancyConstant n) * OAI.Analysis.Fourier.Restriction.sphereMeasure n Set.univ ≤
        D * (A * (1 / 2 : ℝ≥0∞) ^ m) ^ (1 / (n : ℝ)) := by
    have hε : 0 < (1 / 2 : ℝ≥0∞) ^ m := pos_iff_ne_zero.mpr (pow_ne_zero m (by norm_num))
    obtain ⟨x, r, Z, hZ, hcover, hr, hcost⟩ := hausdorff_null_ball_cover hs hnull hε
    have hcostfin : ballCoverCost s r < ∞ :=
      lt_of_le_of_lt hcost (ENNReal.mul_lt_top hA (by finiteness))
    have hlo := dyadic_occupancy_integral_lower (show 1 ≤ n by omega) x r
      (fun j ↦ (hr j).2) hZ hF hcover
    exact hlo.trans ((hbound x r hcostfin).trans
      (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hcost hq.le)))
  have hgeo : Tendsto (fun m : ℕ ↦ (1 / 2 : ℝ≥0∞) ^ m) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have harg : Tendsto (fun m : ℕ ↦ A * (1 / 2 : ℝ≥0∞) ^ m) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hgeo (Or.inr hA.ne)
  have hlim : Tendsto (fun m : ℕ ↦ D * (A * (1 / 2 : ℝ≥0∞) ^ m) ^ (1 / (n : ℝ)))
      atTop (𝓝 0) :=
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hD.ne hq).comp harg
  have hzero : ENNReal.ofReal (lineOccupancyConstant n) * OAI.Analysis.Fourier.Restriction.sphereMeasure n Set.univ ≤ 0 :=
    ge_of_tendsto hlim (Eventually.of_forall hsmall)
  have hpositive : 0 < ENNReal.ofReal (lineOccupancyConstant n) * OAI.Analysis.Fourier.Restriction.sphereMeasure n Set.univ :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (lineOccupancyConstant_pos n)).ne'
      (sphereMeasure_univ_pos (show 1 ≤ n by omega)).ne'
  exact hpositive.not_ge hzero

/-- Kakeya maximal estimates with every positive loss imply the full
Hausdorff-dimensional Kakeya conjecture, not merely its Minkowski form. -/
theorem kakeyaMaximal_implies_kakeya (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture) : OAI.MeasureTheory.Kakeya.KakeyaConjecture := by
  intro n hn F hF
  apply le_antisymm
  · calc
      dimH F ≤ dimH (Set.univ : Set (Space n)) := dimH_mono (Set.subset_univ F)
      _ = n := by rw [Real.dimH_univ_eq_finrank]; simp only [Space, finrank_euclideanSpace_fin]
  · apply ENNReal.le_of_forall_nnreal_lt
    intro d hd
    by_cases hd0 : d = 0
    · simp [hd0]
    · have hdpos : 0 < (d : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hd0)
      have hdn : (d : ℝ) < n := by exact_mod_cast hd
      exact le_dimH_of_hausdorffMeasure_ne_zero
        (maximal_implies_hausdorffMeasure_ne_zero hK hn hdpos hdn hF)

/-- The already checked analytic restriction-to-maximal implication now
also yields the geometric Kakeya conjecture. -/
theorem restriction_implies_kakeya (hR : OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture) : OAI.MeasureTheory.Kakeya.KakeyaConjecture :=
  kakeyaMaximal_implies_kakeya (restriction_implies_kakeyaMaximal hR)

end OAI.MeasureTheory.Kakeya
