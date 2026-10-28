import OAI.MeasureTheory.Kakeya.Restriction

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal BigOperators

noncomputable section
namespace OAI.MeasureTheory.Kakeya

theorem criticalExponent_gt_two {n : ℕ} (hn : 2 ≤ n) : 2 < OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold OAI.Analysis.Fourier.LocalSmoothing.criticalExponent
  rw [lt_div_iff₀ (by linarith : 0 < (n : ℝ) - 1)]
  linarith

theorem diagonal_restriction_range {n : ℕ} (hn : 2 ≤ n) {q : ℝ}
    (hq : OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n < q) :
    ((n : ℝ) + 1) / ((n : ℝ) - 1) * OAI.Analysis.Fourier.Restriction.conjugateExponent (ENNReal.ofReal q) < q := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hq2 : 2 < q := (criticalExponent_gt_two hn).trans hq
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  have hq0 : 0 < q := by linarith
  have hqm1 : 0 < q - 1 := by linarith
  have hmul : 2 * (n : ℝ) < q * ((n : ℝ) - 1) := (div_lt_iff₀ hn1).mp hq
  have hA : ((n : ℝ) + 1) / ((n : ℝ) - 1) < q - 1 :=
    (div_lt_iff₀ hn1).mpr (by nlinarith)
  simp only [OAI.Analysis.Fourier.Restriction.conjugateExponent, ENNReal.ofReal_ne_top, ↓reduceIte,
    ENNReal.toReal_ofReal hq0.le]
  rw [← mul_div_assoc, div_lt_iff₀ hqm1]
  simpa only [mul_comm] using mul_lt_mul_of_pos_right hA hq0

/-- The weighted tube overlap, with the cap masses retained exactly. -/
def packetTubeOverlap {n m : ℕ} (δ : ℝ) (v x : Fin m → Space n) (c : Fin m → ℂ)
    (y : Space n) : ℝ :=
  ∑ i, (OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) (x i)).indicator
    (fun _ ↦ (‖c i‖ * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i)) / 2) ^ 2) y

theorem packetTubeOverlap_nonneg {n m : ℕ} (δ : ℝ) (v x : Fin m → Space n)
    (c : Fin m → ℂ) (y : Space n) : 0 ≤ packetTubeOverlap δ v x c y := by
  apply Finset.sum_nonneg
  intro i _
  apply Set.indicator_nonneg
  intro _ _
  positivity

theorem measurable_packetTubeOverlap {n m : ℕ} (δ : ℝ) (v x : Fin m → Space n)
    (c : Fin m → ℂ) : Measurable (packetTubeOverlap δ v x c) := by
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.indicator (measurableSet_tube _ _ _)

theorem packetTubeOverlap_le {n m : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (v x : Fin m → Space n) (c : Fin m → ℂ) (hv : ∀ i, ‖v i‖ = 1) (y : Space n) :
    packetTubeOverlap δ v x c y ≤
      ∑ i, ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω ↦ c i * capPacket δ (v i) (x i) ω)
        ((δ ^ 2)⁻¹ • y)‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hy : y ∈ OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) (x i)
  · rw [Set.indicator_of_mem hy]
    have hpacket := cap_packet_lower_bound hδ (hv i) hy
    have hw : ‖c i‖ * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i)) / 2 ≤
        ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω ↦ c i * capPacket δ (v i) (x i) ω)
          ((δ ^ 2)⁻¹ • y)‖ := by
      rw [OAI.Analysis.Fourier.Restriction.sphericalExtension_const_mul, norm_mul]
      convert mul_le_mul_of_nonneg_left hpacket (norm_nonneg (c i)) using 1
      ring
    exact pow_le_pow_left₀ (by positivity) hw 2
  · rw [Set.indicator_of_notMem hy]
    positivity

/-- Restriction gives a quantitative weighted tube-overlap estimate. This
retains actual cap measures; geometric cap-size estimates and finite-direction
duality are separate steps on the route to the Kakeya maximal inequality. -/
theorem restriction_implies_weighted_tube_overlap
    (hR : OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture) (n : ℕ) (hn : 2 ≤ n)
    {r q : ℝ} (hr : 1 < r) (hq : 2 ≤ q) (hcrit : OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n < q)
    (hdiag : ((n : ℝ) + 1) / ((n : ℝ) - 1) *
      OAI.Analysis.Fourier.Restriction.conjugateExponent (ENNReal.ofReal r) < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ →
      ∀ (v x : Fin m → Space n) (c : Fin m → ℂ), (∀ i, ‖v i‖ = 1) →
      (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
      Integrable (fun y ↦ packetTubeOverlap δ v x c y ^ (q / 2)) volume ∧
      (∫ y, packetTubeOverlap δ v x c y ^ (q / 2)) ≤
        (δ ^ 2) ^ n * (C ^ q *
          (∑ i, ‖c i‖ ^ r * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i))) ^ (q / r)) := by
  obtain ⟨C, hC, hbound⟩ := restriction_implies_packet_square_estimate hR n hn hr hq hcrit hdiag
  refine ⟨C, hC, ?_⟩
  intro m δ hδ v x c hv hsep
  obtain ⟨henergy, hestimate⟩ := hbound m δ hδ v x c hsep
  let energy : Space n → ℝ := fun y ↦
    (∑ i, ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω ↦ c i * capPacket δ (v i) (x i) ω) y‖ ^ 2) ^ (q / 2)
  have hi : Integrable (fun y ↦ energy ((δ ^ 2)⁻¹ • y)) volume :=
    henergy.comp_smul (inv_ne_zero (pow_ne_zero 2 hδ.ne'))
  have hdom (y : Space n) : packetTubeOverlap δ v x c y ^ (q / 2) ≤
      energy ((δ ^ 2)⁻¹ • y) :=
    Real.rpow_le_rpow (packetTubeOverlap_nonneg δ v x c y)
      (packetTubeOverlap_le hδ v x c hv y) (by linarith)
  have hm : AEStronglyMeasurable (fun y ↦ packetTubeOverlap δ v x c y ^ (q / 2)) volume :=
    (Real.continuous_rpow_const (by linarith : 0 ≤ q / 2)).comp_aestronglyMeasurable
      (measurable_packetTubeOverlap δ v x c).aestronglyMeasurable
  have ho : Integrable (fun y ↦ packetTubeOverlap δ v x c y ^ (q / 2)) volume := by
    apply hi.mono' hm
    exact Filter.Eventually.of_forall fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (Real.rpow_nonneg (packetTubeOverlap_nonneg δ v x c y) _)]
      exact hdom y
  refine ⟨ho, (integral_mono ho hi hdom).trans ?_⟩
  rw [Measure.integral_comp_inv_smul_of_nonneg volume energy (sq_nonneg δ)]
  have hdim : Module.finrank ℝ (Space n) = n := by simp [Space]
  rw [hdim, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left hestimate (by positivity)

/-- Diagonal specialization of the restriction-to-overlap estimate. -/
theorem restriction_implies_diagonal_packet_bound
    (hR : OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture) (n : ℕ) (hn : 2 ≤ n)
    {q : ℝ} (hq : OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ →
      ∀ (v x : Fin m → Space n) (c : Fin m → ℂ), (∀ i, ‖v i‖ = 1) →
      (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
      Integrable (fun y ↦ packetTubeOverlap δ v x c y ^ (q / 2)) volume ∧
      (∫ y, packetTubeOverlap δ v x c y ^ (q / 2)) ≤
        (δ ^ 2) ^ n * (C ^ q * ∑ i, ‖c i‖ ^ q *
          (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i))) := by
  have hq2 := (criticalExponent_gt_two hn).trans hq
  have hq0 : q ≠ 0 := by linarith
  obtain ⟨C, hC, hbound⟩ := restriction_implies_weighted_tube_overlap hR n hn
    (by linarith : 1 < q) hq2.le hq (diagonal_restriction_range hn hq)
  refine ⟨C, hC, ?_⟩
  simpa only [div_self hq0, Real.rpow_one] using hbound

end OAI.MeasureTheory.Kakeya
