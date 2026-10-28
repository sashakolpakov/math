import OAI.MeasureTheory.Kakeya.Duality

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal BigOperators

noncomputable section
namespace OAI.MeasureTheory.Kakeya

def tubeOverlap {n m : ℕ} (δ : ℝ) (v x : Fin m → Space n) (a : Fin m → ℝ)
    (y : Space n) : ℝ := ∑ i, (OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) (x i)).indicator (fun _ ↦ a i) y

theorem tubeOverlap_nonneg {n m : ℕ} (δ : ℝ) (v x : Fin m → Space n)
    (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) (y : Space n) : 0 ≤ tubeOverlap δ v x a y :=
  Finset.sum_nonneg fun i _ ↦ Set.indicator_nonneg (fun _ _ ↦ ha i) y

theorem memLp_tubeOverlap {n m : ℕ} (δ : ℝ) (v x : Fin m → Space n)
    (a : Fin m → ℝ) (s : ℝ≥0∞) : MemLp (tubeOverlap δ v x a) s volume := by
  apply memLp_finsetSum
  intro i _
  exact memLp_indicator_const s (measurableSet_tube _ _ _) (a i)
    (Or.inr (volume_tube_lt_top _ _ _).ne)

theorem scaled_sqrt_norm {a L : ℝ} (_ha : 0 ≤ a) (hL : 0 < L) :
    ‖((2 / L * Real.sqrt a : ℝ) : ℂ)‖ = 2 / L * Real.sqrt a := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem scaled_sqrt_rpow {a L q : ℝ} (ha : 0 ≤ a) (hL : 0 < L) :
    ‖((2 / L * Real.sqrt a : ℝ) : ℂ)‖ ^ q = (2 / L) ^ q * a ^ (q / 2) := by
  rw [scaled_sqrt_norm ha hL, Real.mul_rpow (by positivity) (Real.sqrt_nonneg _)]
  congr 1
  calc
    Real.sqrt a ^ q = Real.sqrt a ^ ((2 : ℝ) * (q / 2)) := by congr 1; ring
    _ = (Real.sqrt a ^ (2 : ℕ)) ^ (q / 2) := by
      simpa using Real.rpow_natCast_mul (Real.sqrt_nonneg a) 2 (q / 2)
    _ = a ^ (q / 2) := by rw [Real.sq_sqrt ha]

theorem tubeOverlap_le_scaled_packetTubeOverlap {n m : ℕ} (δ : ℝ)
    (v x : Fin m → Space n) (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i)
    {L : ℝ} (hL : 0 < L) (hlower : ∀ i, L ≤ (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i)))
    (y : Space n) :
    tubeOverlap δ v x a y ≤ packetTubeOverlap δ v x
      (fun i ↦ ((2 / L * Real.sqrt (a i) : ℝ) : ℂ)) y := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hy : y ∈ OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) (x i)
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, scaled_sqrt_norm (ha i) hL]
    have hroot : Real.sqrt (a i) ≤
        2 / L * Real.sqrt (a i) * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i)) / 2 := by
      calc
        Real.sqrt (a i) = (2 / L * Real.sqrt (a i)) * L / 2 := by field_simp [hL.ne']
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hlower i) (by positivity)) (by norm_num)
    have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 2
    rwa [Real.sq_sqrt (ha i)] at hs
  · simp only [Set.indicator_of_notMem hy, le_refl]

/-- Two-sided cap-mass estimates remove the cap weights from the analytic
packet estimate. The resulting coefficient is kept explicit for scaling. -/
theorem tubeOverlap_bound_of_packet_bound {n m : ℕ} (δ : ℝ)
    (v x : Fin m → Space n) {q C L U : ℝ} (hq : 0 < q) (hC : 0 ≤ C) (hL : 0 < L)
    (hU : 0 ≤ U)
    (hlower : ∀ i, L ≤ (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i)))
    (hupper : ∀ i, (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i)) ≤ U)
    (hpacket : ∀ c : Fin m → ℂ,
      Integrable (fun y ↦ packetTubeOverlap δ v x c y ^ (q / 2)) volume ∧
      (∫ y, packetTubeOverlap δ v x c y ^ (q / 2)) ≤
        (δ ^ 2) ^ n * (C ^ q * ∑ i, ‖c i‖ ^ q *
          (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i))))
    (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∫ y, tubeOverlap δ v x a y ^ (q / 2)) ^ (1 / (q / 2)) ≤
      ((δ ^ 2) ^ n * C ^ q * U * (2 / L) ^ q) ^ (1 / (q / 2)) *
        (∑ i, a i ^ (q / 2)) ^ (1 / (q / 2)) := by
  let c : Fin m → ℂ := fun i ↦ ((2 / L * Real.sqrt (a i) : ℝ) : ℂ)
  have hs : 0 < q / 2 := by linarith
  have hψ := memLp_tubeOverlap δ v x a (ENNReal.ofReal (q / 2))
  have hint : Integrable (fun y ↦ tubeOverlap δ v x a y ^ (q / 2)) volume := by
    have hi := hψ.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hs).ne' ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hs.le,
      Real.norm_of_nonneg (tubeOverlap_nonneg δ v x a ha _)] using hi
  obtain ⟨hpacketInt, hpacketBound⟩ := hpacket c
  have hinput : (∑ i, ‖c i‖ ^ q * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i))) ≤
      ((2 / L) ^ q * U) * ∑ i, a i ^ (q / 2) := by
    simp only [c, scaled_sqrt_rpow (ha _) hL]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hai := ha i
    calc
      (2 / L) ^ q * a i ^ (q / 2) * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i)) ≤
          (2 / L) ^ q * a i ^ (q / 2) * U :=
        mul_le_mul_of_nonneg_left (hupper i) (by positivity)
      _ = _ := by ring
  have hpow : (∫ y, tubeOverlap δ v x a y ^ (q / 2)) ≤
      ((δ ^ 2) ^ n * C ^ q * U * (2 / L) ^ q) * ∑ i, a i ^ (q / 2) := by
    calc
      (∫ y, tubeOverlap δ v x a y ^ (q / 2)) ≤
          ∫ y, packetTubeOverlap δ v x c y ^ (q / 2) :=
        integral_mono hint hpacketInt (fun y ↦ Real.rpow_le_rpow
          (tubeOverlap_nonneg δ v x a ha y)
          (tubeOverlap_le_scaled_packetTubeOverlap δ v x a ha hL hlower y) hs.le)
      _ ≤ (δ ^ 2) ^ n * (C ^ q * ∑ i, ‖c i‖ ^ q *
          (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i))) := hpacketBound
      _ ≤ (δ ^ 2) ^ n * (C ^ q * (((2 / L) ^ q * U) * ∑ i, a i ^ (q / 2))) := by
        gcongr
      _ = _ := by ring
  have hresult := Real.rpow_le_rpow
    (integral_nonneg fun y ↦ Real.rpow_nonneg (tubeOverlap_nonneg δ v x a ha y) _) hpow
    (le_of_lt (one_div_pos.mpr hs))
  rwa [Real.mul_rpow (by positivity)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (ha i) _)] at hresult

theorem double_dual_gt_critical {n : ℕ} (hn : 2 ≤ n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (hpn : p < n) : OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n < 2 * q := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold OAI.Analysis.Fourier.LocalSmoothing.criticalExponent
  rw [div_lt_iff₀ (by linarith : 0 < (n : ℝ) - 1)]
  have h := mul_lt_mul_of_pos_right hpn hpq.symm.sub_one_pos
  have heq := hpq.mul_eq_add
  nlinarith

/-- Restriction controls the finite vector of tube integrals in the full
range `1 < p < n`. The remaining geometric inputs are just lower and upper
cap-mass constants, with their exact scale dependence retained. -/
theorem restriction_implies_finite_tube_integrals_with_cap_bounds
    (hR : OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture) (n : ℕ) (hn : 2 ≤ n)
    {p q : ℝ} (hpq : p.HolderConjugate q) (hpn : p < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ →
      ∀ (v x : Fin m → Space n), (∀ i, ‖v i‖ = 1) →
      (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
      ∀ L U : ℝ, 0 < L → 0 ≤ U →
      (∀ i, L ≤ (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i))) →
      (∀ i, (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i)) ≤ U) →
      ∀ f : Space n → ℂ, MemLp f (ENNReal.ofReal p) volume →
      (∑ i, (∫ y in OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) (x i), ‖f y‖) ^ p) ^ (1 / p) ≤
        ((δ ^ 2) ^ n * C ^ (2 * q) * U * (2 / L) ^ (2 * q)) ^ (1 / q) *
          (∫ y, ‖f y‖ ^ p) ^ (1 / p) := by
  obtain ⟨C, hC, hbound⟩ := restriction_implies_diagonal_packet_bound hR n hn
    (double_dual_gt_critical hn hpq hpn)
  refine ⟨C, hC, ?_⟩
  intro m δ hδ v x hv hsep L U hL hU hlower hupper f hf
  apply finite_set_integrals_of_overlap (μ := (volume : Measure (Space n))) hpq (by positivity)
    (fun i ↦ OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) (x i))
    (fun i ↦ measurableSet_tube _ _ _) (fun i ↦ volume_tube_lt_top _ _ _) ?_ hf
  intro a ha
  refine ⟨memLp_tubeOverlap δ v x a (ENNReal.ofReal q), ?_⟩
  have hhalf : 2 * q / 2 = q := by ring
  have h := tubeOverlap_bound_of_packet_bound δ v x (mul_pos (by norm_num) hpq.symm.pos)
    hC.le hL hU hlower hupper (fun c ↦ hbound m δ hδ v x c hv hsep) a ha
  simpa only [hhalf, tubeOverlap] using h

end OAI.MeasureTheory.Kakeya
