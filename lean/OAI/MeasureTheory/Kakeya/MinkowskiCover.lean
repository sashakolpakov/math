import OAI.MeasureTheory.Kakeya.MinkowskiDefinitions
import OAI.MeasureTheory.Kakeya.DirectionNets

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace OAI.MeasureTheory.Kakeya

/-- The elementary volume-packing estimate for a separated finite net. -/
theorem separated_net_volume_bound {n m : ℕ} {r R : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (v : Fin m → Space n)
    (hv : ∀ i, ‖v i‖ ≤ R) (hsep : ∀ i j, i ≠ j → r < dist (v i) (v j)) :
    (m : ℝ≥0∞) * ENNReal.ofReal ((r / 2) ^ n) * volume (ball (0 : Space n) 1) ≤
      volume (ball (0 : Space n) (R + 1)) := by
  have hdis : Pairwise fun i j : Fin m => Disjoint (ball (v i) (r / 2)) (ball (v j) (r / 2)) := by
    intro i j hij
    apply ball_disjoint_ball
    linarith [hsep i j hij]
  have hvol : (∑ i : Fin m, volume (ball (v i) (r / 2))) ≤
      volume (ball (0 : Space n) (R + 1)) := by
    rw [← measure_biUnion_finset (fun i _ j _ hij => hdis hij) (fun _ _ => measurableSet_ball)]
    apply measure_mono
    intro x hx
    obtain ⟨i,_,hi⟩ := mem_iUnion₂.mp hx
    change dist x 0 < R + 1
    have hdist : dist x (v i) < r / 2 := hi
    have hn : dist (v i) 0 ≤ R := by simpa using hv i
    have := dist_triangle x (v i) 0
    linarith
  simp_rw [(volume : Measure (Space n)).addHaar_ball_of_pos _ (by positivity : 0 < r / 2)] at hvol
  simpa only [Space, finrank_euclideanSpace_fin, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_assoc] using hvol

/-- Every bounded Euclidean set has covering number `O(r^(-n))`.
No regularity or measurability of the set is required. -/
theorem bounded_coveringNumber_power_bound {n : ℕ} {F : Set (Space n)}
    (hF : Bornology.IsBounded F) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ r : ℝ≥0, 0 < r → r ≤ 1 →
      (coveringNumber r F : ℝ≥0∞) * (r : ℝ≥0∞) ^ n ≤ C := by
  classical
  obtain ⟨R,hR⟩ := hF.closure.subset_closedBall (0 : Space n)
  let V : ℝ≥0∞ := volume (ball (0 : Space n) 1)
  let a : ℝ≥0∞ := (1 / 4 : ℝ≥0∞) ^ n * V
  have hV : V ≠ 0 := (measure_ball_pos volume _ zero_lt_one).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  have ha : a ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hV
  have hat : a ≠ ⊤ := ENNReal.mul_ne_top (by finiteness) hVt
  refine ⟨volume (ball (0 : Space n) (R + 1)) / a, ENNReal.div_ne_top measure_ball_lt_top.ne ha, ?_⟩
  intro r hr hr1
  obtain ⟨m,v,hv,hsep,hcover⟩ := compact_finite_separated_net
    (isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure,hF.closure⟩)
    (by positivity : 0 < (r : ℝ) / 2)
  have hc : IsCover (r / 2) F (range v) := by
    intro x hx
    obtain ⟨i,hi⟩ := hcover x (subset_closure hx)
    refine ⟨v i, mem_range_self i, ?_⟩
    simpa [edist_dist, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)] using
      ENNReal.ofReal_le_ofReal hi
  have hcard : coveringNumber r F ≤ (m : ℕ∞) := by
    calc
      coveringNumber r F ≤ externalCoveringNumber (r / 2) F := by
        simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ≥0) ≠ 0)] using
          coveringNumber_two_mul_le_externalCoveringNumber (r / 2) F
      _ ≤ (range v).encard := hc.externalCoveringNumber_le_encard
      _ ≤ m := by
        simpa only [image_univ, encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin] using
          encard_image_le v (univ : Set (Fin m))
  have hm : (coveringNumber r F : ℝ≥0∞) ≤ m := by exact_mod_cast hcard
  have H := separated_net_volume_bound (by positivity : 0 < (r : ℝ) / 2)
    (by exact_mod_cast (show r / 2 ≤ 1 from (div_le_self (show 0 ≤ r by positivity) (by norm_num)).trans hr1))
    v (fun i => by simpa only [mem_closedBall, dist_zero_right] using hR (hv i)) hsep
  have he : ENNReal.ofReal (((r : ℝ) / 2 / 2) ^ n) = (r : ℝ≥0∞) ^ n * (1 / 4 : ℝ≥0∞) ^ n := by
    rw [show (r : ℝ) / 2 / 2 = (r : ℝ) * (1 / 4) by ring,
      mul_pow, ENNReal.ofReal_mul (pow_nonneg r.coe_nonneg _),
      ENNReal.ofReal_pow r.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
  rw [he] at H
  apply (ENNReal.le_div_iff_mul_le (Or.inl ha) (Or.inl hat)).mpr
  calc
    (coveringNumber r F : ℝ≥0∞) * (r : ℝ≥0∞) ^ n * a ≤ (m : ℝ≥0∞) * (r : ℝ≥0∞) ^ n * a := by gcongr
    _ ≤ volume (ball (0 : Space n) (R + 1)) := by simpa only [a, V, mul_assoc] using H

end OAI.MeasureTheory.Kakeya
