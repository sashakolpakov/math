import OAI.MeasureTheory.Kakeya.CapReduction
import OAI.MeasureTheory.Kakeya.Volume

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section
namespace OAI.MeasureTheory.Kakeya

/-- The union of the radius-`2δ` tubes appearing in the overlap estimate. -/
def tubeUnion {n m : ℕ} (δ : ℝ) (v x : Fin m → Space n) : Set (Space n) :=
  ⋃ i, OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) (x i)

theorem measurableSet_tubeUnion {n m : ℕ} (δ : ℝ) (v x : Fin m → Space n) :
    MeasurableSet (tubeUnion δ v x) :=
  MeasurableSet.iUnion fun i ↦ measurableSet_tube _ (v i) (x i)

theorem volume_tubeUnion_lt_top {n m : ℕ} (δ : ℝ) (v x : Fin m → Space n) :
    volume (tubeUnion δ v x) < ∞ := by
  apply lt_of_le_of_lt (measure_iUnion_le _)
  rw [tsum_fintype]
  exact ENNReal.sum_lt_top.mpr fun i _ ↦ volume_tube_lt_top _ (v i) (x i)

/-- Hölder bounds total multiplicity by the volume occupied by a finite tube family. -/
theorem tubeOverlap_integral_le_volume {n m : ℕ} (δ : ℝ)
    (v x : Fin m → Space n) {p q : ℝ} (hpq : p.HolderConjugate q) :
    (∫ y, tubeOverlap δ v x (fun _ ↦ 1) y) ≤
      volume.real (tubeUnion δ v x) ^ (1 / p) *
        (∫ y, tubeOverlap δ v x (fun _ ↦ 1) y ^ q) ^ (1 / q) := by
  let A := tubeUnion δ v x
  let g : Space n → ℝ := A.indicator (fun _ ↦ 1)
  have hg : MemLp g (ENNReal.ofReal p) volume :=
    memLp_indicator_const _ (measurableSet_tubeUnion δ v x) 1
      (Or.inr (volume_tubeUnion_lt_top δ v x).ne)
  have hprod (y : Space n) : g y * tubeOverlap δ v x (fun _ ↦ 1) y =
      tubeOverlap δ v x (fun _ ↦ 1) y := by
    by_cases hy : y ∈ A
    · simp [g, hy]
    · have hzero (i : Fin m) : y ∉ OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) (x i) := by
        intro hi
        exact hy (mem_iUnion.mpr ⟨i, hi⟩)
      simp [g, hy, tubeOverlap, hzero]
  have hpower : (fun y ↦ g y ^ p) = g := by
    funext y
    by_cases hy : y ∈ A
    · simp [g, hy]
    · simp [g, hy, Real.zero_rpow hpq.ne_zero]
  have hmass : (∫ y, g y ^ p) = volume.real A := by
    rw [hpower]
    dsimp [g]
    rw [integral_indicator (measurableSet_tubeUnion δ v x)]
    simp [A]
  have H := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall fun y ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) y)
    (Filter.Eventually.of_forall (tubeOverlap_nonneg δ v x (fun _ ↦ 1) (fun _ ↦ zero_le_one)))
    hg (memLp_tubeOverlap δ v x (fun _ ↦ 1) (ENNReal.ofReal q))
  change (∫ y, g y * tubeOverlap δ v x (fun _ ↦ 1) y) ≤
    (∫ y, g y ^ p) ^ (1 / p) *
      (∫ y, tubeOverlap δ v x (fun _ ↦ 1) y ^ q) ^ (1 / q) at H
  simpa only [hprod, hmass] using H

/-- Integrating multiplicity counts every tube with its full volume. -/
theorem integral_tubeOverlap_one {n m : ℕ} (δ : ℝ) (v x : Fin m → Space n) :
    (∫ y, tubeOverlap δ v x (fun _ ↦ 1) y) =
      ∑ i, volume.real (OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) (x i)) := by
  unfold tubeOverlap
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator (measurableSet_tube _ _ _)]
    simp
  · intro i _
    exact memLp_one_iff_integrable.mp (memLp_indicator_const 1
      (measurableSet_tube _ _ _) (1 : ℝ) (Or.inr (volume_tube_lt_top _ _ _).ne))

/-- Algebraic form of the critical Hölder lower bound, including zero mass. -/
theorem volume_lower_of_critical_holder {n : ℕ} (hn : 2 ≤ n)
    {c K M V : ℝ} (hc : 0 ≤ c) (hK : 0 < K) (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hbound : c * M ≤ V ^ (1 / (n : ℝ)) *
      (K * M ^ (1 / ((n : ℝ) / ((n : ℝ) - 1))))) :
    c ^ n * M / K ^ n ≤ V := by
  by_cases hzero : M = 0
  · simpa [hzero] using hV
  have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hzero)
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hfrac : M / M ^ (1 / ((n : ℝ) / ((n : ℝ) - 1))) =
      M ^ (1 / (n : ℝ)) := by
    conv_lhs => lhs; rw [← Real.rpow_one M]
    rw [← Real.rpow_sub hMpos]
    congr 1
    field_simp
    ring
  have hbase : c / K * M ^ (1 / (n : ℝ)) ≤ V ^ (1 / (n : ℝ)) := by
    rw [← hfrac]
    calc
      c / K * (M / M ^ (1 / ((n : ℝ) / ((n : ℝ) - 1)))) =
          (c * M) / (K * M ^ (1 / ((n : ℝ) / ((n : ℝ) - 1)))) := by ring
      _ ≤ V ^ (1 / (n : ℝ)) :=
        (div_le_iff₀ (mul_pos hK (Real.rpow_pos_of_pos hMpos _))).mpr hbound
  have hroot (a : ℝ) (ha : 0 ≤ a) : (a ^ (1 / (n : ℝ))) ^ n = a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha,
      one_div_mul_cancel (ne_of_gt (lt_trans zero_lt_one hnR)), Real.rpow_one]
  have H := pow_le_pow_left₀ (mul_nonneg (div_nonneg hc hK.le) (Real.rpow_nonneg hM _)) hbase n
  rw [mul_pow, div_pow, hroot M hM, hroot V hV] at H
  convert H using 1
  ring

/-- A critical overlap bound gives a quantitative lower bound for the occupied
volume. The constant is dimension-only, and no restriction on the tube centers
is needed. `K` may in particular be a power of `1 + log (1/δ)`. -/
theorem tubeUnion_volume_lower_of_overlap (n : ℕ) (hn : 2 ≤ n) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (v x : Fin m → Space n), (∀ i, ‖v i‖ = 1) →
      ∀ K : ℝ, 0 < K →
      (∫ y, tubeOverlap δ v x (fun _ ↦ 1) y ^ ((n : ℝ) / ((n : ℝ) - 1))) ^
          (1 / ((n : ℝ) / ((n : ℝ) - 1))) ≤
        K * ((m : ℝ) * δ ^ (n - 1)) ^ (1 / ((n : ℝ) / ((n : ℝ) - 1))) →
      c * ((m : ℝ) * δ ^ (n - 1)) / K ^ n ≤ volume.real (tubeUnion δ v x) := by
  obtain ⟨a, ha, hvolume⟩ := exists_volume_tube_real_lower (n := n) (by omega)
  refine ⟨a ^ n, pow_pos ha _, ?_⟩
  intro m δ hδ hδone v x hv K hK hoverlap
  have hmass : a * ((m : ℝ) * δ ^ (n - 1)) ≤
      ∫ y, tubeOverlap δ v x (fun _ ↦ 1) y := by
    rw [integral_tubeOverlap_one]
    calc
      a * ((m : ℝ) * δ ^ (n - 1)) = ∑ _i : Fin m, a * δ ^ (n - 1) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ ≤ _ := Finset.sum_le_sum fun i _ ↦
        (hvolume δ (v i) (x i) hδ hδone (hv i)).trans
          (ENNReal.toReal_mono (volume_tube_lt_top _ _ _).ne
            (measure_mono (tube_mono (by linarith : δ ≤ 2 * δ) (v i) (x i))))
  apply volume_lower_of_critical_holder hn ha.le hK (by positivity) ENNReal.toReal_nonneg
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  exact hmass.trans ((tubeOverlap_integral_le_volume δ v x
    (Real.HolderConjugate.conjExponent hnR)).trans
      (mul_le_mul_of_nonneg_left hoverlap (Real.rpow_nonneg ENNReal.toReal_nonneg _)))

/-- A logarithmic critical overlap loss becomes an inverse logarithmic volume
bound. The exponent is multiplied only by the dimension. -/
theorem tubeUnion_logarithmic_volume_lower (n : ℕ) (hn : 2 ≤ n)
    (C : ℝ) (hC : 0 < C) (A : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (v x : Fin m → Space n), (∀ i, ‖v i‖ = 1) →
      (∫ y, tubeOverlap δ v x (fun _ ↦ 1) y ^ ((n : ℝ) / ((n : ℝ) - 1))) ^
          (1 / ((n : ℝ) / ((n : ℝ) - 1))) ≤
        (C * (1 + Real.log (1 / δ)) ^ A) *
          ((m : ℝ) * δ ^ (n - 1)) ^ (1 / ((n : ℝ) / ((n : ℝ) - 1))) →
      c * ((m : ℝ) * δ ^ (n - 1)) / (1 + Real.log (1 / δ)) ^ (n * A) ≤
        volume.real (tubeUnion δ v x) := by
  obtain ⟨b, hb, H⟩ := tubeUnion_volume_lower_of_overlap n hn
  refine ⟨b / C ^ n, div_pos hb (pow_pos hC _), ?_⟩
  intro m δ hδ hδone v x hv hoverlap
  have hlog : 0 < 1 + Real.log (1 / δ) := by
    have := Real.log_nonneg ((one_le_div hδ).mpr hδone)
    linarith
  have h := H m δ hδ hδone v x hv (C * (1 + Real.log (1 / δ)) ^ A)
    (mul_pos hC (pow_pos hlog _)) hoverlap
  rw [mul_pow, ← pow_mul, Nat.mul_comm A n] at h
  convert h using 1
  ring

/-- In three dimensions, a family with at least `δ⁻²` directions has occupied
volume bounded below by an inverse power of the logarithm. Direction separation
is needed only by the analytic overlap estimate supplied as the hypothesis. -/
theorem tubeUnion_three_dimensional_logarithmic_volume_lower
    (C : ℝ) (hC : 0 < C) (A : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (v x : Fin m → Space 3), (∀ i, ‖v i‖ = 1) → 1 ≤ (m : ℝ) * δ ^ 2 →
      (∫ y, tubeOverlap δ v x (fun _ ↦ 1) y ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
        (C * (1 + Real.log (1 / δ)) ^ A) * ((m : ℝ) * δ ^ 2) ^ (2 / 3 : ℝ) →
      c / (1 + Real.log (1 / δ)) ^ (3 * A) ≤ volume.real (tubeUnion δ v x) := by
  obtain ⟨c, hc, H⟩ := tubeUnion_logarithmic_volume_lower 3 (by omega) C hC A
  refine ⟨c, hc, ?_⟩
  intro m δ hδ hδone v x hv hdense hoverlap
  have hbound := H m δ hδ hδone v x hv (by norm_num at *; exact hoverlap)
  calc
    c / (1 + Real.log (1 / δ)) ^ (3 * A) ≤
        c * ((m : ℝ) * δ ^ 2) / (1 + Real.log (1 / δ)) ^ (3 * A) := by
      apply div_le_div_of_nonneg_right
      · nlinarith
      · have := Real.log_nonneg ((one_le_div hδ).mpr hδone)
        positivity
    _ ≤ _ := by simpa using hbound

end OAI.MeasureTheory.Kakeya
