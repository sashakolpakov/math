import OAI.MeasureTheory.Kakeya.Scaling
import OAI.MeasureTheory.Kakeya.Measurability

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal BigOperators

noncomputable section
namespace OAI.MeasureTheory.Kakeya

theorem ennreal_rpow_iSup {ι : Type*} (f : ι → ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (⨆ i, f i) ^ p = ⨆ i, f i ^ p :=
  (ENNReal.orderIsoRpow p hp).map_iSup f

/-- Each direction has its own independently chosen tube center. -/
theorem finite_power_sup_le {m : ℕ} {X : Type*} [Nonempty X]
    (F : Fin m → X → ℝ≥0∞) {p : ℝ} (hp : 0 < p) {B : ℝ≥0∞}
    (h : ∀ x : Fin m → X, ∑ i, F i (x i) ^ p ≤ B) :
    ∑ i, (⨆ x, F i x) ^ p ≤ B := by
  simp_rw [ennreal_rpow_iSup _ hp]
  rw [finsetSum_iSup_independent]
  exact iSup_le h

theorem normalized_finite_moment_le {m : ℕ} (I : Fin m → ℝ)
    (J : Fin m → ℝ≥0∞) {p k B : ℝ} (hp : 0 < p) (hk : 0 < k)
    (hB : 0 ≤ B) (hI : ∀ i, 0 ≤ I i)
    (hJ : ∀ i, J i ≤ ENNReal.ofReal (I i / k))
    (hbound : (∑ i, I i ^ p) ^ (1 / p) ≤ B) :
    ∑ i, J i ^ p ≤ ENNReal.ofReal ((B / k) ^ p) := by
  have hsum : 0 ≤ ∑ i, I i ^ p := Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (hI i) _
  have hs : ∑ i, I i ^ p ≤ B ^ p := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hsum _) hbound hp.le
    simpa only [← Real.rpow_mul hsum, one_div_mul_cancel hp.ne', Real.rpow_one] using h
  calc
    ∑ i, J i ^ p ≤ ∑ i, ENNReal.ofReal ((I i / k) ^ p) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← ENNReal.ofReal_rpow_of_nonneg (div_nonneg (hI i) hk.le) hp.le]
      exact ENNReal.rpow_le_rpow (hJ i) hp.le
    _ = ENNReal.ofReal ((∑ i, I i ^ p) / k ^ p) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦
        Real.rpow_nonneg (div_nonneg (hI i) hk.le) _)]
      congr 1
      simp_rw [Real.div_rpow (hI _) hk.le]
      rw [Finset.sum_div]
    _ ≤ ENNReal.ofReal (B ^ p / k ^ p) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hs (Real.rpow_nonneg hk.le _))
    _ = ENNReal.ofReal ((B / k) ^ p) := by rw [Real.div_rpow hB hk.le]

/-- A uniform vector bound for tube integrals controls the actual supremum
over all centers, without any attainment or countability assumption. -/
theorem finite_kakeya_moment_of_integral_bound {n m : ℕ} {δ p k B : ℝ}
    (hp : 1 ≤ p) (hk : 0 < k) (hB : 0 ≤ B) (v : Fin m → Space n)
    (f : Space n → ℂ) (hf : MemLp f (ENNReal.ofReal p) volume)
    (hvol : ∀ i x, ENNReal.ofReal k ≤ volume (OAI.MeasureTheory.Kakeya.tube δ (v i) x))
    (hbound : ∀ x : Fin m → Space n,
      (∑ i, (∫ y in OAI.MeasureTheory.Kakeya.tube δ (v i) (x i), ‖f y‖) ^ p) ^ (1 / p) ≤ B) :
    ∑ i, OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f (v i) ^ p ≤ ENNReal.ofReal ((B / k) ^ p) := by
  apply finite_power_sup_le (fun i x ↦ tubeMass δ f (v i) x / volume (OAI.MeasureTheory.Kakeya.tube δ (v i) x))
    (by linarith : 0 < p)
  intro x
  apply normalized_finite_moment_le
    (fun i ↦ ∫ y in OAI.MeasureTheory.Kakeya.tube δ (v i) (x i), ‖f y‖)
    (fun i ↦ tubeMass δ f (v i) (x i) / volume (OAI.MeasureTheory.Kakeya.tube δ (v i) (x i)))
    (by linarith) hk hB (fun i ↦ integral_nonneg fun y ↦ norm_nonneg (f y))
    _ (hbound x)
  intro i
  have hfin : IsFiniteMeasure (volume.restrict (OAI.MeasureTheory.Kakeya.tube δ (v i) (x i))) :=
    ⟨by simpa using volume_tube_lt_top δ (v i) (x i)⟩
  have hi : IntegrableOn f (OAI.MeasureTheory.Kakeya.tube δ (v i) (x i)) volume :=
    (hf.mono_measure Measure.restrict_le_self).integrable (ENNReal.one_le_ofReal.mpr hp)
  have heq : tubeMass δ f (v i) (x i) =
      ENNReal.ofReal (∫ y in OAI.MeasureTheory.Kakeya.tube δ (v i) (x i), ‖f y‖) :=
    (ofReal_integral_norm_eq_lintegral_enorm hi).symm
  rw [heq, ENNReal.ofReal_div_of_pos hk]
  exact ENNReal.div_le_div_left (hvol i (x i)) _

/-- Restriction implies a scale-explicit discrete estimate for the genuine
Kakeya maximal function on every separated family of unit directions. -/
theorem restriction_implies_discrete_kakeya
    (hR : OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture) (n : ℕ) (hn : 2 ≤ n)
    {p q : ℝ} (hpq : p.HolderConjugate q) (hpn : p < n) :
    ∃ D : ℝ, 0 < D ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ v : Fin m → Space n, (∀ i, ‖v i‖ = 1) →
      (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
      ∀ f : Space n → ℂ, MemLp f (ENNReal.ofReal p) volume →
      ∑ i, OAI.MeasureTheory.Kakeya.kakeyaMaximal (2 * δ) f (v i) ^ p ≤
        ENNReal.ofReal ((D * δ ^ ((2 * (n : ℝ) + (n - 1 : ℕ)) / q -
          3 * (n - 1 : ℕ)) * (∫ y, ‖f y‖ ^ p) ^ (1 / p)) ^ p) := by
  obtain ⟨A, hA, hraw⟩ := restriction_implies_finite_tube_integrals hR n hn hpq hpn
  obtain ⟨c, hc, hvolume⟩ := exists_volume_tube_real_lower (n := n) (by omega)
  refine ⟨A / c, div_pos hA hc, ?_⟩
  intro m δ hδ hδone v hv hsep f hf
  have hvol (i : Fin m) (x : Space n) :
      ENNReal.ofReal (c * δ ^ (n - 1)) ≤ volume (OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) x) := by
    calc
      _ ≤ ENNReal.ofReal (volume.real (OAI.MeasureTheory.Kakeya.tube δ (v i) x)) :=
        ENNReal.ofReal_le_ofReal (hvolume δ (v i) x hδ hδone (hv i))
      _ = volume (OAI.MeasureTheory.Kakeya.tube δ (v i) x) :=
        ENNReal.ofReal_toReal (volume_tube_lt_top δ (v i) x).ne
      _ ≤ volume (OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) x) :=
        measure_mono (tube_mono (by linarith) (v i) x)
  have h := finite_kakeya_moment_of_integral_bound hpq.lt.le
    (by positivity : 0 < c * δ ^ (n - 1))
    (by positivity : 0 ≤ A * δ ^ ((2 * (n : ℝ) + (n - 1 : ℕ)) / q -
      2 * (n - 1 : ℕ)) * (∫ y, ‖f y‖ ^ p) ^ (1 / p))
    v f hf hvol (fun x ↦ hraw m δ hδ hδone v x hv hsep f hf)
  have heq : (A * δ ^ ((2 * (n : ℝ) + (n - 1 : ℕ)) / q - 2 * (n - 1 : ℕ)) *
      (∫ y, ‖f y‖ ^ p) ^ (1 / p)) / (c * δ ^ (n - 1)) =
      (A / c) * δ ^ ((2 * (n : ℝ) + (n - 1 : ℕ)) / q - 3 * (n - 1 : ℕ)) *
        (∫ y, ‖f y‖ ^ p) ^ (1 / p) := by
    have he : (2 * (n : ℝ) + (n - 1 : ℕ)) / q - 3 * (n - 1 : ℕ) =
        ((2 * (n : ℝ) + (n - 1 : ℕ)) / q - 2 * (n - 1 : ℕ)) - (n - 1 : ℕ) := by ring
    rw [he]
    conv_rhs => rw [Real.rpow_sub hδ, Real.rpow_natCast]
    ring
  simpa only [heq] using h

end OAI.MeasureTheory.Kakeya
