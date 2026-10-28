import OAI.MeasureTheory.Kakeya.Log.VolumeExtension
import Mathlib.MeasureTheory.Group.LIntegral

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal BigOperators

noncomputable section
namespace OAI.MeasureTheory.Kakeya

theorem volume_ball_center_eq_zero {n : ℕ} (z : Space n) (R : ℝ) :
    volume (ball z R) = volume (ball (0 : Space n) R) := by
  have he : (fun y : Space n ↦ z + y) ⁻¹' ball z R = ball (0 : Space n) R := by
    ext y
    simp only [mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
  have h := measure_preimage_add (volume : Measure (Space n)) z (ball z R)
  rw [he] at h
  exact h.symm

/-- Averaging intersections with translates of a ball counts each point by
exactly the volume of that ball. -/
theorem lintegral_volume_inter_ball {n : ℕ} (U : Set (Space n)) (R : ℝ) :
    (∫⁻ z : Space n, volume (U ∩ ball z R)) =
      volume U * volume (ball (0 : Space n) R) := by
  let F : Space n × Space n → ℝ≥0∞ :=
    {p | dist p.1 p.2 < R}.indicator (fun _ ↦ 1)
  have hF : Measurable F := by
    apply measurable_const.indicator
    exact (isOpen_lt (continuous_fst.dist continuous_snd) continuous_const).measurableSet
  have he (z y : Space n) : F (z, y) = (ball z R).indicator (fun _ ↦ (1 : ℝ≥0∞)) y := by
    simp [F, Set.indicator, dist_comm]
  have hi (z : Space n) : (∫⁻ y in U, F (z, y)) = volume (U ∩ ball z R) := by
    simp_rw [he]
    rw [lintegral_indicator measurableSet_ball, lintegral_const,
      Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_ball, inter_comm]
    simp
  have hj (y : Space n) : (∫⁻ z, F (z, y)) = volume (ball (0 : Space n) R) := by
    have he' : (fun z ↦ F (z, y)) = (ball y R).indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
      funext z
      simp [F, Set.indicator]
    rw [he', lintegral_indicator measurableSet_ball, lintegral_const,
      Measure.restrict_apply_univ, one_mul, volume_ball_center_eq_zero]
  calc
    _ = ∫⁻ z, ∫⁻ y in U, F (z, y) := by simp_rw [hi]
    _ = ∫⁻ y in U, ∫⁻ z, F (z, y) :=
      lintegral_lintegral_swap (μ := (volume : Measure (Space n)))
        (ν := volume.restrict U) hF.aemeasurable
    _ = _ := by simp_rw [hj]; simp [mul_comm]

/-- The average number of centers in a unit ball is the number of centers
times the volume of one unit ball. -/
theorem lintegral_ball_center_count {n m : ℕ} (x : Fin m → Space n) :
    (∫⁻ z, ∑ i, (ball (x i) 1).indicator (fun _ ↦ (1 : ℝ≥0∞)) z) =
      (m : ℝ≥0∞) * volume (ball (0 : Space n) 1) := by
  rw [lintegral_finsetSum]
  · simp_rw [lintegral_indicator measurableSet_ball, lintegral_const,
      Measure.restrict_apply_univ, one_mul, volume_ball_center_eq_zero]
    simp
  · intro i _
    exact measurable_const.indicator measurableSet_ball

/-- A lower bound in every translated observation ball can be integrated to
remove any boundedness assumption on the locations of the centers. -/
theorem global_mass_of_local_ball_mass {n m : ℕ} (x : Fin m → Space n)
    (U : Set (Space n)) (hU : volume U < ∞) {d : ℝ} (hd : 0 ≤ d)
    (hlocal : ∀ z : Space n,
      d * (∑ i, (ball (x i) 1).indicator (fun _ ↦ (1 : ℝ)) z) ≤
        volume.real (U ∩ ball z 4)) :
    d * (m : ℝ) * volume.real (ball (0 : Space n) 1) ≤
      volume.real U * volume.real (ball (0 : Space n) 4) := by
  have hcast (z : Space n) :
      ENNReal.ofReal (∑ i, (ball (x i) 1).indicator (fun _ ↦ (1 : ℝ)) z) =
        ∑ i, (ball (x i) 1).indicator (fun _ ↦ (1 : ℝ≥0∞)) z := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦
      Set.indicator_nonneg (fun _ _ ↦ zero_le_one) z)]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hz : z ∈ ball (x i) 1 <;> simp [hz]
  have H (z : Space n) :
      ENNReal.ofReal d * (∑ i, (ball (x i) 1).indicator (fun _ ↦ (1 : ℝ≥0∞)) z) ≤
        volume (U ∩ ball z 4) := by
    rw [← hcast, ← ENNReal.ofReal_mul hd]
    have hfin : volume (U ∩ ball z 4) ≠ ∞ :=
      ne_of_lt ((measure_mono inter_subset_left).trans_lt hU)
    exact (ENNReal.ofReal_le_ofReal (hlocal z)).trans_eq (ENNReal.ofReal_toReal hfin)
  have hint := lintegral_mono (μ := (volume : Measure (Space n))) H
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_ball_center_count, lintegral_volume_inter_ball] at hint
  have hfinite : volume U * volume (ball (0 : Space n) 4) ≠ ∞ :=
    (ENNReal.mul_lt_top hU measure_ball_lt_top).ne
  have hreal := ENNReal.toReal_mono hfinite hint
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hd, ENNReal.toReal_natCast,
    Measure.real, mul_assoc] using hreal

/-- Reindex the centers falling in one observation ball, translate them to the
unit ball, and compare their tube union with the original union. -/
theorem local_tubeUnion_volume_lower {n m : ℕ} {δ d : ℝ} (hδone : δ ≤ 1)
    (v x : Fin m → Space n) (hv : ∀ i, ‖v i‖ = 1)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (v i) (v j))
    (hlocal : ∀ (k : ℕ) (w a : Fin k → Space n),
      (∀ i, ‖w i‖ = 1) → (∀ i, ‖a i‖ ≤ 1) →
      (∀ i j, i ≠ j → δ ≤ dist (w i) (w j)) →
      d * (k : ℝ) ≤ volume.real (tubeUnion δ w a)) (z : Space n) :
    d * (∑ i, (ball (x i) 1).indicator (fun _ ↦ (1 : ℝ)) z) ≤
      volume.real (tubeUnion δ v x ∩ ball z 4) := by
  classical
  let s : Finset (Fin m) := Finset.univ.filter (fun i ↦ dist (x i) z < 1)
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let w : Fin (Fintype.card s) → Space n := fun i ↦ v (e.symm i).val
  let a : Fin (Fintype.card s) → Space n := fun i ↦ x (e.symm i).val - z
  have hw (i : Fin (Fintype.card s)) : ‖w i‖ = 1 := hv _
  have ha (i : Fin (Fintype.card s)) : ‖a i‖ ≤ 1 := by
    have hi := (Finset.mem_filter.mp (e.symm i).property).2
    exact (show ‖x (e.symm i).val - z‖ < 1 from hi).le
  have hs : ∀ i j, i ≠ j → δ ≤ dist (w i) (w j) := by
    intro i j hij
    apply hsep
    intro h
    exact hij (e.symm.injective (Subtype.ext h))
  have hsub : tubeUnion δ w a ⊆
      (fun y : Space n ↦ z + y) ⁻¹' (tubeUnion δ v x ∩ ball z 4) := by
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    have ho : z + y ∈ OAI.MeasureTheory.Kakeya.tube (2 * δ) (v (e.symm i).val) (x (e.symm i).val) := by
      obtain ⟨t, ht, hdist⟩ := mem_tube_iff.mp hi
      apply mem_tube_iff.mpr
      refine ⟨t, ht, ?_⟩
      have heq : x (e.symm i).val + t • v (e.symm i).val = z + (a i + t • w i) := by
        dsimp [a, w]
        abel
      rw [heq, dist_add_left]
      exact hdist
    have hball := tube_subset_ball (2 * δ) (w i) (a i) hi
    have hnorm : ‖y‖ < 4 := by
      have htri := norm_add_le (y - a i) (a i)
      rw [sub_add_cancel] at htri
      rw [mem_ball, dist_eq_norm, hw] at hball
      have hai := ha i
      linarith
    exact ⟨mem_iUnion.mpr ⟨(e.symm i).val, ho⟩, by
      simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left] using hnorm⟩
  have hmeasure := measure_mono (μ := (volume : Measure (Space n))) hsub
  rw [measure_preimage_add] at hmeasure
  have hfinite : volume (tubeUnion δ v x ∩ ball z 4) ≠ ∞ :=
    ((measure_mono inter_subset_left).trans_lt (volume_tubeUnion_lt_top δ v x)).ne
  have hresult := (hlocal _ w a hw ha hs).trans (ENNReal.toReal_mono hfinite hmeasure)
  have hcount : (∑ i, (ball (x i) 1).indicator (fun _ ↦ (1 : ℝ)) z) =
      (Fintype.card s : ℝ) := by
    rw [Fintype.card_coe]
    simp only [Set.indicator, mem_ball]
    simp_rw [dist_comm z]
    rw [← Finset.sum_filter]
    simp [s]
  rw [hcount]
  exact hresult

/-- A dimension-only change of constant extends a bounded-center tube-union
estimate to completely arbitrary centers. -/
theorem tubeUnion_volume_lower_globalize {n : ℕ} {δ d : ℝ}
    (hδone : δ ≤ 1) (hd : 0 ≤ d)
    (hlocal : ∀ (k : ℕ) (w a : Fin k → Space n),
      (∀ i, ‖w i‖ = 1) → (∀ i, ‖a i‖ ≤ 1) →
      (∀ i j, i ≠ j → δ ≤ dist (w i) (w j)) →
      d * (k : ℝ) ≤ volume.real (tubeUnion δ w a))
    (m : ℕ) (v x : Fin m → Space n) (hv : ∀ i, ‖v i‖ = 1)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) :
    (d * volume.real (ball (0 : Space n) 1) / volume.real (ball (0 : Space n) 4)) *
      (m : ℝ) ≤ volume.real (tubeUnion δ v x) := by
  have H := global_mass_of_local_ball_mass x (tubeUnion δ v x)
    (volume_tubeUnion_lt_top δ v x) hd
    (local_tubeUnion_volume_lower hδone v x hv hsep hlocal)
  have hball : 0 < volume.real (ball (0 : Space n) 4) :=
    ENNReal.toReal_pos (measure_ball_pos volume _ (by norm_num)).ne' measure_ball_lt_top.ne
  calc
    _ = (d * (m : ℝ) * volume.real (ball (0 : Space n) 1)) /
        volume.real (ball (0 : Space n) 4) := by ring
    _ ≤ _ := (div_le_iff₀ hball).mpr H

/-- Logarithmic critical extension controls the occupied volume of arbitrary
finite direction-separated tube arrangements, with no bound on their centers. -/
theorem local_critical_extension_logarithmic_tube_volume_global
    {n : ℕ} (hn : 2 ≤ n) (C : ℝ) (hC : 0 < C) (A : ℕ)
    (hext : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ g : Space n → ℂ, MemLp g (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) →
        MemLp (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
          (volume.restrict (Metric.ball (0 : Space n) (4 / δ ^ 2))) ∧
        eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
          (volume.restrict (Metric.ball (0 : Space n) (4 / δ ^ 2))) ≤
          ENNReal.ofReal (C * (1 + Real.log (1 / δ)) ^ A) *
            eLpNorm g (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (v x : Fin m → Space n), (∀ i, ‖v i‖ = 1) →
        (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
      c * ((m : ℝ) * δ ^ (n - 1)) / (1 + Real.log (1 / δ)) ^ (2 * n * A) ≤
        volume.real (tubeUnion δ v x) := by
  obtain ⟨a, ha, H⟩ := local_critical_extension_logarithmic_tube_volume hn C hC A hext
  have hball (r : ℝ) (hr : 0 < r) : 0 < volume.real (ball (0 : Space n) r) :=
    ENNReal.toReal_pos (measure_ball_pos volume _ hr).ne' measure_ball_lt_top.ne
  refine ⟨a * volume.real (ball (0 : Space n) 1) / volume.real (ball (0 : Space n) 4),
    div_pos (mul_pos ha (hball 1 zero_lt_one)) (hball 4 (by norm_num)), ?_⟩
  intro m δ hδ hδone v x hv hsep
  let d := a * δ ^ (n - 1) / (1 + Real.log (1 / δ)) ^ (2 * n * A)
  have hlog : 0 ≤ 1 + Real.log (1 / δ) := by
    have := Real.log_nonneg ((one_le_div hδ).mpr hδone)
    linarith
  have hd : 0 ≤ d := div_nonneg (mul_nonneg ha.le (pow_nonneg hδ.le _)) (pow_nonneg hlog _)
  have hlocal (k : ℕ) (w b : Fin k → Space n) (hw : ∀ i, ‖w i‖ = 1)
      (hb : ∀ i, ‖b i‖ ≤ 1) (hs : ∀ i j, i ≠ j → δ ≤ dist (w i) (w j)) :
      d * (k : ℝ) ≤ volume.real (tubeUnion δ w b) := by
    convert H k δ hδ hδone w b hw hb hs using 1
    dsimp [d]
    ring
  have hglobal := tubeUnion_volume_lower_globalize hδone hd hlocal m v x hv hsep
  convert hglobal using 1
  dsimp [d]
  ring

end OAI.MeasureTheory.Kakeya
