import OAI.MeasureTheory.Kakeya.Measurability
import Mathlib.Topology.MetricSpace.CoveringNumbers

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal NNReal Pointwise

noncomputable section
namespace OAI.MeasureTheory.Kakeya

/-- A compact set admits a finite separated net. -/
theorem compact_finite_separated_net {E : Type*} [MetricSpace E]
    {A : Set E} (hA : IsCompact A) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (m : ℕ) (v : Fin m → E), (∀ i, v i ∈ A) ∧
      (∀ i j, i ≠ j → δ < dist (v i) (v j)) ∧
      ∀ y ∈ A, ∃ i, dist y (v i) ≤ δ := by
  let ε : ℝ≥0 := ⟨δ, hδ.le⟩
  have hε : ε ≠ 0 := fun h ↦ hδ.ne' (congrArg (fun a : ℝ≥0 ↦ (a : ℝ)) h)
  obtain ⟨N, _, hNfin, hNcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact (ε := ε / 2) (by positivity) hA
  have hpack : Metric.packingNumber ε A ≠ ⊤ := by
    apply ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hNfin)
    have h := (Metric.packingNumber_two_mul_le_externalCoveringNumber (ε / 2) A).trans
      hNcover.externalCoveringNumber_le_encard
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ≥0) ≠ 0)] using h
  let C := Metric.maximalSeparatedSet ε A
  have hCfin : C.Finite := Set.encard_ne_top_iff.mp (by
    change (Metric.maximalSeparatedSet ε A).encard ≠ ⊤
    rw [Metric.encard_maximalSeparatedSet hpack]
    exact hpack)
  let : Fintype C := hCfin.fintype
  let e := (Fintype.equivFin C).symm
  refine ⟨Fintype.card C, fun i ↦ (e i).val, ?_, ?_, ?_⟩
  · intro i
    exact Metric.maximalSeparatedSet_subset (e i).property
  · intro i j hij
    have hne : (e i).val ≠ (e j).val := fun h ↦ hij (e.injective (Subtype.ext h))
    have h := Metric.isSeparated_maximalSeparatedSet (e i).property (e j).property hne
    rw [← ENNReal.ofReal_coe_nnreal, edist_dist] at h
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hδ.le).mp h
  · intro y hy
    obtain ⟨z, hz, hdist⟩ := Metric.isCover_maximalSeparatedSet hpack hy
    refine ⟨e.symm ⟨z, hz⟩, ?_⟩
    change edist y z ≤ (ε : ℝ≥0∞) at hdist
    rw [← ENNReal.ofReal_coe_nnreal, edist_dist] at hdist
    simpa using (ENNReal.ofReal_le_ofReal_iff hδ.le).mp hdist

theorem unit_sphere_finite_separated_net {n : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    ∃ (m : ℕ) (v : Fin m → Space n), (∀ i, ‖v i‖ = 1) ∧
      (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) ∧
      ∀ y : Space n, ‖y‖ = 1 → ∃ i, dist y (v i) ≤ δ := by
  obtain ⟨m, v, hv, hsep, hcover⟩ :=
    compact_finite_separated_net (isCompact_sphere (0 : Space n) 1) hδ
  refine ⟨m, v, ?_, fun i j hij ↦ (hsep i j hij).le, ?_⟩
  · intro i
    simpa using hv i
  · intro y hy
    exact hcover y (by simpa using hy)

/-- Dilation of a tube expands its transverse radius, and its longer axis
contains the original unit axis. -/
theorem tube_four_mul_subset_smul {n : ℕ} {δ : ℝ} (v : Space n) :
    OAI.MeasureTheory.Kakeya.tube (4 * δ) v 0 ⊆ (4 : ℝ) • OAI.MeasureTheory.Kakeya.tube δ v 0 := by
  intro y hy
  obtain ⟨t, ht, hyt⟩ := mem_tube_iff.mp hy
  refine Set.mem_smul_set.mpr ⟨(1 / 4 : ℝ) • y, ?_, by simp [smul_smul]⟩
  apply mem_tube_iff.mpr
  refine ⟨t / 4, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
  have heq : (1 / 4 : ℝ) • y - ((0 : Space n) + (t / 4) • v) =
      (1 / 4 : ℝ) • (y - ((0 : Space n) + t • v)) := by
    simp [smul_sub, smul_smul, div_eq_mul_inv, mul_comm]
  rw [dist_eq_norm, heq, norm_smul]
  rw [dist_eq_norm] at hyt
  norm_num at *
  linarith

theorem volume_tube_four_mul_le {n : ℕ} (δ : ℝ) (v x : Space n) :
    volume (OAI.MeasureTheory.Kakeya.tube (4 * δ) v x) ≤ ENNReal.ofReal ((4 : ℝ) ^ n) * volume (OAI.MeasureTheory.Kakeya.tube δ v x) := by
  rw [volume_tube_center_eq, volume_tube_center_eq δ]
  calc
    _ ≤ volume ((4 : ℝ) • OAI.MeasureTheory.Kakeya.tube δ v 0) := measure_mono (tube_four_mul_subset_smul v)
    _ = _ := by simp [Measure.addHaar_smul, Space]

theorem volume_tube_near_direction {n : ℕ} {δ : ℝ} {ω v : Space n}
    (hωv : dist ω v ≤ δ) (x : Space n) :
    volume (OAI.MeasureTheory.Kakeya.tube (2 * δ) v x) ≤
      ENNReal.ofReal ((4 : ℝ) ^ n) * volume (OAI.MeasureTheory.Kakeya.tube δ ω x) := by
  have hi : OAI.MeasureTheory.Kakeya.tube (δ / 2) v x ⊆ OAI.MeasureTheory.Kakeya.tube δ ω x := by
    have h := tube_direction_inclusion (δ := δ / 2) (ω := v) (v := ω) (x := x)
      (by simpa only [dist_comm] using hωv)
    simpa only [add_halves] using h
  calc
    _ ≤ ENNReal.ofReal ((4 : ℝ) ^ n) * volume (OAI.MeasureTheory.Kakeya.tube (δ / 2) v x) := by
      have heq : 4 * (δ / 2) = 2 * δ := by ring
      simpa only [heq] using volume_tube_four_mul_le (δ / 2) v x
    _ ≤ _ := by gcongr

theorem ennreal_div_le_mul_div {a b A B c : ℝ≥0∞}
    (hA : A ≠ 0) (hA' : A ≠ ∞) (hB : B ≠ 0) (hB' : B ≠ ∞)
    (hab : a ≤ b) (hvol : B ≤ c * A) : a / A ≤ c * (b / B) := by
  apply (ENNReal.div_le_iff hA hA').mpr
  calc
    a ≤ b := hab
    _ = (b / B) * B := (ENNReal.div_mul_cancel hB hB').symm
    _ ≤ (b / B) * (c * A) := by gcongr
    _ = _ := by ring

/-- Nearby directions have comparable maximal averages, with a uniform
dimensional constant obtained directly by tube dilation. -/
theorem kakeyaMaximal_near_direction {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (f : Space n → ℂ) {ω v : Space n} (hωv : dist ω v ≤ δ) :
    OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f ω ≤ ENNReal.ofReal ((4 : ℝ) ^ n) * OAI.MeasureTheory.Kakeya.kakeyaMaximal (2 * δ) f v := by
  apply iSup_le
  intro x
  calc
    _ ≤ ENNReal.ofReal ((4 : ℝ) ^ n) *
        ((∫⁻ y in OAI.MeasureTheory.Kakeya.tube (2 * δ) v x, ‖f y‖ₑ) / volume (OAI.MeasureTheory.Kakeya.tube (2 * δ) v x)) := by
      apply ennreal_div_le_mul_div
        (volume_tube_pos hδ ω x).ne' (volume_tube_lt_top δ ω x).ne
        (volume_tube_pos (by linarith) v x).ne' (volume_tube_lt_top (2 * δ) v x).ne
      · exact lintegral_mono_set (tube_direction_inclusion_double hδ.le hωv)
      · exact volume_tube_near_direction hωv x
    _ ≤ _ := mul_le_mul' le_rfl (le_iSup
      (fun x : Space n ↦ (∫⁻ y in OAI.MeasureTheory.Kakeya.tube (2 * δ) v x, ‖f y‖ₑ) /
        volume (OAI.MeasureTheory.Kakeya.tube (2 * δ) v x)) x)

end OAI.MeasureTheory.Kakeya
