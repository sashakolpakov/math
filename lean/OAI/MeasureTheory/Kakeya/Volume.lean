import OAI.Analysis.Fourier.Restriction.Geometry

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal Pointwise

noncomputable section
namespace OAI.MeasureTheory.Kakeya

theorem preimage_add_tube_center {n : ℕ} (δ : ℝ) (v x : Space n) :
    (fun y ↦ x + y) ⁻¹' OAI.MeasureTheory.Kakeya.tube δ v x = OAI.MeasureTheory.Kakeya.tube δ v 0 := by
  ext y
  simp only [mem_preimage, mem_tube_iff, zero_add, dist_add_left]

theorem volume_tube_center_eq {n : ℕ} (δ : ℝ) (v x : Space n) :
    volume (OAI.MeasureTheory.Kakeya.tube δ v x) = volume (OAI.MeasureTheory.Kakeya.tube δ v 0) := by
  have h := measure_preimage_add (volume : Measure (Space n)) x (OAI.MeasureTheory.Kakeya.tube δ v x)
  rw [preimage_add_tube_center] at h
  exact h.symm

theorem volume_real_tube_center_eq {n : ℕ} (δ : ℝ) (v x : Space n) :
    volume.real (OAI.MeasureTheory.Kakeya.tube δ v x) = volume.real (OAI.MeasureTheory.Kakeya.tube δ v 0) := by
  exact congrArg ENNReal.toReal (volume_tube_center_eq δ v x)

/-- Translation of the cap cone embeds it into a tube with the same central direction. -/
theorem packetCap_cone_volume_le_tube {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (v x : Space n) :
    volume (Ioo (0 : ℝ) 1 • packetCap δ v) ≤ volume (OAI.MeasureTheory.Kakeya.tube δ v x) := by
  have hsub : Ioo (0 : ℝ) 1 • packetCap δ v ⊆
      (fun y ↦ (x - (1 / 2 : ℝ) • v) + y) ⁻¹' OAI.MeasureTheory.Kakeya.tube δ v x := by
    rintro y ⟨r, hr, ω, hω, rfl⟩
    apply mem_tube_iff.mpr
    refine ⟨r - 1 / 2, ⟨by linarith [hr.1], by linarith [hr.2]⟩, ?_⟩
    rw [dist_eq_norm]
    have hid : x - (1 / 2 : ℝ) • v + r • ω - (x + (r - 1 / 2) • v) =
        r • (ω - v) := by
      rw [smul_sub, sub_smul]
      abel
    rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1]
    have hle : r * ‖ω - v‖ ≤ δ / 32 := by
      calc r * ‖ω - v‖ ≤ 1 * (δ / 32) :=
             mul_le_mul hr.2.le hω.2 (norm_nonneg _) (by norm_num)
           _ = δ / 32 := one_mul _
    linarith
  have h := measure_mono (μ := (volume : Measure (Space n))) hsub
  rwa [measure_preimage_add] at h

theorem volume_tube_real_lower {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hv : ‖v‖ = 1) (x : Space n) :
    (volume.real (ball (0 : Space n) 1) / (2 * 512 ^ n)) * δ ^ (n - 1) ≤
      volume.real (OAI.MeasureTheory.Kakeya.tube δ v x) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm := ENNReal.toReal_mono (volume_tube_lt_top δ v x).ne
    (packetCap_cone_volume_le_tube hδ v x)
  change volume.real (Ioo (0 : ℝ) 1 • packetCap δ v) ≤ volume.real (OAI.MeasureTheory.Kakeya.tube δ v x) at hm
  have heq : (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ v) =
      (n : ℝ) * volume.real (Ioo (0 : ℝ) 1 • packetCap δ v) := by
    simp only [Measure.real, OAI.Analysis.Fourier.Restriction.sphereMeasure_packetCap, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hl := OAI.Analysis.Fourier.Restriction.packetCap_real_lower hn hδ hδone hv
  rw [heq] at hl
  apply (mul_le_mul_iff_right₀ hn').mp
  calc
    (n : ℝ) * (volume.real (ball (0 : Space n) 1) / (2 * 512 ^ n) * δ ^ (n - 1)) =
        ((n : ℝ) * volume.real (ball (0 : Space n) 1) / (2 * 512 ^ n)) * δ ^ (n - 1) := by ring
    _ ≤ (n : ℝ) * volume.real (Ioo (0 : ℝ) 1 • packetCap δ v) := hl
    _ ≤ (n : ℝ) * volume.real (OAI.MeasureTheory.Kakeya.tube δ v x) := mul_le_mul_of_nonneg_left hm hn'.le

theorem exists_volume_tube_real_lower {n : ℕ} (hn : 1 ≤ n) :
    ∃ c : ℝ, 0 < c ∧ ∀ (δ : ℝ) (v x : Space n), 0 < δ → δ ≤ 1 → ‖v‖ = 1 →
      c * δ ^ (n - 1) ≤ volume.real (OAI.MeasureTheory.Kakeya.tube δ v x) := by
  refine ⟨volume.real (ball (0 : Space n) 1) / (2 * 512 ^ n), ?_, ?_⟩
  · have hv : 0 < volume.real (ball (0 : Space n) 1) :=
      ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume _ zero_lt_one))
        measure_ball_lt_top.ne
    positivity
  · intro δ v x hδ hδone hv
    exact volume_tube_real_lower hn hδ hδone hv x

/-- A length-one tube is covered by at most floor(1/δ)+1 balls of radius 2δ. -/
theorem tube_subset_ball_cover {n : ℕ} {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hv : ‖v‖ = 1) (x : Space n) :
    OAI.MeasureTheory.Kakeya.tube δ v x ⊆ ⋃ j ∈ Finset.range (⌊1 / δ⌋₊ + 1),
      ball (x + ((j : ℝ) * δ - 1 / 2) • v) (2 * δ) := by
  intro y hy
  obtain ⟨t, ht, hyt⟩ := mem_tube_iff.mp hy
  let r : ℝ := t + 1 / 2
  have hr0 : 0 ≤ r := by dsimp [r]; linarith [ht.1]
  have hr1 : r ≤ 1 := by dsimp [r]; linarith [ht.2]
  let j : ℕ := ⌊r / δ⌋₊
  have hj : j < ⌊1 / δ⌋₊ + 1 :=
    Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right hr1 hδ.le))
  have hjlo : (j : ℝ) * δ ≤ r :=
    (le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg hr0 hδ.le))
  have hjhi : r < (j : ℝ) * δ + δ := by
    have h := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (r / δ))
    dsimp [j]
    linarith
  have hdist : dist (x + t • v) (x + ((j : ℝ) * δ - 1 / 2) • v) < δ := by
    rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, hv, mul_one, Real.norm_eq_abs]
    have hlo : 0 ≤ t - ((j : ℝ) * δ - 1 / 2) := by dsimp [r] at hjlo; linarith
    rw [abs_of_nonneg hlo]
    dsimp [r] at hjhi
    linarith
  exact mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hj,
    (dist_triangle y (x + t • v) _).trans_lt (by linarith)⟩

theorem volume_tube_upper_floor {n : ℕ} {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hv : ‖v‖ = 1) (x : Space n) :
    volume (OAI.MeasureTheory.Kakeya.tube δ v x) ≤ ((⌊1 / δ⌋₊ + 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal ((2 * δ) ^ n) * volume (ball (0 : Space n) 1) := by
  have h := (measure_mono (tube_subset_ball_cover hδ hv x)).trans
    (measure_biUnion_finset_le (μ := (volume : Measure (Space n))) _ _)
  simp_rw [(volume : Measure (Space n)).addHaar_ball_of_pos _
    (show 0 < 2 * δ by positivity)] at h
  simpa [Space, nsmul_eq_mul, mul_assoc] using h

theorem volume_tube_real_upper_floor {n : ℕ} {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hv : ‖v‖ = 1) (x : Space n) :
    volume.real (OAI.MeasureTheory.Kakeya.tube δ v x) ≤ (⌊1 / δ⌋₊ + 1 : ℝ) * ((2 * δ) ^ n) *
      volume.real (ball (0 : Space n) 1) := by
  have hfin : ((⌊1 / δ⌋₊ + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((2 * δ) ^ n) *
      volume (ball (0 : Space n) 1) ≠ ⊤ := by finiteness
  have h := ENNReal.toReal_mono hfin (volume_tube_upper_floor hδ hv x)
  simpa [ENNReal.toReal_mul, ENNReal.toReal_add,
    ENNReal.toReal_ofReal (show 0 ≤ (2 * δ) ^ n by positivity), Measure.real] using h

theorem volume_tube_real_upper {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hv : ‖v‖ = 1) (x : Space n) :
    volume.real (OAI.MeasureTheory.Kakeya.tube δ v x) ≤
      (2 ^ (n + 1) * volume.real (ball (0 : Space n) 1)) * δ ^ (n - 1) := by
  have hfloor := OAI.Analysis.Fourier.Restriction.capCover_count_upper hδ hδone
  have hvol : 0 ≤ volume.real (ball (0 : Space n) 1) := ENNReal.toReal_nonneg
  have hmono : (⌊1 / δ⌋₊ + 1 : ℝ) * ((2 * δ) ^ n) * volume.real (ball (0 : Space n) 1) ≤
      (2 / δ) * ((2 * δ) ^ n) * volume.real (ball (0 : Space n) 1) := by gcongr
  have hp : δ ^ n = δ ^ (n - 1) * δ := by
    simpa only [Nat.sub_add_cancel hn] using pow_succ δ (n - 1)
  have heq : (2 / δ) * ((2 * δ) ^ n) * volume.real (ball (0 : Space n) 1) =
      (2 ^ (n + 1) * volume.real (ball (0 : Space n) 1)) * δ ^ (n - 1) := by
    rw [mul_pow, hp, pow_succ]
    field_simp
  exact (volume_tube_real_upper_floor hδ hv x).trans (hmono.trans_eq heq)

theorem exists_volume_tube_real_upper {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ) (v x : Space n), 0 < δ → δ ≤ 1 → ‖v‖ = 1 →
      volume.real (OAI.MeasureTheory.Kakeya.tube δ v x) ≤ C * δ ^ (n - 1) := by
  refine ⟨2 ^ (n + 1) * volume.real (ball (0 : Space n) 1), ?_, ?_⟩
  · have hv : 0 < volume.real (ball (0 : Space n) 1) :=
      ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume _ zero_lt_one)) measure_ball_lt_top.ne
    positivity
  · intro δ v x hδ hδone hv
    exact volume_tube_real_upper hn hδ hδone hv x

end OAI.MeasureTheory.Kakeya
