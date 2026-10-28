import OAI.MeasureTheory.Kakeya.Packets

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal Pointwise

noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- Polar normalization of the exact packet caps used in the restriction argument. -/
theorem sphereMeasure_packetCap {n : ℕ} (δ : ℝ) (v : Space n) :
    OAI.Analysis.Fourier.Restriction.sphereMeasure n (OAI.MeasureTheory.Kakeya.packetCap δ v) =
      (n : ℝ≥0∞) * volume (Ioo (0 : ℝ) 1 • OAI.MeasureTheory.Kakeya.packetCap δ v) := by
  have himage : (Subtype.val : sphere (0 : Space n) 1 → Space n) ''
      ((Subtype.val : sphere (0 : Space n) 1 → Space n) ⁻¹' OAI.MeasureTheory.Kakeya.packetCap δ v) =
      OAI.MeasureTheory.Kakeya.packetCap δ v := by
    apply Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hy
    · intro x hx
      refine ⟨⟨x, ?_⟩, hx, rfl⟩
      simpa only [mem_sphere, dist_zero_right] using hx.1
  rw [OAI.Analysis.Fourier.Restriction.sphereMeasure, Measure.map_apply measurable_subtype_coe (OAI.MeasureTheory.Kakeya.measurableSet_packetCap δ v),
    Measure.toSphere_apply' _ ((OAI.MeasureTheory.Kakeya.measurableSet_packetCap δ v).preimage measurable_subtype_coe),
    himage]
  simp [Space]

/-- A quantitative normalization estimate, avoiding differentiability of the norm. -/
theorem norm_normalize_sub_unit_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x v : E} (hx : x ≠ 0) (hv : ‖v‖ = 1) {r : ℝ} (hr : 0 < r) :
    r * ‖‖x‖⁻¹ • x - v‖ ≤ 2 * ‖x - r • v‖ := by
  let u : E := ‖x‖⁻¹ • x
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hxnorm]
  have hux : ‖x‖ • u = x := by simp [u, smul_smul, hxnorm]
  have hid : r • (u - v) = (r - ‖x‖) • u + (x - r • v) := by
    rw [sub_smul, hux, smul_sub]
    abel
  have hnormrv : ‖r • v‖ = r := by simp [norm_smul, hv, abs_of_pos hr]
  have hrev : |r - ‖x‖| ≤ ‖x - r • v‖ := by
    simpa only [hnormrv, norm_sub_rev] using abs_norm_sub_norm_le (r • v) x
  calc
    r * ‖‖x‖⁻¹ • x - v‖ = ‖r • (u - v)‖ := by simp [norm_smul, abs_of_pos hr, u]
    _ = ‖(r - ‖x‖) • u + (x - r • v)‖ := by rw [hid]
    _ ≤ ‖(r - ‖x‖) • u‖ + ‖x - r • v‖ := norm_add_le _ _
    _ = |r - ‖x‖| + ‖x - r • v‖ := by simp [norm_smul, hu]
    _ ≤ 2 * ‖x - r • v‖ := by linarith

/-- Uniform small balls along the middle half of a ray lie in the cap cone. -/
theorem ball_subset_packetCap_cone {n : ℕ} {δ r : ℝ} {v : Space n}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hv : ‖v‖ = 1)
    (hrlo : 1 / 2 ≤ r) (hrhi : r ≤ 3 / 4) :
    ball (r • v) (δ / 512) ⊆ Ioo (0 : ℝ) 1 • OAI.MeasureTheory.Kakeya.packetCap δ v := by
  intro x hx
  have hdist : ‖x - r • v‖ < δ / 512 := hx
  have hr : 0 < r := by linarith
  have hnormrv : ‖r • v‖ = r := by simp [norm_smul, hv, abs_of_pos hr]
  have hx0 : x ≠ 0 := by
    intro hx0
    simp only [hx0, zero_sub, norm_neg, hnormrv] at hdist
    linarith
  have hx1 : ‖x‖ < 1 := by
    have ht := norm_add_le (x - r • v) (r • v)
    rw [sub_add_cancel, hnormrv] at ht
    linarith
  have hunit : ‖‖x‖⁻¹ • x‖ = 1 := by simp [norm_smul, norm_ne_zero_iff.mpr hx0]
  have hcap : ‖‖x‖⁻¹ • x - v‖ ≤ δ / 32 := by
    have ht := norm_normalize_sub_unit_mul hx0 hv hr
    have hn := norm_nonneg (‖x‖⁻¹ • x - v)
    nlinarith
  refine ⟨‖x‖, ⟨norm_pos_iff.mpr hx0, hx1⟩, ‖x‖⁻¹ • x, ⟨hunit, hcap⟩, ?_⟩
  simp [smul_smul, norm_ne_zero_iff.mpr hx0]

def capPackingCenter {n : ℕ} (δ : ℝ) (v : Space n) (j : ℕ) : Space n :=
  (1 / 2 + (j : ℝ) * δ / 4) • v

theorem capPacking_count_lower {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) :
    1 / (2 * δ) ≤ (⌊1 / δ⌋₊ : ℝ) := by
  have hge : (1 : ℝ) ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by simpa)
  have hfloor : 1 ≤ ⌊1 / δ⌋₊ := Nat.le_floor (by simpa using hge)
  have hfloor' : (1 : ℝ) ≤ (⌊1 / δ⌋₊ : ℝ) := by exact_mod_cast hfloor
  have hlt := Nat.lt_floor_add_one (1 / δ)
  have heq : 1 / (2 * δ) = (1 / δ) / 2 := by ring
  rw [heq]
  linarith

theorem capPacking_ball_subset {n : ℕ} {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hv : ‖v‖ = 1)
    {j : ℕ} (hj : j < ⌊1 / δ⌋₊) :
    ball (capPackingCenter δ v j) (δ / 512) ⊆ Ioo (0 : ℝ) 1 • OAI.MeasureTheory.Kakeya.packetCap δ v := by
  have hjle : (j : ℝ) ≤ 1 / δ :=
    (Nat.cast_le.mpr hj.le).trans (Nat.floor_le (by positivity))
  have hjmul : (j : ℝ) * δ ≤ 1 := (le_div_iff₀ hδ).mp hjle
  apply ball_subset_packetCap_cone hδ hδone hv
  · have hnonneg : 0 ≤ (j : ℝ) * δ / 4 := by positivity
    linarith
  · linarith

theorem capPacking_balls_disjoint {n : ℕ} {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hv : ‖v‖ = 1) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (ball (capPackingCenter δ v i) (δ / 512))
      (ball (capPackingCenter δ v j) (δ / 512)) := by
  have hdiff : 1 ≤ |(i : ℝ) - j| := by
    rcases lt_or_gt_of_ne hij with h | h
    · have hcast : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt h
      have hlt : (i : ℝ) < j := by exact_mod_cast h
      rw [abs_of_neg (sub_neg.mpr hlt)]
      linarith
    · have hcast : (j : ℝ) + 1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt h
      have hlt : (j : ℝ) < i := by exact_mod_cast h
      rw [abs_of_pos (sub_pos.mpr hlt)]
      linarith
  have hsep : δ / 4 ≤ dist (capPackingCenter δ v i) (capPackingCenter δ v j) := by
    rw [capPackingCenter, capPackingCenter, dist_eq_norm, ← sub_smul, norm_smul, hv,
      mul_one, Real.norm_eq_abs]
    have heq : (1 / 2 + (i : ℝ) * δ / 4) - (1 / 2 + (j : ℝ) * δ / 4) =
        ((i : ℝ) - j) * (δ / 4) := by ring
    rw [heq, abs_mul, abs_of_pos (by positivity : 0 < δ / 4)]
    nlinarith
  apply Metric.ball_disjoint_ball
  linarith

/-- The cone contains order δ⁻¹ disjoint balls of radius δ/512. -/
theorem capPacking_measure_le {n : ℕ} {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hv : ‖v‖ = 1) :
    (∑ j ∈ Finset.range ⌊1 / δ⌋₊,
      volume (ball (capPackingCenter δ v j) (δ / 512))) ≤
      volume (Ioo (0 : ℝ) 1 • OAI.MeasureTheory.Kakeya.packetCap δ v) := by
  rw [← measure_biUnion_finset (fun i _ j _ hij ↦ capPacking_balls_disjoint hδ hv hij)
    (fun _ _ ↦ measurableSet_ball)]
  apply measure_mono
  intro x hx
  obtain ⟨j, hj, hx⟩ := mem_iUnion₂.mp hx
  exact capPacking_ball_subset hδ hδone hv (Finset.mem_range.mp hj) hx

theorem packetCap_measure_lower_floor {n : ℕ} {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hv : ‖v‖ = 1) :
    (n : ℝ≥0∞) * (⌊1 / δ⌋₊ : ℝ≥0∞) * ENNReal.ofReal ((δ / 512) ^ n) *
      volume (ball (0 : Space n) 1) ≤ OAI.Analysis.Fourier.Restriction.sphereMeasure n (OAI.MeasureTheory.Kakeya.packetCap δ v) := by
  rw [sphereMeasure_packetCap]
  have h := capPacking_measure_le hδ hδone hv
  simp_rw [(volume : Measure (Space n)).addHaar_ball_of_pos _
    (show 0 < δ / 512 by positivity)] at h
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ (n : ℝ≥0∞) by positivity)
  simpa [Space, nsmul_eq_mul, mul_assoc] using hm

theorem packetCap_real_lower_floor {n : ℕ} {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hv : ‖v‖ = 1) :
    (n : ℝ) * (⌊1 / δ⌋₊ : ℝ) * ((δ / 512) ^ n) *
      volume.real (ball (0 : Space n) 1) ≤ (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (OAI.MeasureTheory.Kakeya.packetCap δ v) := by
  have h := ENNReal.toReal_mono (measure_ne_top (OAI.Analysis.Fourier.Restriction.sphereMeasure n) _)
    (packetCap_measure_lower_floor hδ hδone hv)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (show 0 ≤ (δ / 512) ^ n by positivity), Measure.real] using h

/-- Sharp power δ^(n-1), with an explicit positive dimensional coefficient. -/
theorem packetCap_real_lower {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hv : ‖v‖ = 1) :
    ((n : ℝ) * volume.real (ball (0 : Space n) 1) / (2 * 512 ^ n)) * δ ^ (n - 1) ≤
      (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (OAI.MeasureTheory.Kakeya.packetCap δ v) := by
  have hfloor := capPacking_count_lower hδ hδone
  have hvol : 0 ≤ volume.real (ball (0 : Space n) 1) := ENNReal.toReal_nonneg
  have hmono : (n : ℝ) * (1 / (2 * δ)) * ((δ / 512) ^ n) *
      volume.real (ball (0 : Space n) 1) ≤
      (n : ℝ) * (⌊1 / δ⌋₊ : ℝ) * ((δ / 512) ^ n) * volume.real (ball (0 : Space n) 1) := by
    gcongr
  have hp : δ ^ n = δ ^ (n - 1) * δ := by
    simpa only [Nat.sub_add_cancel hn] using pow_succ δ (n - 1)
  have heq : (n : ℝ) * (1 / (2 * δ)) * ((δ / 512) ^ n) *
      volume.real (ball (0 : Space n) 1) =
      ((n : ℝ) * volume.real (ball (0 : Space n) 1) / (2 * 512 ^ n)) * δ ^ (n - 1) := by
    rw [div_pow, hp]
    field_simp
  rw [heq] at hmono
  exact hmono.trans (packetCap_real_lower_floor hδ hδone hv)

theorem packetCap_lower_coefficient_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < (n : ℝ) * volume.real (ball (0 : Space n) 1) / (2 * 512 ^ n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hv : 0 < volume.real (ball (0 : Space n) 1) :=
    ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume _ zero_lt_one))
      measure_ball_lt_top.ne
  positivity

/-- The cone of a cap is covered by order δ⁻¹ balls of radius 2δ. -/
theorem packetCap_cone_subset_cover {n : ℕ} {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hv : ‖v‖ = 1) :
    Ioo (0 : ℝ) 1 • OAI.MeasureTheory.Kakeya.packetCap δ v ⊆
      ⋃ j ∈ Finset.range (⌊1 / δ⌋₊ + 1), ball (((j : ℝ) * δ) • v) (2 * δ) := by
  rintro x ⟨r, hr, ω, hω, rfl⟩
  let j : ℕ := ⌊r / δ⌋₊
  have hj : j < ⌊1 / δ⌋₊ + 1 := by
    apply Nat.lt_succ_of_le
    exact Nat.floor_mono (div_le_div_of_nonneg_right hr.2.le hδ.le)
  have hjlo : (j : ℝ) * δ ≤ r := by
    exact (le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg hr.1.le hδ.le))
  have hjhi : r < (j : ℝ) * δ + δ := by
    have ht := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (r / δ))
    dsimp [j]
    linarith
  apply mem_iUnion₂.mpr
  refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
  rw [mem_ball, dist_eq_norm]
  have hid : r • ω - ((j : ℝ) * δ) • v =
      r • (ω - v) + (r - (j : ℝ) * δ) • v := by
    rw [smul_sub, sub_smul]
    abel
  rw [hid]
  have hnorm : ‖r • (ω - v)‖ ≤ δ / 32 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1]
    calc r * ‖ω - v‖ ≤ 1 * (δ / 32) := mul_le_mul hr.2.le hω.2 (norm_nonneg _) (by norm_num)
         _ = δ / 32 := one_mul _
  have hnorm' : ‖(r - (j : ℝ) * δ) • v‖ < δ := by
    rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hjlo)]
    linarith
  exact (norm_add_le _ _).trans_lt (by linarith)

theorem capCover_count_upper {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) :
    (⌊1 / δ⌋₊ + 1 : ℝ) ≤ 2 / δ := by
  have hfloor := Nat.floor_le (by positivity : 0 ≤ 1 / δ)
  have hge : (1 : ℝ) ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by simpa)
  have heq : 2 / δ = 2 * (1 / δ) := by ring
  rw [heq]
  linarith

theorem packetCap_measure_upper_floor {n : ℕ} {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hv : ‖v‖ = 1) :
    OAI.Analysis.Fourier.Restriction.sphereMeasure n (OAI.MeasureTheory.Kakeya.packetCap δ v) ≤
      (n : ℝ≥0∞) * ((⌊1 / δ⌋₊ + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((2 * δ) ^ n) *
        volume (ball (0 : Space n) 1) := by
  rw [sphereMeasure_packetCap]
  have h := (measure_mono (packetCap_cone_subset_cover hδ hv)).trans
    (measure_biUnion_finset_le (μ := (volume : Measure (Space n))) _ _)
  simp_rw [(volume : Measure (Space n)).addHaar_ball_of_pos _
    (show 0 < 2 * δ by positivity)] at h
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ (n : ℝ≥0∞) by positivity)
  simpa [Space, nsmul_eq_mul, mul_assoc] using hm

theorem packetCap_real_upper_floor {n : ℕ} {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hv : ‖v‖ = 1) :
    (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (OAI.MeasureTheory.Kakeya.packetCap δ v) ≤
      (n : ℝ) * (⌊1 / δ⌋₊ + 1 : ℝ) * ((2 * δ) ^ n) *
        volume.real (ball (0 : Space n) 1) := by
  have h := packetCap_measure_upper_floor hδ hv
  have hfin : (n : ℝ≥0∞) * ((⌊1 / δ⌋₊ + 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal ((2 * δ) ^ n) * volume (ball (0 : Space n) 1) ≠ ⊤ := by
    finiteness
  have ht := ENNReal.toReal_mono hfin h
  simpa [ENNReal.toReal_mul, ENNReal.toReal_add,
    ENNReal.toReal_ofReal (show 0 ≤ (2 * δ) ^ n by positivity), Measure.real] using ht

theorem packetCap_real_upper {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hv : ‖v‖ = 1) :
    (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (OAI.MeasureTheory.Kakeya.packetCap δ v) ≤
      ((n : ℝ) * 2 ^ (n + 1) * volume.real (ball (0 : Space n) 1)) * δ ^ (n - 1) := by
  have hfloor := capCover_count_upper hδ hδone
  have hvol : 0 ≤ volume.real (ball (0 : Space n) 1) := ENNReal.toReal_nonneg
  have hmono : (n : ℝ) * (⌊1 / δ⌋₊ + 1 : ℝ) * ((2 * δ) ^ n) *
      volume.real (ball (0 : Space n) 1) ≤
      (n : ℝ) * (2 / δ) * ((2 * δ) ^ n) * volume.real (ball (0 : Space n) 1) := by
    gcongr
  have hp : δ ^ n = δ ^ (n - 1) * δ := by
    simpa only [Nat.sub_add_cancel hn] using pow_succ δ (n - 1)
  have heq : (n : ℝ) * (2 / δ) * ((2 * δ) ^ n) * volume.real (ball (0 : Space n) 1) =
      ((n : ℝ) * 2 ^ (n + 1) * volume.real (ball (0 : Space n) 1)) * δ ^ (n - 1) := by
    rw [mul_pow, hp, pow_succ]
    field_simp
  exact (packetCap_real_upper_floor hδ hv).trans (hmono.trans_eq heq)

/-- Uniform two-sided surface-measure bounds for the exact wave-packet cap. -/
theorem packetCap_real_comparable {n : ℕ} (hn : 1 ≤ n) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (δ : ℝ) (v : Space n), 0 < δ → δ ≤ 1 → ‖v‖ = 1 →
      c * δ ^ (n - 1) ≤ (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (OAI.MeasureTheory.Kakeya.packetCap δ v) ∧
      (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (OAI.MeasureTheory.Kakeya.packetCap δ v) ≤ C * δ ^ (n - 1) := by
  refine ⟨(n : ℝ) * volume.real (ball (0 : Space n) 1) / (2 * 512 ^ n),
    (n : ℝ) * 2 ^ (n + 1) * volume.real (ball (0 : Space n) 1),
    packetCap_lower_coefficient_pos hn, ?_, ?_⟩
  · have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hv : 0 < volume.real (ball (0 : Space n) 1) :=
      ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume _ zero_lt_one))
        measure_ball_lt_top.ne
    positivity
  · intro δ v hδ hδone hv
    exact ⟨packetCap_real_lower hn hδ hδone hv, packetCap_real_upper hn hδ hδone hv⟩

end OAI.Analysis.Fourier.Restriction
