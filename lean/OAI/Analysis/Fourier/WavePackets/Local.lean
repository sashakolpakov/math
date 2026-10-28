import OAI.Analysis.Fourier.WavePackets.Periodization

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ContDiff ENNReal

theorem isCompact_coordinateCube (n : ℕ) (r : ℝ) : IsCompact (coordinateCube n r) := by
  have heq : coordinateCube n r =
      WithLp.toLp 2 '' Set.Icc (fun _ : Fin n => -r) (fun _ => r) := by
    ext x
    constructor
    · intro hx
      refine ⟨WithLp.ofLp x, ⟨?_, ?_⟩, rfl⟩
      · intro i; exact (abs_le.mp (hx i)).1
      · intro i; exact (abs_le.mp (hx i)).2
    · rintro ⟨y, hy, rfl⟩ i
      exact abs_le.mpr ⟨hy.1 i, hy.2 i⟩
  rw [heq]
  exact isCompact_Icc.image (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ))

theorem measurableSet_coordinateCube (n : ℕ) (r : ℝ) : MeasurableSet (coordinateCube n r) :=
  (isCompact_coordinateCube n r).isClosed.measurableSet

theorem volume_coordinateCube (n : ℕ) (r : ℝ) :
    volume (coordinateCube n r) = ENNReal.ofReal (2 * r) ^ n := by
  have heq : coordinateCube n r =
      WithLp.ofLp ⁻¹' Set.Icc (fun _ : Fin n => -r) (fun _ => r) := by
    ext x
    simp only [coordinateCube, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc,
      Pi.le_def, abs_le, forall_and]
  rw [heq, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage measurableSet_Icc.nullMeasurableSet]
  simp [Real.volume_Icc_pi, sub_neg_eq_add, two_mul]

theorem one_sub_inv_toReal_nonneg {p : ℝ≥0∞} (hp : 1 ≤ p) :
    0 ≤ 1 - 1 / p.toReal := by
  by_cases hp_top : p = ⊤
  · simp [hp_top]
  · have hpr : 1 ≤ p.toReal := by
      simpa only [ENNReal.toReal_one] using
        (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top).mpr hp
    exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr hpr)

theorem eLpNorm_eq_restrict_of_ae_support {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} {f : α → F} {s : Set α}
    (hs : MeasurableSet s) (hf : ∀ᵐ x ∂μ, f x ≠ 0 → x ∈ s) (p : ℝ≥0∞) :
    eLpNorm f p μ = eLpNorm f p (μ.restrict s) := by
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs]
  apply eLpNorm_congr_ae
  filter_upwards [hf] with x hx
  by_cases hxs : x ∈ s
  · simp [hxs]
  · have hz : f x = 0 := by by_contra h; exact hxs (hx h)
    simp [hxs, hz]

theorem integrable_of_memLp_of_ae_support {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} {f : α → F} {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s < ⊤) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : MemLp f p μ) (hsupport : ∀ᵐ x ∂μ, f x ≠ 0 → x ∈ s) :
    Integrable f μ := by
  apply memLp_one_iff_integrable.mp
  change eLpNorm f 1 μ < ⊤
  rw [eLpNorm_eq_restrict_of_ae_support hs hsupport 1]
  apply (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hf.aestronglyMeasurable.restrict).trans_lt
  apply ENNReal.mul_lt_top (hf.mono_measure Measure.restrict_le_self).eLpNorm_lt_top
  apply ENNReal.rpow_lt_top_of_nonneg
  · simpa using one_sub_inv_toReal_nonneg hp
  · simpa using hμs.ne

section Periodization

variable {n : ℕ} {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure]

theorem stronglyMeasurable_periodizationError_spacetime
    {a f : EuclideanSpace ℝ (Fin n) → ℂ}
    (ha : Continuous a) (hs : HasCompactSupport a) (h : ℝ)
    (hf : AEStronglyMeasurable f μ) :
    StronglyMeasurable (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      periodizationError μ a f h q.1 q.2) := by
  have hm : StronglyMeasurable (fun q : (ℝ × EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) =>
      periodizationRemainder μ a h q.1.1 (q.1.2 - q.2) * hf.mk f q.2) := by
    apply Measurable.stronglyMeasurable
    exact ((measurable_periodizationRemainder_spacetime ha hs h).comp
      ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).sub measurable_snd))).mul
      (hf.stronglyMeasurable_mk.measurable.comp measurable_snd)
  have heq : (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      periodizationError μ a f h q.1 q.2) =
      (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        ∫ Y, periodizationRemainder μ a h q.1 (q.2 - Y) * hf.mk f Y ∂μ) := by
    funext q
    apply integral_congr_ae
    filter_upwards [hf.ae_eq_mk] with Y hY
    rw [hY]
  rw [heq]
  exact hm.integral_prod_right'

/-- The local space-time measure on the unit cube and time interval `[1,2]`. -/
noncomputable def localSpacetimeMeasure
    (μ : Measure (EuclideanSpace ℝ (Fin n))) : Measure (ℝ × EuclideanSpace ℝ (Fin n)) :=
  (volume.restrict (Set.Icc (1 : ℝ) 2)).prod (μ.restrict (coordinateCube n (1 / 2)))

/-- The periodized-copy error has a rapidly decaying local space-time norm.
The two explicit finite-volume factors are precisely the Hölder loss from
`10Q` and the constant-function norm on `Q`. -/
theorem periodizationError_local_eLpNorm_bound
    {a : EuclideanSpace ℝ (Fin n) → ℂ}
    (ha : ContDiff ℝ ∞ a) (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport a)
    (hs : HasCompactSupport a) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : EuclideanSpace ℝ (Fin n) → ℂ),
      Integrable f μ → (∀ᵐ Y ∂μ, f Y ≠ 0 → Y ∈ coordinateCube n 5) →
      ∀ (p : ℝ≥0∞), 1 ≤ p → ∀ h : ℝ, 0 < h → h ≤ 1 →
        eLpNorm (fun q : ℝ × EuclideanSpace ℝ (Fin n) => periodizationError μ a f h q.1 q.2)
          p (localSpacetimeMeasure μ) ≤
          μ (coordinateCube n (1 / 2)) ^ p.toReal⁻¹ *
            ENNReal.ofReal (C * h ^ N) *
            (eLpNorm f p μ * μ (coordinateCube n 5) ^ (1 - 1 / p.toReal)) := by
  obtain ⟨C, hC, hb⟩ := periodizationError_bound (μ := μ) ha hzero hs N
  refine ⟨C, hC, ?_⟩
  intro f hf hsupport p hp h hh hh₁
  have hpoint : ∀ᵐ q ∂localSpacetimeMeasure μ,
      ‖periodizationError μ a f h q.1 q.2‖ ≤ C * h ^ N * ∫ Y, ‖f Y‖ ∂μ := by
    have ht := ae_restrict_mem (μ := volume) (s := Set.Icc (1 : ℝ) 2) measurableSet_Icc
    have hx := ae_restrict_mem (μ := μ) (s := coordinateCube n (1 / 2)) (measurableSet_coordinateCube _ _)
    have hboth : ∀ᵐ q ∂localSpacetimeMeasure μ,
        q.1 ∈ Set.Icc (1 : ℝ) 2 ∧ q.2 ∈ coordinateCube n (1 / 2) :=
      (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.prod (measurableSet_coordinateCube _ _))).mpr
        (ht.mono fun T hT => hx.mono fun X hX => ⟨hT, hX⟩)
    filter_upwards [hboth] with q hq
    exact (hb f hf hsupport q.2 q.1 h hq.2 (by linarith [hq.1.1]) hq.1.2 hh hh₁).2
  have he := eLpNorm_le_of_ae_bound (p := p)
    (stronglyMeasurable_periodizationError_spacetime ha.continuous hs h hf.aestronglyMeasurable).aestronglyMeasurable hpoint
  have hm : localSpacetimeMeasure μ Set.univ = μ (coordinateCube n (1 / 2)) := by
    rw [localSpacetimeMeasure, ← Set.univ_prod_univ, Measure.prod_prod]
    norm_num [Real.volume_Icc]
  rw [hm, ENNReal.ofReal_mul (mul_nonneg hC (pow_nonneg hh.le N))] at he
  have hnorm : ENNReal.ofReal (∫ Y, ‖f Y‖ ∂μ) = eLpNorm f 1 μ := by
    have heq := (memLp_one_iff_integrable.mpr hf).eLpNorm_eq_integral_rpow_norm
      one_ne_zero ENNReal.one_ne_top
    simpa using heq.symm
  rw [hnorm] at he
  apply he.trans
  rw [← mul_assoc]
  apply mul_le_mul' le_rfl
  rw [eLpNorm_eq_restrict_of_ae_support (measurableSet_coordinateCube _ _) hsupport 1,
    eLpNorm_eq_restrict_of_ae_support (measurableSet_coordinateCube _ _) hsupport p]
  simpa using eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hf.aestronglyMeasurable.restrict

end Periodization

/-- With Lebesgue normalization the unit cube has mass one. Consequently
the local periodization error is `O(h^N)` on every `Lᵖ`, uniformly in `p≥1`.
The explicit loss absorbed here is only the volume `10^n` of `10Q`. -/
theorem periodizationError_local_bound {n : ℕ}
    {a : EuclideanSpace ℝ (Fin n) → ℂ}
    (ha : ContDiff ℝ ∞ a) (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport a)
    (hs : HasCompactSupport a) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : EuclideanSpace ℝ (Fin n) → ℂ) (p : ℝ≥0∞),
      1 ≤ p → MemLp f p volume →
      (∀ᵐ Y ∂volume, f Y ≠ 0 → Y ∈ coordinateCube n 5) →
      ∀ h : ℝ, 0 < h → h ≤ 1 →
        MemLp (fun q : ℝ × EuclideanSpace ℝ (Fin n) => periodizationError volume a f h q.1 q.2)
          p (localSpacetimeMeasure volume) ∧
        eLpNorm (fun q : ℝ × EuclideanSpace ℝ (Fin n) => periodizationError volume a f h q.1 q.2)
          p (localSpacetimeMeasure volume) ≤ ENNReal.ofReal (C * h ^ N) * eLpNorm f p volume := by
  obtain ⟨C, hC, hb⟩ := periodizationError_local_eLpNorm_bound (μ := volume) ha hzero hs N
  refine ⟨C * 10 ^ n, mul_nonneg hC (by positivity), ?_⟩
  intro f p hp hf hsupport h hh hh₁
  have hfi : Integrable f volume := integrable_of_memLp_of_ae_support
    (measurableSet_coordinateCube n 5) (by rw [volume_coordinateCube]; finiteness) hp hf hsupport
  have he := hb f hfi hsupport p hp h hh hh₁
  norm_num [volume_coordinateCube] at he
  have hfac : ((10 : ℝ≥0∞) ^ n) ^ (1 - 1 / p.toReal) ≤ (10 : ℝ≥0∞) ^ n := by
    calc
      _ ≤ ((10 : ℝ≥0∞) ^ n) ^ (1 : ℝ) := by
        apply ENNReal.rpow_le_rpow_of_exponent_le
        · exact one_le_pow₀ (by norm_num)
        · have : 0 ≤ 1 / p.toReal := by positivity
          linarith
      _ = _ := ENNReal.rpow_one _
  have hbound : eLpNorm
      (fun q : ℝ × EuclideanSpace ℝ (Fin n) => periodizationError volume a f h q.1 q.2)
      p (localSpacetimeMeasure volume) ≤
      ENNReal.ofReal (C * 10 ^ n * h ^ N) * eLpNorm f p volume := by
    apply he.trans
    calc
      _ ≤ ENNReal.ofReal (C * h ^ N) * (eLpNorm f p volume * (10 : ℝ≥0∞) ^ n) := by
        gcongr
        simpa only [one_div] using hfac
      _ = _ := by
        rw [show C * 10 ^ n * h ^ N = (C * h ^ N) * 10 ^ n by ring,
          ENNReal.ofReal_mul (mul_nonneg hC (pow_nonneg hh.le N)), ENNReal.ofReal_pow (by norm_num)]
        norm_num [mul_assoc, mul_comm, mul_left_comm]
  exact ⟨hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top), hbound⟩

end OAI.Analysis.Fourier.WavePackets
