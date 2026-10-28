import OAI.Analysis.Fourier.WavePackets.Assembly

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ENNReal ContDiff

noncomputable def spatialTailWeight {n : ℕ} (X : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 + ‖X‖) ^ (-(n + 1 : ℝ))

theorem spatialTailWeight_nonneg {n : ℕ} (X : EuclideanSpace ℝ (Fin n)) :
    0 ≤ spatialTailWeight X := by unfold spatialTailWeight; positivity

theorem integrable_spatialTailWeight (n : ℕ) :
    Integrable (@spatialTailWeight n) := by
  apply integrable_one_add_norm
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  linarith

theorem far_input_separation {n : ℕ} {k : Fin n → ℤ}
    {X Y : EuclideanSpace ℝ (Fin n)} (hX : X ∈ translatedCube n (1 / 2) k)
    (hY : Y ∉ translatedCube n 5 k) : 3 ≤ ‖X - Y‖ := by
  have hn : ¬ ∀ i, |Y i - (k i : ℝ)| ≤ 5 := hY
  push Not at hn
  obtain ⟨i, hi⟩ := hn
  have hx := hX i
  change |X i - (k i : ℝ)| ≤ 1 / 2 at hx
  have hd : |Y i - (k i : ℝ)| ≤ |X i - Y i| + |X i - (k i : ℝ)| := by
    have he : Y i - (k i : ℝ) = -(X i - Y i) + (X i - (k i : ℝ)) := by ring
    rw [he]
    simpa only [abs_neg] using abs_add_le (-(X i - Y i)) (X i - (k i : ℝ))
  have hcoord : |X i - Y i| ≤ ‖X - Y‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (X - Y) i
  linarith

noncomputable def farWave {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℂ) (h : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℂ) (q : ℝ × EuclideanSpace ℝ (Fin n)) : ℂ :=
  OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h q.1 f q.2 - nearWave φ h f q

theorem measurable_nearWave {n : ℕ} {φ f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    (hm : Measurable f) (hf : Integrable f) : Measurable (nearWave φ h f) := by
  apply measurable_cubeAssembly
  intro k
  exact measurable_frequencyHalfWave_spacetime hφ hs hh (measurable_localizedData hm k)
    (hf.indicator (measurableSet_translatedCube _ _ _))

theorem measurable_farWave {n : ℕ} {φ f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    (hm : Measurable f) (hf : Integrable f) : Measurable (farWave φ h f) :=
  (measurable_frequencyHalfWave_spacetime hφ hs hh hm hf).sub
    (measurable_nearWave hφ hs hh hm hf)

theorem farWave_pointwise_majorant {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hs : HasCompactSupport φ) (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : EuclideanSpace ℝ (Fin n) → ℂ, Integrable f →
      ∀ h T : ℝ, 0 < h → h ≤ 1 → 0 ≤ T → T ≤ 2 → ∀ X,
      ‖farWave φ h f (T, X)‖ₑ ≤ ENNReal.ofReal (C * h ^ N) *
        ∫⁻ Z, ENNReal.ofReal (spatialTailWeight Z) * ‖f (X - Z)‖ₑ := by
  obtain ⟨C, hC, hb⟩ := waveTail_uniform_majorant (μ := volume) hφ hzero hs N
  let P : ℂ := (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹
  refine ⟨‖P‖ * C, mul_nonneg (norm_nonneg P) hC, ?_⟩
  intro f hf h T hh hh₁ hT₀ hT₁ X
  let k := nearestCube X
  have hfk : Integrable (localizedData f k) := hf.indicator (measurableSet_translatedCube _ _ _)
  have hK := (frequencyHalfWave_eq_integral_kernel hφ.continuous hs hh T hf X).1
  have hKk := (frequencyHalfWave_eq_integral_kernel hφ.continuous hs hh T hfk X).1
  have he : farWave φ h f (T, X) = P * ∫ Y,
      semiclassicalWaveKernel volume φ h T (X - Y) * (f Y - localizedData f k Y) := by
    change OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h T f X - OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h T (localizedData f k) X = _
    rw [(frequencyHalfWave_eq_integral_kernel hφ.continuous hs hh T hf X).2,
      (frequencyHalfWave_eq_integral_kernel hφ.continuous hs hh T hfk X).2]
    simp_rw [mul_sub]
    rw [integral_sub hK hKk]
    ring
  have hpoint (Y : EuclideanSpace ℝ (Fin n)) :
      ‖semiclassicalWaveKernel volume φ h T (X - Y) * (f Y - localizedData f k Y)‖ₑ ≤
        ENNReal.ofReal (C * h ^ N) * (ENNReal.ofReal (spatialTailWeight (X - Y)) * ‖f Y‖ₑ) := by
    by_cases hY : Y ∈ translatedCube n 5 k
    · simp [localizedData, Set.indicator_of_mem hY]
    · have hsep := far_input_separation (mem_nearestCube X) hY
      have hnorm := hb T h hT₀ hT₁ hh hh₁ (X - Y)
      rw [waveTail, Set.indicator_of_mem
        (show X - Y ∈ {Z : EuclideanSpace ℝ (Fin n) | 3 ≤ ‖Z‖} from hsep)] at hnorm
      simp only [finrank_euclideanSpace, Fintype.card_fin] at hnorm
      have hn := ENNReal.ofReal_le_ofReal hnorm
      rw [ENNReal.ofReal_mul (mul_nonneg hC (pow_nonneg hh.le N)), ofReal_norm] at hn
      simp only [localizedData, Set.indicator_of_notMem hY, sub_zero, enorm_mul]
      exact (mul_le_mul' hn (le_refl ‖f Y‖ₑ)).trans_eq (mul_assoc _ _ _)
  rw [he, enorm_mul]
  calc
    _ ≤ ‖P‖ₑ * ∫⁻ Y,
        ‖semiclassicalWaveKernel volume φ h T (X - Y) * (f Y - localizedData f k Y)‖ₑ := by
      gcongr
      exact enorm_integral_le_lintegral_enorm _
    _ ≤ ‖P‖ₑ * (ENNReal.ofReal (C * h ^ N) *
        ∫⁻ Y, ENNReal.ofReal (spatialTailWeight (X - Y)) * ‖f Y‖ₑ) := by
      gcongr
      calc
        _ ≤ ∫⁻ Y, ENNReal.ofReal (C * h ^ N) *
            (ENNReal.ofReal (spatialTailWeight (X - Y)) * ‖f Y‖ₑ) := lintegral_mono hpoint
        _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
      have hi := lintegral_sub_left_eq_self (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
        (fun Z => ENNReal.ofReal (spatialTailWeight Z) * ‖f (X - Z)‖ₑ) X
      simp only [sub_sub_cancel] at hi
      rw [hi, ← mul_assoc, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg P)]
      congr 2
      ring

theorem eLpNorm_le_of_enorm_convolution_bound {n : ℕ}
    {g f : EuclideanSpace ℝ (Fin n) → ℂ} (hg : Measurable g) (hf : Measurable f)
    {w : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hw : Measurable w)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hptop : p ≠ ⊤) (A : ℝ≥0∞)
    (hb : ∀ X, ‖g X‖ₑ ≤ A * ∫⁻ Z, w Z * ‖f (X - Z)‖ₑ) :
    eLpNorm g p volume ≤ A * (∫⁻ Z, w Z) * eLpNorm f p volume := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpr : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using (ENNReal.toReal_le_toReal ENNReal.one_ne_top hptop).mpr hp
  have hpos : 0 < p.toReal := lt_of_lt_of_le zero_lt_one hpr
  have hi : (∫⁻ X, ‖g X‖ₑ ^ p.toReal) ≤
      A ^ p.toReal * ((∫⁻ Z, w Z) ^ p.toReal * ∫⁻ X, ‖f X‖ₑ ^ p.toReal) := by
    calc
      _ ≤ ∫⁻ X, (A * ∫⁻ Z, w Z * ‖f (X - Z)‖ₑ) ^ p.toReal :=
        lintegral_mono fun X => ENNReal.rpow_le_rpow (hb X) hpos.le
      _ = A ^ p.toReal * ∫⁻ X, (∫⁻ Z, w Z * ‖f (X - Z)‖ₑ) ^ p.toReal := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hpos.le]
        apply lintegral_const_mul''
        fun_prop
      _ ≤ _ := mul_le_mul_right (lintegral_convolution_rpow_le hw hf.enorm hpr) _
  have hr := ENNReal.rpow_le_rpow hi (show 0 ≤ 1 / p.toReal by positivity)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, mul_one_div_cancel hpos.ne', ENNReal.rpow_one, ENNReal.rpow_one] at hr
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hg.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hf.aestronglyMeasurable]
  simpa only [mul_assoc] using hr

/-- The actual cube-dependent far-input remainder is negligible in global
space-time `Lᵖ`, not merely its fixed-kernel proxy. -/
theorem farWave_spacetime_bound {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hs : HasCompactSupport φ) (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : EuclideanSpace ℝ (Fin n) → ℂ, Measurable f → Integrable f →
      ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ → ∀ h : ℝ, 0 < h → h ≤ 1 →
      eLpNorm (farWave φ h f) p ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume) ≤
        ENNReal.ofReal (C * h ^ N) * eLpNorm f p volume := by
  obtain ⟨C, hC, hb⟩ := farWave_pointwise_majorant hφ hs hzero N
  let D : ℝ := ∫ Z : EuclideanSpace ℝ (Fin n), spatialTailWeight Z
  have hD : 0 ≤ D := integral_nonneg spatialTailWeight_nonneg
  have hweight : Measurable (fun Z : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (spatialTailWeight Z)) := by
    unfold spatialTailWeight
    fun_prop
  have hmass : (∫⁻ Z : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (spatialTailWeight Z)) =
      ENNReal.ofReal D := (ofReal_integral_eq_lintegral_ofReal (integrable_spatialTailWeight n)
        (Filter.Eventually.of_forall spatialTailWeight_nonneg)).symm
  refine ⟨C * D, mul_nonneg hC hD, ?_⟩
  intro f hm hf p hp hptop h hh hh₁
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hg := measurable_farWave hφ.continuous hs hh hm hf
  apply eLpNorm_prod_le_of_slice_bound (by norm_num [Real.volume_Icc]) hg.aestronglyMeasurable hp0 hptop
  filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
  have he := eLpNorm_le_of_enorm_convolution_bound
    (hg.comp (measurable_const.prodMk measurable_id)) hm hweight hp hptop
    (ENNReal.ofReal (C * h ^ N)) (hb f hf h T hh hh₁ (by linarith [hT.1]) hT.2)
  rw [hmass, ← ENNReal.ofReal_mul (mul_nonneg hC (pow_nonneg hh.le N))] at he
  have heq : C * h ^ N * D = C * D * h ^ N := by ring
  simpa only [heq, Function.comp_def, id_eq] using he

end OAI.Analysis.Fourier.WavePackets
