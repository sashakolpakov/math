import OAI.Analysis.Fourier.WavePackets.Cubes

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ENNReal ContDiff

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem measurable_frequencyHalfWave_spacetime {n : ℕ}
    {φ f : EuclideanSpace ℝ (Fin n) → ℂ} (hφ : Continuous φ)
    (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h) (hm : Measurable f) (hf : Integrable f) :
    Measurable (fun q : ℝ × EuclideanSpace ℝ (Fin n) => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h q.1 f q.2) := by
  have he : (fun q : ℝ × EuclideanSpace ℝ (Fin n) => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h q.1 f q.2) =
      (fun q => (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹ *
        ∫ Y, semiclassicalWaveKernel volume φ h q.1 (q.2 - Y) * f Y) := by
    funext q
    exact (frequencyHalfWave_eq_integral_kernel hφ hs hh q.1 hf q.2).2
  rw [he]
  apply measurable_const.mul
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right' (f := fun q :
    (ℝ × EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) =>
      semiclassicalWaveKernel volume φ h q.1.1 (q.1.2 - q.2) * f q.2)
  apply Measurable.stronglyMeasurable
  exact ((continuous_semiclassicalWaveKernel_spacetime hφ hs h).measurable.comp
    ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).sub measurable_snd))).mul
    (hm.comp measurable_snd)

theorem frequencyHalfWave_translate {n : ℕ}
    {φ f : EuclideanSpace ℝ (Fin n) → ℂ} (hφ : Continuous φ)
    (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h) (hf : Integrable f)
    (c X : EuclideanSpace ℝ (Fin n)) (T : ℝ) :
    OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h T (fun Y => f (c + Y)) X =
      OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h T f (c + X) := by
  have hshift : Integrable (fun Y => f (c + Y)) :=
    (measurePreserving_add_left volume c).integrable_comp_of_integrable hf
  rw [(frequencyHalfWave_eq_integral_kernel hφ hs hh T hshift X).2,
    (frequencyHalfWave_eq_integral_kernel hφ hs hh T hf (c + X)).2]
  congr 1
  have hi := (measurePreserving_add_left volume c).integral_comp
    (Homeomorph.addLeft c).measurableEmbedding
    (fun Y => semiclassicalWaveKernel volume φ h T (c + X - Y) * f Y)
  simpa only [add_sub_add_left_eq_sub] using hi

theorem lintegral_translatedCube {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (r : ℝ) (k : Fin n → ℤ) :
    (∫⁻ X in coordinateCube n r, u (integerVector k + X)) =
      ∫⁻ X in translatedCube n r k, u X := by
  have hi := (measurePreserving_add_left volume (integerVector k)).setLIntegral_comp_preimage_emb
    (Homeomorph.addLeft (integerVector k)).measurableEmbedding u (translatedCube n r k)
  have he : (fun X => integerVector k + X) ⁻¹' translatedCube n r k = coordinateCube n r := by
    ext X
    simp [translatedCube, add_sub_cancel_left]
  rw [he] at hi
  exact hi

theorem eLpNorm_spacetime_translate {n : ℕ}
    {u : ℝ × EuclideanSpace ℝ (Fin n) → ℂ} (hu : Measurable u)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ⊤) (k : Fin n → ℤ) :
    eLpNorm (fun q : ℝ × EuclideanSpace ℝ (Fin n) => u (q.1, integerVector k + q.2))
      p (localSpacetimeMeasure volume) = eLpNorm u p (cubeSpacetimeMeasure n k) := by
  have hm : Measurable (fun q : ℝ × EuclideanSpace ℝ (Fin n) => u (q.1, integerVector k + q.2)) :=
    hu.comp (by fun_prop)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hm.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hu.aestronglyMeasurable,
    localSpacetimeMeasure, cubeSpacetimeMeasure,
    lintegral_prod _ (hm.enorm.pow_const _).aemeasurable,
    lintegral_prod _ (hu.enorm.pow_const _).aemeasurable]
  congr 1
  apply lintegral_congr
  intro T
  exact lintegral_translatedCube (fun X => ‖u (T, X)‖ₑ ^ p.toReal) _ k

noncomputable def localizedData {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (k : Fin n → ℤ) := (translatedCube n 5 k).indicator f

noncomputable def centeredData {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (k : Fin n → ℤ) := (coordinateCube n 5).indicator (fun X => f (integerVector k + X))

theorem centeredData_eq {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (k : Fin n → ℤ) (X : EuclideanSpace ℝ (Fin n)) :
    centeredData f k X = localizedData f k (integerVector k + X) := by
  classical
  by_cases hx : X ∈ coordinateCube n 5
  · have hy : integerVector k + X ∈ translatedCube n 5 k := by simpa [translatedCube] using hx
    simp only [centeredData, localizedData, Set.indicator_of_mem hx, Set.indicator_of_mem hy]
  · have hy : integerVector k + X ∉ translatedCube n 5 k := by simpa [translatedCube] using hx
    simp only [centeredData, localizedData, Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]

theorem eLpNorm_centeredData {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : Measurable f) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ⊤) (k : Fin n → ℤ) :
    eLpNorm (centeredData f k) p volume = eLpNorm f p (volume.restrict (translatedCube n 5 k)) := by
  rw [centeredData, eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_coordinateCube _ _)]
  have hm : Measurable (fun X => f (integerVector k + X)) := hf.comp (by fun_prop)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hm.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hf.aestronglyMeasurable]
  congr 1
  exact lintegral_translatedCube (fun x => ‖f x‖ₑ ^ p.toReal) 5 k

noncomputable def nearestCube {n : ℕ} (X : EuclideanSpace ℝ (Fin n)) : Fin n → ℤ :=
  fun i => ⌊X i + 1 / 2⌋

theorem measurable_nearestCube {n : ℕ} : Measurable (@nearestCube n) := by
  apply Measurable.of_eval
  intro i
  unfold nearestCube
  fun_prop

theorem mem_nearestCube {n : ℕ} (X : EuclideanSpace ℝ (Fin n)) :
    X ∈ translatedCube n (1 / 2) (nearestCube X) := by
  intro i
  change |X i - (⌊X i + 1 / 2⌋ : ℝ)| ≤ 1 / 2
  exact abs_le.mpr ⟨by linarith [Int.floor_le (X i + 1 / 2)],
    by linarith [Int.lt_floor_add_one (X i + 1 / 2)]⟩

noncomputable def cubeAssembly {n : ℕ}
    (v : (Fin n → ℤ) → ℝ × EuclideanSpace ℝ (Fin n) → ℂ)
    (q : ℝ × EuclideanSpace ℝ (Fin n)) : ℂ := v (nearestCube q.2) q

theorem measurable_cubeAssembly {n : ℕ}
    {v : (Fin n → ℤ) → ℝ × EuclideanSpace ℝ (Fin n) → ℂ}
    (hv : ∀ k, Measurable (v k)) : Measurable (cubeAssembly v) := by
  classical
  have he : cubeAssembly v = fun q => ∑' k : Fin n → ℤ,
      {q : ℝ × EuclideanSpace ℝ (Fin n) | nearestCube q.2 = k}.indicator (v k) q := by
    funext q
    rw [tsum_eq_single (nearestCube q.2)]
    · simp [cubeAssembly]
    · intro k hk
      exact Set.indicator_of_notMem (by exact Ne.symm hk) _
  rw [he]
  apply Measurable.tsum
  intro k
  exact (hv k).indicator (measurableSet_eq_fun (measurable_nearestCube.comp measurable_snd) measurable_const)

theorem lintegral_cubeAssembly_le {n : ℕ}
    {v : (Fin n → ℤ) → ℝ × EuclideanSpace ℝ (Fin n) → ℂ}
    (hv : ∀ k, Measurable (v k)) (s : ℝ) :
    (∫⁻ q, ‖cubeAssembly v q‖ₑ ^ s ∂(volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume) ≤
      ∑' k : Fin n → ℤ, ∫⁻ q, ‖v k q‖ₑ ^ s ∂cubeSpacetimeMeasure n k := by
  let W := fun k : Fin n → ℤ => fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
    {q | q.2 ∈ translatedCube n (1 / 2) k}.indicator (fun q => ‖v k q‖ₑ ^ s) q
  have hW (k) : Measurable (W k) :=
    ((hv k).enorm.pow_const _).indicator ((measurableSet_translatedCube _ _ _).preimage measurable_snd)
  have hp (q : ℝ × EuclideanSpace ℝ (Fin n)) : ‖cubeAssembly v q‖ₑ ^ s ≤ ∑' k, W k q := by
    calc
      _ = W (nearestCube q.2) q := by
        exact (Set.indicator_of_mem (show q ∈ {z : ℝ × EuclideanSpace ℝ (Fin n) |
          z.2 ∈ translatedCube n (1 / 2) (nearestCube q.2)} from mem_nearestCube q.2)
          (fun z => ‖v (nearestCube q.2) z‖ₑ ^ s)).symm
      _ ≤ _ := ENNReal.le_tsum (f := fun k => W k q) _
  apply (lintegral_mono hp).trans
  rw [lintegral_tsum fun k => (hW k).aemeasurable]
  apply le_of_eq
  congr 1
  funext k
  rw [lintegral_prod _ (hW k).aemeasurable]
  change _ = ∫⁻ q, ‖v k q‖ₑ ^ s ∂(volume.restrict (Set.Icc (1 : ℝ) 2)).prod
    (volume.restrict (translatedCube n (1 / 2) k))
  rw [lintegral_prod _ ((hv k).enorm.pow_const _).aemeasurable]
  apply lintegral_congr
  intro T
  have he : (fun X => W k (T, X)) = (translatedCube n (1 / 2) k).indicator (fun X => ‖v k (T, X)‖ₑ ^ s) := by
    funext X
    rfl
  rw [he, lintegral_indicator (measurableSet_translatedCube _ _ _)]

theorem eLpNorm_cubeAssembly_le {n : ℕ}
    {v : (Fin n → ℤ) → ℝ × EuclideanSpace ℝ (Fin n) → ℂ} (hv : ∀ k, Measurable (v k))
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Measurable f)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ⊤) (A : ℝ≥0∞)
    (hlocal : ∀ k : Fin n → ℤ, eLpNorm (v k) p (cubeSpacetimeMeasure n k) ≤
      A * eLpNorm f p (volume.restrict (translatedCube n 5 k))) :
    eLpNorm (cubeAssembly v) p ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume) ≤
      A * ((11 : ℝ≥0∞) ^ n) ^ (1 / p.toReal) * eLpNorm f p volume := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hi : (∫⁻ q, ‖cubeAssembly v q‖ₑ ^ p.toReal ∂(volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume) ≤
      A ^ p.toReal * ((11 : ℝ≥0∞) ^ n * ∫⁻ x, ‖f x‖ₑ ^ p.toReal) := by
    calc
      _ ≤ ∑' k : Fin n → ℤ, ∫⁻ q, ‖v k q‖ₑ ^ p.toReal ∂cubeSpacetimeMeasure n k :=
        lintegral_cubeAssembly_le hv _
      _ ≤ ∑' k : Fin n → ℤ,
          A ^ p.toReal * ∫⁻ x in translatedCube n 5 k, ‖f x‖ₑ ^ p.toReal := by
        apply ENNReal.tsum_le_tsum
        intro k
        have he := ENNReal.rpow_le_rpow (hlocal k) hp.le
        rw [eLpNorm_rpow_eq_lintegral hp0 hptop (hv k).aestronglyMeasurable,
          ENNReal.mul_rpow_of_nonneg _ _ hp.le,
          eLpNorm_rpow_eq_lintegral hp0 hptop hf.aestronglyMeasurable] at he
        exact he
      _ = A ^ p.toReal * ∑' k : Fin n → ℤ,
          ∫⁻ x in translatedCube n 5 k, ‖f x‖ₑ ^ p.toReal := ENNReal.tsum_mul_left
      _ ≤ _ := mul_le_mul_right (tsum_lintegral_enlargedCube_le (hf.enorm.pow_const _)) _
  have hroot := ENNReal.rpow_le_rpow hi (show 0 ≤ 1 / p.toReal by positivity)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    mul_one_div_cancel hp.ne', ENNReal.rpow_one] at hroot
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop (measurable_cubeAssembly hv).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hf.aestronglyMeasurable]
  simpa only [mul_assoc] using hroot

theorem measurable_localizedData {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : Measurable f) (k : Fin n → ℤ) : Measurable (localizedData f k) :=
  hf.indicator (measurableSet_translatedCube _ _ _)

theorem integrable_localizedData {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℂ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hf : MemLp f p volume) (k : Fin n → ℤ) :
    Integrable (localizedData f k) := by
  have hL : MemLp (localizedData f k) p volume :=
    hf.indicator (measurableSet_translatedCube n 5 k)
  have hvol : volume (translatedCube n 5 k) < ⊤ := by
    have he : volume (translatedCube n 5 k) = volume (coordinateCube n 5) := by
      exact (measurePreserving_sub_right volume (integerVector k)).measure_preimage
        (measurableSet_coordinateCube _ _).nullMeasurableSet
    rw [he, volume_coordinateCube]
    finiteness
  exact integrable_of_memLp_of_ae_support (measurableSet_translatedCube n 5 k) hvol hp hL
    (Filter.Eventually.of_forall fun X hX => Set.support_indicator_subset hX)

noncomputable def nearWave {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℂ) (h : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℂ) : ℝ × EuclideanSpace ℝ (Fin n) → ℂ :=
  cubeAssembly fun k q => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h q.1 (localizedData f k) q.2

/-- The near-input part of the actual Euclidean half-wave satisfies the
global periodic-to-Euclidean estimate after bounded-overlap summation. -/
theorem nearWave_bound_of_periodic_bound {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hs : HasCompactSupport φ) (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ →
      ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ B : ℝ≥0∞,
      (∀ g : UnitAddTorus (Fin n) → ℂ, Measurable g → MemLp g p volume →
        eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) => periodicHalfWave φ h q.1 g q.2)
          p (periodicSpacetimeMeasure n) ≤ B * eLpNorm g p volume) →
      ∀ f : EuclideanSpace ℝ (Fin n) → ℂ, Measurable f → MemLp f p volume →
      eLpNorm (nearWave φ h f) p ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume) ≤
        (B + ENNReal.ofReal (C * h ^ N)) * ((11 : ℝ≥0∞) ^ n) ^ (1 / p.toReal) * eLpNorm f p volume := by
  obtain ⟨C, hC, hb⟩ := local_bound_of_periodic_bound hφ hs hzero N
  refine ⟨C, hC, ?_⟩
  intro p hp hptop h hh hh₁ B hper f hm hf
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hmeas (k : Fin n → ℤ) : Measurable (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h q.1 (localizedData f k) q.2) :=
    measurable_frequencyHalfWave_spacetime hφ.continuous hs hh
      (measurable_localizedData hm k) (integrable_localizedData hp hf k)
  apply eLpNorm_cubeAssembly_le hmeas hm hp0 hptop
  intro k
  have hmc : Measurable (centeredData f k) :=
    (hm.comp (by fun_prop)).indicator (measurableSet_coordinateCube n 5)
  have hpc : MemLp (centeredData f k) p volume := by
    change eLpNorm (centeredData f k) p volume < ⊤
    rw [eLpNorm_centeredData hm hp0 hptop]
    exact (hf.mono_measure Measure.restrict_le_self).eLpNorm_lt_top
  have hc := hb p hp hptop h hh hh₁ B hper (centeredData f k) hmc hpc
    (Set.support_indicator_subset)
  rw [eLpNorm_centeredData hm hp0 hptop] at hc
  rw [← eLpNorm_spacetime_translate (hmeas k) hp0 hptop k]
  convert hc using 1
  congr 1
  funext q
  have he : centeredData f k = fun X => localizedData f k (integerVector k + X) :=
    funext (centeredData_eq f k)
  rw [he]
  exact (frequencyHalfWave_translate hφ.continuous hs hh (integrable_localizedData hp hf k)
    (integerVector k) q.2 q.1).symm

end OAI.Analysis.Fourier.WavePackets
