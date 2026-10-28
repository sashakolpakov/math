import OAI.Analysis.Fourier.WavePackets.Localization

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory UnitAddTorus
open scoped ENNReal ContDiff

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem lintegral_local_torus_pullback_le {n : ℕ} (g : UnitAddTorus (Fin n) → ℝ≥0∞) :
    (∫⁻ Y in coordinateCube n (1 / 2), g (torusProjection ((1 / 100 : ℝ) • Y))) ≤
      (100 : ℝ≥0∞) ^ n * ∫⁻ x, g x := by
  let F : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    (coordinateCube n (1 / 2)).indicator (fun Y => g (torusProjection ((1 / 100 : ℝ) • Y)))
  have hsF : Function.support F ⊆ coordinateCube n 5 := by
    intro Y hY i
    have hmem : Y ∈ coordinateCube n (1 / 2) := Set.support_indicator_subset hY
    exact (hmem i).trans (by norm_num)
  have hpoint (x : UnitAddTorus (Fin n)) : torusInput F x ≤ g x := by
    let r := WithLp.toLp 2
      ((UnitAddTorus.measurableEquivPiIoc (fun _ : Fin n => -(1/2 : ℝ))) x).val
    have hq : torusProjection r = x := by
      exact (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin n => -(1/2 : ℝ))).symm_apply_apply x
    change F ((100 : ℝ) • r) ≤ g x
    by_cases hr : (100 : ℝ) • r ∈ coordinateCube n (1 / 2)
    · simp only [F, Set.indicator_of_mem hr]
      have he : (1 / 100 : ℝ) • ((100 : ℝ) • r) = r := by module
      rw [he, hq]
    · simp only [F, Set.indicator_of_notMem hr, zero_le]
  have hi : ((100 : ℝ≥0∞) ^ n)⁻¹ * ∫⁻ Y, F Y ≤ ∫⁻ x, g x := by
    rw [← lintegral_torusInput F hsF]
    exact lintegral_mono hpoint
  have hm := mul_le_mul_right hi ((100 : ℝ≥0∞) ^ n)
  rw [← mul_assoc, ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_mul] at hm
  simpa only [F, lintegral_indicator (measurableSet_coordinateCube n (1 / 2))] using hm

noncomputable def periodicSpacetimeMeasure (n : ℕ) : Measure (ℝ × UnitAddTorus (Fin n)) :=
  (volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume

theorem measurable_periodicHalfWave_spacetime {n : ℕ}
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) (h : ℝ) (f : UnitAddTorus (Fin n) → ℂ) :
    Measurable (fun q : ℝ × UnitAddTorus (Fin n) => periodicHalfWave φ h q.1 f q.2) := by
  apply Measurable.tsum
  intro k
  have hc : Continuous (fun q : ℝ × UnitAddTorus (Fin n) =>
      periodicSymbol φ h q.1 k * mFourierCoeff f k * mFourier k q.2) := by
    unfold periodicSymbol
    fun_prop
  exact hc.measurable

theorem eLpNorm_local_torus_pullback_le {n : ℕ}
    (g : ℝ × UnitAddTorus (Fin n) → ℂ) (hg : Measurable g)
    {p : ℝ≥0∞} (hp : p ≠ 0) (hptop : p ≠ ⊤) :
    eLpNorm (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      g (q.1, torusProjection ((1 / 100 : ℝ) • q.2))) p (localSpacetimeMeasure volume) ≤
      ((100 : ℝ≥0∞) ^ n) ^ (1 / p.toReal) * eLpNorm g p (periodicSpacetimeMeasure n) := by
  have hpull : Measurable (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      g (q.1, torusProjection ((1 / 100 : ℝ) • q.2))) :=
    hg.comp (measurable_fst.prodMk ((continuous_torusProjection.measurable).comp
      (by fun_prop)))
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hptop hpull.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp hptop hg.aestronglyMeasurable,
    ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  apply ENNReal.rpow_le_rpow
  · rw [localSpacetimeMeasure, periodicSpacetimeMeasure,
      lintegral_prod _ (hpull.enorm.pow_const _).aemeasurable,
      lintegral_prod _ (hg.enorm.pow_const _).aemeasurable,
      ← lintegral_const_mul' _ _ (by finiteness)]
    apply lintegral_mono
    intro T
    exact lintegral_local_torus_pullback_le (fun x => ‖g (T, x)‖ₑ ^ p.toReal)
  · positivity

/-- The quantitative local transfer inequality. The periodic norm is the
genuine Fourier-series half-wave norm; the error decays to arbitrary order. -/
theorem frequencyHalfWave_local_transfer {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hs : HasCompactSupport φ) (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ →
      ∀ f : EuclideanSpace ℝ (Fin n) → ℂ, Measurable f → MemLp f p volume →
      Function.support f ⊆ coordinateCube n 5 →
      ∀ h : ℝ, 0 < h → h ≤ 1 →
      eLpNorm (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h q.1 f q.2) p (localSpacetimeMeasure volume) ≤
        ((100 : ℝ≥0∞) ^ n) ^ (1 / p.toReal) *
          eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) =>
            periodicHalfWave φ h q.1 (torusInput f) q.2) p (periodicSpacetimeMeasure n) +
          ENNReal.ofReal (C * h ^ N) * eLpNorm f p volume := by
  obtain ⟨C, hC, hbound⟩ := periodizationError_local_bound hφ hzero hs N
  let P : ℂ := (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹
  refine ⟨‖P‖ * C, mul_nonneg (norm_nonneg P) hC, ?_⟩
  intro p hp hptop f hm hf hsupport h hh hh₁
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hp)
  have hsAE : ∀ᵐ Y ∂volume, f Y ≠ 0 → Y ∈ coordinateCube n 5 :=
    Filter.Eventually.of_forall fun Y hY => hsupport hY
  have hfi : Integrable f := integrable_of_memLp_of_ae_support
    (measurableSet_coordinateCube n 5) (by rw [volume_coordinateCube]; finiteness) hp hf hsAE
  let G := fun q : ℝ × UnitAddTorus (Fin n) => periodicHalfWave φ h q.1 (torusInput f) q.2
  let E := fun q : ℝ × EuclideanSpace ℝ (Fin n) => periodizationError volume φ f h q.1 q.2
  have hG : Measurable G := measurable_periodicHalfWave_spacetime φ h (torusInput f)
  have hboth : ∀ᵐ q ∂localSpacetimeMeasure (volume : Measure (EuclideanSpace ℝ (Fin n))),
      q.1 ∈ Set.Icc (1 : ℝ) 2 ∧ q.2 ∈ coordinateCube n (1 / 2) :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.prod (measurableSet_coordinateCube _ _))).mpr
      ((ae_restrict_mem measurableSet_Icc).mono fun T hT =>
        (ae_restrict_mem (measurableSet_coordinateCube _ _)).mono fun X hX => ⟨hT, hX⟩)
  have heq : (fun q : ℝ × EuclideanSpace ℝ (Fin n) => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h q.1 f q.2) =ᵐ[
      localSpacetimeMeasure volume]
      (fun q => G (q.1, torusProjection ((1 / 100 : ℝ) • q.2)) - P * E q) := by
    filter_upwards [hboth] with q hq
    have he := periodicHalfWave_local_comparison hφ hs hzero hm hfi hsupport hh hh₁
      (by linarith [hq.1.1]) hq.1.2 hq.2
    dsimp [G, E, P]
    exact (eq_sub_iff_add_eq.mpr he.symm)
  rw [eLpNorm_congr_ae heq]
  apply (eLpNorm_sub_le hp).trans
  apply add_le_add (eLpNorm_local_torus_pullback_le G hG hp0 hptop)
  have hmul : eLpNorm (fun q => P * E q) p (localSpacetimeMeasure volume) =
      ENNReal.ofReal ‖P‖ * eLpNorm E p (localSpacetimeMeasure volume) := by
    rw [ofReal_norm]
    convert eLpNorm_const_smul P E p (localSpacetimeMeasure volume) using 1
  rw [hmul]
  calc
    _ ≤ ENNReal.ofReal ‖P‖ * (ENNReal.ofReal (C * h ^ N) * eLpNorm f p volume) := by
      gcongr
      exact (hbound f p hp hf hsAE h hh hh₁).2
    _ = ENNReal.ofReal (‖P‖ * C * h ^ N) * eLpNorm f p volume := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg P)]
      congr 2
      ring

/-- Any proved periodic bound transfers, with the same main constant, to
Euclidean data supported in `10Q`. This is an implication, not an assertion
that the periodic local-smoothing estimate has already been proved. -/
theorem local_bound_of_periodic_bound {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hs : HasCompactSupport φ) (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ →
      ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ B : ℝ≥0∞,
      (∀ g : UnitAddTorus (Fin n) → ℂ, Measurable g → MemLp g p volume →
        eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) => periodicHalfWave φ h q.1 g q.2)
          p (periodicSpacetimeMeasure n) ≤ B * eLpNorm g p volume) →
      ∀ f : EuclideanSpace ℝ (Fin n) → ℂ, Measurable f → MemLp f p volume →
      Function.support f ⊆ coordinateCube n 5 →
      eLpNorm (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h q.1 f q.2) p (localSpacetimeMeasure volume) ≤
        (B + ENNReal.ofReal (C * h ^ N)) * eLpNorm f p volume := by
  obtain ⟨C, hC, hb⟩ := frequencyHalfWave_local_transfer hφ hs hzero N
  refine ⟨C, hC, ?_⟩
  intro p hp hptop h hh hh₁ B hper f hm hf hsf
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hp)
  have hinput : MemLp (torusInput f) p volume := by
    change eLpNorm (torusInput f) p volume < ⊤
    rw [eLpNorm_torusInput f hm hsf hp0 hptop]
    exact ENNReal.mul_lt_top (by finiteness) hf.eLpNorm_lt_top
  have hscale : ((100 : ℝ≥0∞) ^ n) ^ (1 / p.toReal) *
      eLpNorm (torusInput f) p volume = eLpNorm f p volume := by
    rw [eLpNorm_torusInput f hm hsf hp0 hptop, ← mul_assoc,
      ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ENNReal.mul_inv_cancel (by positivity) (by finiteness), ENNReal.one_rpow, one_mul]
  calc
    _ ≤ ((100 : ℝ≥0∞) ^ n) ^ (1 / p.toReal) *
          eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) =>
            periodicHalfWave φ h q.1 (torusInput f) q.2) p (periodicSpacetimeMeasure n) +
          ENNReal.ofReal (C * h ^ N) * eLpNorm f p volume := hb p hp hptop f hm hf hsf h hh hh₁
    _ ≤ ((100 : ℝ≥0∞) ^ n) ^ (1 / p.toReal) *
          (B * eLpNorm (torusInput f) p volume) +
          ENNReal.ofReal (C * h ^ N) * eLpNorm f p volume := by
      gcongr
      exact hper (torusInput f) (measurable_torusInput hm) hinput
    _ = _ := by rw [mul_left_comm _ B, hscale, add_mul]

end OAI.Analysis.Fourier.WavePackets
