import OAI.Analysis.Fourier.WavePackets.LinearKernel
import OAI.Analysis.Fourier.WavePackets.Young

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ENNReal

noncomputable local instance periodicKernelCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance periodicKernelCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance periodicKernelCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem lintegral_torus_eq_unitCell {n : ℕ} (f : UnitAddTorus (Fin n) → ℝ≥0∞) :
    (∫⁻ x, f x) = ∫⁻ x in unitCell n, f (torusProjection x) := by
  rw [UnitAddTorus.lintegral_preimage f (fun _ => 0)]
  have hbox : (volume : Measure (Fin n → ℝ)).restrict
      {x | ∀ i, x i ∈ Set.Ioc 0 (0 + 1)} =
      volume.restrict {x | ∀ i, x i ∈ Set.Ico 0 1} := by
    have hset (s : Set ℝ) : {x : Fin n → ℝ | ∀ i, x i ∈ s} = Set.univ.pi (fun _ => s) := by
      ext x
      simp
    rw [hset, hset]
    change (Measure.pi fun _ : Fin n => (volume : Measure ℝ)).restrict
        (Set.univ.pi fun _ => Set.Ioc 0 (0 + 1)) =
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)).restrict
        (Set.univ.pi fun _ => Set.Ico 0 1)
    simp_rw [Measure.restrict_pi_pi, zero_add, ← restrict_Ico_eq_restrict_Ioc]
  rw [hbox]
  have hpres := (PiLp.volume_preserving_ofLp (Fin n)).setLIntegral_comp_preimage_emb
    (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).measurableEmbedding
    (fun x => f (fun i => (x i : UnitAddCircle))) {x : Fin n → ℝ | ∀ i, x i ∈ Set.Ico 0 1}
  convert hpres.symm using 1
  have hcell : unitCell n = WithLp.ofLp ⁻¹'
      {x : Fin n → ℝ | ∀ i, x i ∈ Set.Ico 0 1} := by
    ext x
    simp [unitCell, ZSpan.fundamentalDomain]
  rw [hcell]
  rfl

noncomputable def torusRepresentative {n : ℕ} (x : UnitAddTorus (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 ((UnitAddTorus.measurableEquivPiIoc (fun _ : Fin n => 0)) x).val

theorem measurable_torusRepresentative {n : ℕ} : Measurable (@torusRepresentative n) := by
  exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_subtype_coe.comp
    (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin n => 0)).measurable)

theorem torusProjection_representative {n : ℕ} (x : UnitAddTorus (Fin n)) :
    torusProjection (torusRepresentative x) = x := by
  change (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin n => 0)).symm
    ((UnitAddTorus.measurableEquivPiIoc (fun _ : Fin n => 0)) x) = x
  exact MeasurableEquiv.symm_apply_apply _ x

/-- Periodization as an actual measurable function on the compact torus. -/
noncomputable def latticePeriodization {n : ℕ} (K : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : UnitAddTorus (Fin n)) : ℂ :=
  ∑' k : Fin n → ℤ, K (integerVector k + torusRepresentative x)

theorem measurable_latticePeriodization {n : ℕ} {K : EuclideanSpace ℝ (Fin n) → ℂ}
    (hK : Measurable K) : Measurable (latticePeriodization K) := by
  apply Measurable.tsum
  intro k
  exact hK.comp (measurable_const.add measurable_torusRepresentative)

theorem latticePeriodization_projection {n : ℕ} (K : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) :
    latticePeriodization K (torusProjection x) = ∑' k : Fin n → ℤ, K (integerVector k + x) := by
  obtain ⟨k, hk⟩ := torusProjection_fiber (torusProjection_representative (torusProjection x))
  unfold latticePeriodization
  rw [hk, lattice_sum_periodic]

/-- Periodization does not increase the L1 norm, with normalized torus Haar
measure. This holds for measurable kernels, not merely Schwartz kernels. -/
theorem eLpNorm_latticePeriodization_le {n : ℕ} {K : EuclideanSpace ℝ (Fin n) → ℂ}
    (hK : Measurable K) :
    eLpNorm (latticePeriodization K) 1 volume ≤ eLpNorm K 1 volume := by
  rw [eLpNorm_one_eq_lintegral_enorm (measurable_latticePeriodization hK).aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm hK.aestronglyMeasurable, lintegral_torus_eq_unitCell,
    lintegral_eq_tsum_unitCell]
  simp_rw [latticePeriodization_projection]
  calc
    _ ≤ ∫⁻ x in unitCell n, ∑' k : Fin n → ℤ, ‖K (integerVector k + x)‖ₑ :=
      lintegral_mono fun _ => enorm_tsum_le_tsum_enorm
    _ = _ := by
      rw [lintegral_tsum]
      intro k
      exact (hK.enorm.comp (measurable_const.add measurable_id)).aemeasurable

theorem integrable_latticePeriodization {n : ℕ} {K : EuclideanSpace ℝ (Fin n) → ℂ}
    (hK : Measurable K) (hi : Integrable K) : Integrable (latticePeriodization K) := by
  apply memLp_one_iff_integrable.mp
  exact (eLpNorm_latticePeriodization_le hK).trans_lt (memLp_one_iff_integrable.mpr hi)

/-- Uniform L1 control of a Euclidean kernel immediately gives all finite
`Lp` multiplier bounds on the torus. -/
theorem eLpNorm_periodized_convolution_le {n : ℕ} {K : EuclideanSpace ℝ (Fin n) → ℂ}
    (hK : Measurable K) {f : UnitAddTorus (Fin n) → ℂ} (hf : Measurable f)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    eLpNorm (complexConvolution (latticePeriodization K) f volume) p volume ≤
      eLpNorm K 1 volume * eLpNorm f p volume :=
  (eLpNorm_complexConvolution_le_of_measurable (measurable_latticePeriodization hK) hf hp hp_top).trans
    (mul_le_mul' (eLpNorm_latticePeriodization_le hK) le_rfl)

/-- The endpoint Young estimate in pointwise form, useful for the
amplitude pieces in the restricted-sector argument. -/
theorem enorm_complexConvolution_le_of_enorm_bound {G : Type*} [AddCommGroup G]
    [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
    {μ : Measure G} [SFinite μ] [μ.IsAddRightInvariant]
    {k f : G → ℂ} (hk : Measurable k) {B : ℝ≥0∞}
    (hf : ∀ y, ‖f y‖ₑ ≤ B) (x : G) :
    ‖complexConvolution k f μ x‖ₑ ≤ eLpNorm k 1 μ * B := by
  rw [eLpNorm_one_eq_lintegral_enorm hk.aestronglyMeasurable]
  calc
    _ ≤ ∫⁻ y, ‖k y * f (x - y)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y, ‖k y‖ₑ * B ∂μ := lintegral_mono fun y => by
      rw [enorm_mul]
      exact mul_le_mul' le_rfl (hf (x - y))
    _ = _ := lintegral_mul_const B hk.enorm

theorem eLpNorm_periodized_convolution_top_le {n : ℕ}
    {K : EuclideanSpace ℝ (Fin n) → ℂ} (hK : Measurable K)
    {f : UnitAddTorus (Fin n) → ℂ} (hfm : Measurable f) {B : ℝ≥0∞}
    (hf : ∀ y, ‖f y‖ₑ ≤ B) :
    eLpNorm (complexConvolution (latticePeriodization K) f volume) ∞ volume ≤
      eLpNorm K 1 volume * B := by
  rw [eLpNorm_exponent_top (aestronglyMeasurable_complexConvolution
    (measurable_latticePeriodization hK).aestronglyMeasurable hfm.aestronglyMeasurable)]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  exact Filter.Eventually.of_forall fun x =>
    (enorm_complexConvolution_le_of_enorm_bound (measurable_latticePeriodization hK) hf x).trans
      (mul_le_mul' (eLpNorm_latticePeriodization_le hK) le_rfl)

end OAI.Analysis.Fourier.WavePackets
