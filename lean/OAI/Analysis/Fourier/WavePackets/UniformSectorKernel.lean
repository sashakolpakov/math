import OAI.Analysis.Fourier.WavePackets.SectorMultiplier
import OAI.Analysis.Fourier.BochnerRiesz.Multiplier

open OAI.Analysis.Fourier.Wave

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ENNReal FourierTransform ContDiff RealInnerProductSpace

theorem fourierInv_eq_normalized_angularInverse {n : ℕ} (φ : Space n → ℂ) (x : Space n) :
    𝓕⁻ φ x = ((2 * Real.pi) ^ n) • OAI.Analysis.Fourier.LocalSmoothing.angularInverse φ ((2 * Real.pi) • x) := by
  rw [OAI.Analysis.Fourier.LocalSmoothing.angularInverse, smul_smul, mul_inv_cancel₀ (pow_ne_zero n (by positivity)), one_smul,
    Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [inner_smul_left, starRingEnd_apply, star_trivial, smul_eq_mul, Complex.ofReal_mul]
  rw [real_inner_comm ξ x]
  congr 2
  ring

/-- The two Fourier conventions have the same inverse-kernel L1 norm. -/
theorem eLpNorm_fourierInv_eq_angularInverse {n : ℕ} {φ : Space n → ℂ}
    (hφ : Integrable φ) : eLpNorm (𝓕⁻ φ) 1 volume = eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse φ) 1 volume := by
  let h : ℝ := (2 * Real.pi)⁻¹
  have hh : 0 < h := by dsimp [h]; positivity
  have he : 𝓕⁻ φ = fun x => (h ^ n)⁻¹ • OAI.Analysis.Fourier.LocalSmoothing.angularInverse φ (h⁻¹ • x) := by
    funext x
    rw [fourierInv_eq_normalized_angularInverse]
    simp only [h, inv_pow, inv_inv]
  rw [he]
  exact OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_normalized_dilate_one _
    (OAI.Analysis.Fourier.BochnerRiesz.continuous_angularInverse hφ).measurable hh

/-- Compact smooth families of fixed-support rescaled symbols retain a
uniform L1 kernel bound after *arbitrary* invertible linear distortions.
No condition number or Jacobian bound on the distortion is needed. -/
theorem uniform_linearly_rescaled_inverse_kernel_bound {Q : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] {n : ℕ}
    {K : Set Q} {S : Set (Space n)} (hK : IsCompact K) (hS : IsCompact S)
    {a : Q × Space n → ℂ} (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ Set.univ ×ˢ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ A : Space n ≃L[ℝ] Space n,
      eLpNorm (𝓕⁻ (fun ξ => a (q, A ξ))) 1 volume ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hc⟩ := OAI.Analysis.Fourier.BochnerRiesz.uniform_angularInverse_L1 hK hS ha hs
  refine ⟨C, hC, ?_⟩
  intro q hq A
  let φ : Space n → ℂ := fun ξ => a (q, ξ)
  have hcont : ContDiff ℝ ∞ φ := ha.comp (contDiff_const.prodMk contDiff_id)
  have hcompact : HasCompactSupport φ := by
    apply hS.of_isClosed_subset (isClosed_tsupport _)
    intro ξ hξ
    exact (hs (tsupport_comp_subset_preimage a (continuous_const.prodMk continuous_id) hξ)).2
  have hφint : Integrable φ := hcont.continuous.integrable_of_hasCompactSupport hcompact
  have hmeas : Measurable (𝓕⁻ φ) := by
    have he : ((𝓕⁻ (hcompact.toSchwartzMap hcont) : SchwartzMap (Space n) ℂ) : Space n → ℂ) =
        𝓕⁻ φ := by rw [SchwartzMap.fourierInv_coe]; rfl
    rw [← he]
    exact (𝓕⁻ (hcompact.toSchwartzMap hcont)).continuous.measurable
  change eLpNorm (𝓕⁻ (φ ∘ A)) 1 volume ≤ ENNReal.ofReal C
  rw [eLpNorm_fourierInv_comp_linearEquiv A φ hmeas, eLpNorm_fourierInv_eq_angularInverse hφint]
  exact (hc q hq).2

section Periodic

noncomputable local instance uniformSectorCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance uniformSectorCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance uniformSectorCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The uniform sector-projection multiplier conclusion for any compact
smooth family of rescaled annular symbols. The linear distortions and
semiclassical scale are completely unrestricted except for invertibility. -/
theorem uniform_linearly_rescaled_periodic_cutoff_bound {Q : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] {n : ℕ}
    {K : Set Q} {S : Set (Space n)} (hK : IsCompact K) (hS : IsCompact S)
    (hzero : (0 : Space n) ∉ S)
    {a : Q × Space n → ℂ} (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ Set.univ ×ˢ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ A : Space n ≃L[ℝ] Space n,
      ∀ h : ℝ, 0 < h → ∀ f : UnitAddTorus (Fin n) → ℂ, Measurable f → Integrable f →
        (∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
          eLpNorm (periodicHalfWave (fun ξ => a (q, A ξ)) h 0 f) p volume ≤
            ENNReal.ofReal C * eLpNorm f p volume) ∧
        (∀ B : ℝ≥0∞, (∀ x, ‖f x‖ₑ ≤ B) →
          eLpNorm (periodicHalfWave (fun ξ => a (q, A ξ)) h 0 f) ⊤ volume ≤
            ENNReal.ofReal C * B) := by
  obtain ⟨C, hC, hc⟩ := uniform_linearly_rescaled_inverse_kernel_bound hK hS ha hs
  refine ⟨C, hC, ?_⟩
  intro q hq A h hh f hf hfi
  have hcomp : Continuous (fun ξ : Space n => (q, A ξ)) := continuous_const.prodMk A.continuous
  have hdiff : ContDiff ℝ ∞ (fun ξ : Space n => a (q, A ξ)) :=
    ha.comp (contDiff_const.prodMk A.contDiff)
  have hcompact : HasCompactSupport (fun ξ : Space n => a (q, A ξ)) := by
    apply (hS.image A.symm.continuous).of_isClosed_subset (isClosed_tsupport _)
    intro ξ hξ
    exact ⟨A ξ, (hs (tsupport_comp_subset_preimage a hcomp hξ)).2, A.symm_apply_apply ξ⟩
  have hz : (0 : Space n) ∉ tsupport (fun ξ : Space n => a (q, A ξ)) := by
    intro h0
    have hzS := (hs (tsupport_comp_subset_preimage a hcomp h0)).2
    exact hzero (by simpa using hzS)
  constructor
  · intro p hp hptop
    exact (periodic_cutoff_norm_bound hcompact hdiff hz hh hf hfi hp hptop).trans
      (mul_le_mul' (hc q hq A) le_rfl)
  · intro B hB
    exact (periodic_cutoff_top_norm_bound hcompact hdiff hz hh hf hfi hB).trans
      (mul_le_mul' (hc q hq A) le_rfl)

end Periodic

end OAI.Analysis.Fourier.WavePackets
