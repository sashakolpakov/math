import OAI.Analysis.Fourier.SquareFunction.BoundaryConvergence
import OAI.Analysis.Fourier.SquareFunction.BoundaryEnvelope
import OAI.Analysis.Fourier.SquareFunction.Radius.Synthesis
import OAI.Analysis.Fourier.SquareFunction.Radius.Dyadic

open OAI.Analysis.Fourier.Wave

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform Set Filter
open scoped ENNReal Topology

theorem measurable_radiusInverseFourier {n : ℕ} {m : ℝ × Space n → ℂ}
    (hm : Measurable m) {F : Space n → ℂ} (hF : Measurable F) :
    Measurable (fun z : ℝ × Space n =>
      𝓕⁻ (fun ξ : Space n => m (z.1, ξ) * F ξ) z.2) := by
  have hi : StronglyMeasurable (fun z : (ℝ × Space n) × Space n =>
      spatialPhase z.1.2 z.2 * (m (z.1.1, z.2) * F z.2)) := by
    apply Measurable.stronglyMeasurable
    have hm' : Measurable (fun z : (ℝ × Space n) × Space n => m (z.1.1, z.2)) :=
      hm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    unfold spatialPhase
    fun_prop
  simpa only [fourierInv_eq_spatialPhase_smul, smul_eq_mul] using
    (hi.integral_prod_right' (ν := (volume : Measure (Space n)))).measurable

theorem measurable_radiusFourierIntegral {n : ℕ} {m : ℝ × Space n → ℂ}
    (hm : Measurable m) (f : SchwartzMap (Space n) ℂ) :
    Measurable (fun z : ℝ × Space n =>
      𝓕⁻ (fun ξ : Space n => m (z.1, ξ) * (𝓕 f : SchwartzMap (Space n) ℂ) ξ) z.2) := by
  have hi : StronglyMeasurable (fun z : (ℝ × Space n) × Space n =>
      spatialPhase z.1.2 z.2 * (m (z.1.1, z.2) * (𝓕 f : SchwartzMap (Space n) ℂ) z.2)) := by
    apply Measurable.stronglyMeasurable
    have hf := (𝓕 f : SchwartzMap (Space n) ℂ).continuous.measurable
    have hm' : Measurable (fun z : (ℝ × Space n) × Space n => m (z.1.1, z.2)) :=
      hm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    unfold spatialPhase
    fun_prop
  simpa only [fourierInv_eq_spatialPhase_smul, smul_eq_mul] using
    (hi.integral_prod_right' (ν := (volume : Measure (Space n)))).measurable

theorem measurable_boundaryRadiusDerivative {n : ℕ} (α : ℝ)
    (f : SchwartzMap (Space n) ℂ) :
    Measurable (fun z : ℝ × Space n => boundaryRadiusDerivative α z.1 f z.2) := by
  apply measurable_radiusFourierIntegral (n := n) (f := f)
    (m := fun z : ℝ × Space n => (radiusMultiplier α ‖z.2‖ z.1 : ℂ) *
      (OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff (4 * (z.1 - ‖z.2‖)) : ℂ))
  have hm : Measurable (fun z : ℝ × Space n => radiusMultiplier α ‖z.2‖ z.1) :=
    (measurable_radiusMultiplier α).comp ((continuous_norm.measurable.comp measurable_snd).prodMk measurable_fst)
  have hc := OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff.continuous.measurable
  fun_prop

theorem measurable_amplitudeShellProfile_symbol {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : Continuous A) (φ : SchwartzMap ℝ ℂ) (δ a : ℝ) :
    Measurable (fun z : ℝ × Space n =>
      A (z.1, a⁻¹ • z.2) * φ ((z.1 - a⁻¹ * ‖z.2‖) / δ)) := by
  have hφ := φ.continuous
  fun_prop

theorem measurable_radiusInverseFourier_fixed {n : ℕ} {m : ℝ × Space n → ℂ}
    (hm : Measurable m) {F : Space n → ℂ} (hF : Measurable F) (x : Space n) :
    Measurable (fun r : ℝ => 𝓕⁻ (fun ξ : Space n => m (r, ξ) * F ξ) x) := by
  have hi : StronglyMeasurable (fun z : ℝ × Space n =>
      spatialPhase x z.2 * (m (z.1, z.2) * F z.2)) := by
    apply Measurable.stronglyMeasurable
    have hm' : Measurable (fun z : ℝ × Space n => m (z.1, z.2)) := hm
    unfold spatialPhase
    fun_prop
  simpa only [fourierInv_eq_spatialPhase_smul, smul_eq_mul] using
    (hi.integral_prod_right' (ν := (volume : Measure (Space n)))).measurable

theorem measurable_amplitudeShellProfile {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : Continuous A) (φ : SchwartzMap ℝ ℂ) (δ a : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    Measurable (amplitudeShellProfile A φ δ a f x) := by
  unfold amplitudeShellProfile
  exact measurable_radiusInverseFourier_fixed
    (measurable_amplitudeShellProfile_symbol hA φ δ a)
    (OAI.Analysis.Fourier.BochnerRiesz.continuous_fourier_of_integrable (n := n) f.integrable).measurable x

noncomputable def dyadicBoundarySquare {n : ℕ} (α : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) : ℝ≥0∞ :=
  dyadicRadiusNorm (volume.restrict (Icc (1 : ℝ) 2)) (fun k r =>
    boundaryRadiusDerivative α r
      (OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate ((2 : ℝ) ^ k)⁻¹ (by positivity) f) ((2 : ℝ) ^ k • x))

theorem dyadicRadiusNorm_const_mul {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (u : ℤ → X → ℂ) (c : ℂ) :
    dyadicRadiusNorm μ (fun k x => c * u k x) = ‖c‖ₑ * dyadicRadiusNorm μ u := by
  unfold dyadicRadiusNorm
  have hn (k : ℤ) : eLpNorm (fun x => c * u k x) 2 μ = ‖c‖ₑ * eLpNorm (u k) 2 μ := by
    change eLpNorm (c • u k) 2 μ = _
    rw [eLpNorm_const_smul]
  simp only [hn,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), ENNReal.tsum_mul_left]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ← ENNReal.rpow_mul]
  norm_num

theorem dyadicBoundarySquare_le_envelope {n : ℕ} [NeZero n] {A : ℝ × Space n → ℂ}
    (hA : Continuous A) (hc : HasCompactSupport A) {α : ℝ} (hα : 1 / 2 < α)
    (ha : ∀ r ∈ Icc (1 : ℝ) 2, ∀ ξ : Space n, 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ 2 →
      A (r, ξ) = (2 * α * ‖ξ‖ ^ 2 * r ^ (-2 * α) * (r + ‖ξ‖) ^ (α - 1) : ℝ))
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    dyadicBoundarySquare α f x ≤ boundaryShellEnvelope A hA α 2 f x := by
  let g (k : ℤ) := OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate ((2 : ℝ) ^ k)⁻¹ (by positivity) f
  let u (j : ℕ) (k : ℤ) (r : ℝ) := Complex.ofReal (dyadicShellWidth 2 j ^ (α - 1)) *
    amplitudeShellProfile A (OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile (α - 1))
      (dyadicShellWidth 2 j) ((2 : ℝ) ^ k) f x r
  have H := dyadicRadiusNorm_le_tsum
    (μ := volume.restrict (Icc (1 : ℝ) 2)) (u := u)
    (v := fun k r => boundaryRadiusDerivative α r (g k) ((2 : ℝ) ^ k • x))
    (fun j k => ((measurable_amplitudeShellProfile hA _ _ _ f x).const_mul _).aestronglyMeasurable)
    (fun k => ((measurable_boundaryRadiusDerivative α (g k)).comp
      (show Measurable (fun r : ℝ => (r, (2 : ℝ) ^ k • x)) from
        measurable_id.prodMk measurable_const)).aestronglyMeasurable) ?_
  · apply H.trans_eq
    unfold boundaryShellEnvelope
    apply tsum_congr
    intro j
    rw [show u j = (fun k r => Complex.ofReal (dyadicShellWidth 2 j ^ (α - 1)) *
      amplitudeShellProfile A (OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile (α - 1))
        (dyadicShellWidth 2 j) ((2 : ℝ) ^ k) f x r) from rfl,
      dyadicRadiusNorm_const_mul, dyadicAmplitudeShellSquare_eq_radius_norms hA hc]
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (dyadicShellWidth_pos 2 j).le _)]
    rfl
  · intro k
    have hs : Icc (1 : ℝ) 2 ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le (by norm_num) hr.1
    have hi := ae_restrict_of_ae_restrict_of_subset hs (ae_integrable_radius_symbol_schwartz hα (g k))
    filter_upwards [hi, ae_restrict_mem measurableSet_Icc] with r hir hr
    have ht := boundaryRadiusDerivative_tendsto hA hc hr.1 hr.2 (ha r hr) (g k) hir ((2 : ℝ) ^ k • x)
    convert ht using 1
    funext N
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [u]
    congr 1
    exact (amplitudeShellRadiusMap_dilate hA hc _ _
      (a := (2 : ℝ) ^ k) (by positivity) f x ⟨r, hr⟩).symm

end OAI.Analysis.Fourier.SquareFunction
