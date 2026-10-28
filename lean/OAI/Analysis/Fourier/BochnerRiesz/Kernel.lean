import OAI.Analysis.Fourier.WavePackets.Uniform
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import OAI.Analysis.Fourier.LocalSmoothing.Definitions

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ContDiff

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

open OAI.Analysis.Fourier.WavePackets

/-- Uniform nonstationary phase with a smoothly varying amplitude.
This form applies to compact families of annular Sobolev multipliers. -/
theorem uniform_rapid_decay_joint_amplitude
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {U K : Set P} {S : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hS : IsCompact S) {φ : P → E → ℝ} {d : P × E → ℝ} {v : P → E} {a : P × E → ℂ}
    (hφc : ∀ p ∈ U, Continuous (φ p)) (hv : ContDiff ℝ ∞ v)
    (hφ : ∀ p ∈ U, ∀ ξ ∈ S, HasLineDerivAt ℝ (φ p) (d (p, ξ)) ξ (v p))
    (hd : ∀ q ∈ U ×ˢ S, ContDiffAt ℝ ∞ (fun q => (d q : ℂ)) q)
    (hd₀ : ∀ q ∈ U ×ˢ S, d q ≠ 0)
    (ha : ContDiffOn ℝ ∞ a (U ×ˢ Set.univ)) (hs : tsupport a ⊆ Set.univ ×ˢ S) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ h : ℝ, 0 < h →
      ‖∫ ξ, OAI.Analysis.Fourier.WavePackets.oscillation (φ p) h ξ * a (p, ξ) ∂μ‖ ≤ h ^ N * C := by
  let A := OAI.Analysis.Fourier.WavePackets.jointAmplitude (fun q => (d q : ℂ)) v a
  let B := fun k => OAI.Analysis.Fourier.WavePackets.quotientAmplitude (fun q => (d q : ℂ)) (A k)
  have hdn : ∀ q ∈ U ×ˢ S, (d q : ℂ) ≠ 0 := by
    intro q hq
    exact_mod_cast hd₀ q hq
  have hA (k : ℕ) : ContDiffOn ℝ ∞ (A k) (U ×ˢ Set.univ) ∧
      tsupport (A k) ⊆ Set.univ ×ˢ S := OAI.Analysis.Fourier.WavePackets.jointAmplitude_regular hU ha hv hs hd hdn k
  have hB (k : ℕ) : ContDiffOn ℝ ∞ (B k) (U ×ˢ Set.univ) ∧
      tsupport (B k) ⊆ Set.univ ×ˢ S :=
    ⟨OAI.Analysis.Fourier.WavePackets.joint_quotient_contDiffOn hU (hA k).1 (hA k).2 hd hdn,
      (OAI.Analysis.Fourier.WavePackets.tsupport_quotientAmplitude_subset _ _).trans (hA k).2⟩
  have hcont : ContinuousOn (A N) (K ×ˢ S) :=
    (hA N).1.continuousOn.mono (fun q hq => ⟨hKU hq.1, trivial⟩)
  obtain ⟨C, hCp, hC⟩ := ((hK.prod hS).image_of_continuousOn hcont).isBounded.exists_pos_norm_le
  refine ⟨C * μ.real S, mul_nonneg hCp.le ENNReal.toReal_nonneg, ?_⟩
  intro p hp h hh
  have hpU := hKU hp
  have hslice (k : ℕ) : tsupport (fun ξ => A k (p, ξ)) ⊆ S :=
    OAI.Analysis.Fourier.WavePackets.tsupport_slice_subset hS.isClosed (hA k).2 p
  have hbslice (k : ℕ) : tsupport (fun ξ => B k (p, ξ)) ⊆ S :=
    OAI.Analysis.Fourier.WavePackets.tsupport_slice_subset hS.isClosed (hB k).2 p
  have hdecay : ‖∫ ξ, OAI.Analysis.Fourier.WavePackets.oscillation (φ p) h ξ * a (p, ξ) ∂μ‖ ≤
      h ^ N * ∫ ξ, ‖A N (p, ξ)‖ ∂μ := by
    apply OAI.Analysis.Fourier.WavePackets.norm_integral_oscillation_mul_le (a := fun k ξ => A k (p, ξ))
      (b := fun k ξ => B k (p, ξ)) (d := fun ξ => d (p, ξ)) hh (v p) N
    · intro k _ ξ hξ
      exact hφ p hpU ξ (hbslice k hξ)
    · intro k _ ξ
      have hdiff := ((hB k).1.contDiffAt
        ((hU.prod isOpen_univ).mem_nhds (show (p, ξ) ∈ U ×ˢ Set.univ from ⟨hpU, trivial⟩))).differentiableAt (by simp)
      simpa [HasLineDerivAt, A, OAI.Analysis.Fourier.WavePackets.jointAmplitude, OAI.Analysis.Fourier.WavePackets.jointAmplitudeStep] using
        hdiff.hasFDerivAt.hasLineDerivAt (0, v p)
    · intro k _ ξ
      dsimp [B, OAI.Analysis.Fourier.WavePackets.quotientAmplitude]
      by_cases hξ : ξ ∈ S
      · field_simp [hdn (p, ξ) ⟨hpU, hξ⟩]
      · have hz : A k (p, ξ) = 0 := image_eq_zero_of_notMem_tsupport
          (fun hmem => hξ ((hA k).2 hmem).2)
        simp [hz]
    · intro k _
      have hsa : HasCompactSupport (fun ξ => A k (p, ξ)) :=
        hS.of_isClosed_subset (isClosed_tsupport _) (hslice k)
      exact ((OAI.Analysis.Fourier.WavePackets.continuous_oscillation (hφc p hpU) h).mul
        (OAI.Analysis.Fourier.WavePackets.contDiff_slice hU (hA k).1 hpU).continuous).integrable_of_hasCompactSupport hsa.mul_left
    · intro k _
      have hsb : HasCompactSupport (fun ξ => B k (p, ξ)) :=
        hS.of_isClosed_subset (isClosed_tsupport _) (hbslice k)
      exact ((OAI.Analysis.Fourier.WavePackets.continuous_oscillation (hφc p hpU) h).mul
        (OAI.Analysis.Fourier.WavePackets.contDiff_slice hU (hB k).1 hpU).continuous).integrable_of_hasCompactSupport hsb.mul_left
  apply hdecay.trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hh.le N)
  apply OAI.Analysis.Fourier.WavePackets.integral_norm_le_of_compact_support_bound hS
    (subset_trans (subset_tsupport _) (hslice N))
  intro ξ hξ
  exact hC _ ⟨(p, ξ), ⟨hp, hξ⟩, rfl⟩

/-- Compact smooth families with a common compact support have uniform
Fourier decay. The direction of the Fourier variable is another compact
parameter; integration by parts differentiates in that direction. -/
theorem uniform_fourier_integral_decay
    {Q E : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {K : Set Q} {S : Set E} (hK : IsCompact K) (hS : IsCompact S)
    {a : Q × E → ℂ} (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ Set.univ ×ˢ S) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ x : E, x ≠ 0 →
      ‖∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * a (q, ξ) ∂μ‖ ≤
        (‖x‖⁻¹) ^ N * C := by
  let U : Set (E × Q) := {p | 0 < ‖p.1‖}
  let K' : Set (E × Q) := Metric.sphere (0 : E) 1 ×ˢ K
  let a' : (E × Q) × E → ℂ := fun z ↦ a (z.1.2, z.2)
  have hU : IsOpen U := isOpen_lt continuous_const continuous_fst.norm
  have hK' : IsCompact K' := (isCompact_sphere (0 : E) 1).prod hK
  have hKU : K' ⊆ U := by
    intro p hp
    have hu : ‖p.1‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hp.1
    change 0 < ‖p.1‖
    rw [hu]
    norm_num
  have ha' : ContDiff ℝ ∞ a' := ha.comp (contDiff_fst.snd.prodMk contDiff_snd)
  have hs' : tsupport a' ⊆ Set.univ ×ˢ S := by
    intro z hz
    refine ⟨trivial, ?_⟩
    exact (hs (tsupport_comp_subset_preimage a (continuous_fst.snd.prodMk continuous_snd) hz)).2
  obtain ⟨C, hC, hb⟩ := uniform_rapid_decay_joint_amplitude (μ := μ) hU hK' hKU hS
    (φ := fun p ξ ↦ inner ℝ p.1 ξ) (d := fun z ↦ inner ℝ z.1.1 z.1.1)
    (v := fun p ↦ p.1) (a := a')
    (fun _ _ ↦ continuous_const.inner continuous_id) contDiff_fst
    (fun p _ ξ _ ↦ (innerSL ℝ p.1).hasFDerivAt.hasLineDerivAt p.1)
    (by
      intro z _
      have hdreal : ContDiff ℝ ∞ (fun z : (E × Q) × E ↦ inner ℝ z.1.1 z.1.1) :=
        ContDiff.inner (𝕜 := ℝ) contDiff_fst.fst contDiff_fst.fst
      exact (Complex.ofRealCLM.contDiff.comp hdreal).contDiffAt)
    (by
      intro z hz
      rw [real_inner_self_eq_norm_sq]
      exact pow_ne_zero _ (ne_of_gt hz.1))
    ha'.contDiffOn hs' N
  refine ⟨C, hC, ?_⟩
  intro q hq x hx
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let u : E := ‖x‖⁻¹ • x
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hnorm.ne']
  have hp : (u, q) ∈ K' := ⟨by simpa only [Metric.mem_sphere, dist_zero_right] using hu, hq⟩
  have hbound := hb (u, q) hp (‖x‖⁻¹) (inv_pos.mpr hnorm)
  have heq (ξ : E) : OAI.Analysis.Fourier.WavePackets.oscillation (fun ξ ↦ inner ℝ u ξ) (‖x‖⁻¹) ξ =
      Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) := by
    have hreal : inner ℝ u ξ / ‖x‖⁻¹ = inner ℝ x ξ := by
      dsimp only [u]
      rw [real_inner_smul_left]
      field_simp
    unfold OAI.Analysis.Fourier.WavePackets.oscillation
    rw [hreal]
    congr 1
    ring
  simpa only [heq, a'] using hbound

theorem bounded_and_power_decay {a F B D : ℝ} (ha : 0 ≤ a) (_ : 0 ≤ F)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (N : ℕ) (hsmall : F ≤ B)
    (hlarge : 0 < a → F ≤ (a⁻¹) ^ N * D) :
    F ≤ (2 ^ N * (B + D)) * (1 + a) ^ (-(N : ℝ)) := by
  have htwo : 0 ≤ (2 : ℝ) ^ N := by positivity
  have hmul : F * (1 + a) ^ N ≤ 2 ^ N * (B + D) := by
    by_cases haone : a ≤ 1
    · calc
        F * (1 + a) ^ N ≤ B * 2 ^ N :=
          mul_le_mul hsmall (pow_le_pow_left₀ (by linarith) (by linarith) N) (by positivity) hB
        _ ≤ 2 ^ N * (B + D) := by nlinarith
    · have hapos : 0 < a := by linarith
      calc
        F * (1 + a) ^ N ≤ ((a⁻¹) ^ N * D) * (2 * a) ^ N :=
          mul_le_mul (hlarge hapos) (pow_le_pow_left₀ (by linarith) (by linarith) N)
            (by positivity) (by positivity)
        _ = 2 ^ N * D := by rw [mul_pow, inv_pow]; field_simp
        _ ≤ 2 ^ N * (B + D) := by nlinarith
  rw [Real.rpow_neg (by linarith : 0 ≤ 1 + a), Real.rpow_natCast, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos (by linarith) N)).mpr hmul

theorem uniform_fourier_integral_bound
    {Q E : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {K : Set Q} {S : Set E} (hK : IsCompact K) (hS : IsCompact S)
    {a : Q × E → ℂ} (ha : Continuous a) (hs : tsupport a ⊆ Set.univ ×ˢ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ x : E,
      ‖∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * a (q, ξ) ∂μ‖ ≤ C := by
  obtain ⟨B, hB, hb⟩ := ((hK.prod hS).image ha).isBounded.exists_pos_norm_le
  refine ⟨B * μ.real S, mul_nonneg hB.le ENNReal.toReal_nonneg, ?_⟩
  intro q hq x
  calc
    _ ≤ ∫ ξ, ‖Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * a (q, ξ)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = ∫ ξ, ‖a (q, ξ)‖ ∂μ := by
      congr 1
      ext ξ
      simp [Complex.norm_exp]
    _ ≤ B * μ.real S := by
      apply OAI.Analysis.Fourier.WavePackets.integral_norm_le_of_compact_support_bound hS
        ((subset_tsupport _).trans (OAI.Analysis.Fourier.WavePackets.tsupport_slice_subset hS.isClosed hs q))
      intro ξ hξ
      exact hb _ ⟨(q, ξ), ⟨hq, hξ⟩, rfl⟩

theorem uniform_fourier_integral_polynomial_decay
    {Q E : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {K : Set Q} {S : Set E} (hK : IsCompact K) (hS : IsCompact S)
    {a : Q × E → ℂ} (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ Set.univ ×ˢ S) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ x : E,
      ‖∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * a (q, ξ) ∂μ‖ ≤
        C * (1 + ‖x‖) ^ (-(N : ℝ)) := by
  obtain ⟨B, hB, hb⟩ := uniform_fourier_integral_bound (μ := μ) hK hS ha.continuous hs
  obtain ⟨D, hD, hd⟩ := uniform_fourier_integral_decay (μ := μ) hK hS ha hs N
  refine ⟨2 ^ N * (B + D), by positivity, ?_⟩
  intro q hq x
  exact bounded_and_power_decay (norm_nonneg _) (norm_nonneg _) hB hD N (hb q hq x)
    (fun hx ↦ hd q hq x (norm_pos_iff.mp hx))

theorem continuous_positive_fourier_integral
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {g : E → ℂ}
    (hg : Integrable g μ) :
    Continuous (fun x : E ↦ ∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * g ξ ∂μ) := by
  have hnorm (x ξ : E) : ‖Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * g ξ‖ = ‖g ξ‖ := by
    simp [Complex.norm_exp]
  have hi (x : E) : Integrable (fun ξ ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * g ξ) μ := by
    have hc : Continuous (fun ξ : E ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))) := by fun_prop
    exact hg.mono (hc.aestronglyMeasurable.mul hg.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ξ ↦ (hnorm x ξ).le)
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_integral_filter_of_dominated_convergence (fun ξ ↦ ‖g ξ‖)
  · exact Filter.Eventually.of_forall fun z ↦ (hi z).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z ↦ Filter.Eventually.of_forall fun ξ ↦ (hnorm z ξ).le
  · exact hg.norm
  · exact Filter.Eventually.of_forall fun ξ ↦ Continuous.tendsto (by fun_prop) x

/-- A compact smooth family of compactly supported symbols has inverse
Fourier kernels with uniformly bounded L¹ norms. -/
theorem uniform_fourier_integral_L1
    {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q] {n : ℕ}
    {K : Set Q} {S : Set (Space n)} (hK : IsCompact K) (hS : IsCompact S)
    {a : Q × Space n → ℂ} (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ Set.univ ×ˢ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K,
      Integrable (fun x : Space n ↦ ∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * a (q, ξ)) ∧
      (∫ x : Space n, ‖∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * a (q, ξ)‖) ≤ C := by
  obtain ⟨D, hD, hb⟩ := uniform_fourier_integral_polynomial_decay (μ := (volume : Measure (Space n)))
    hK hS ha hs (n + 1)
  let w : Space n → ℝ := fun x ↦ D * (1 + ‖x‖) ^ (-((n + 1 : ℕ) : ℝ))
  have hw : Integrable w := by
    apply Integrable.const_mul
    apply integrable_one_add_norm
    simp [Space]
  refine ⟨∫ x, w x, integral_nonneg (fun x ↦ mul_nonneg hD (Real.rpow_nonneg (by positivity) _)), ?_⟩
  intro q hq
  have hslice : HasCompactSupport (fun ξ ↦ a (q, ξ)) :=
    hS.of_isClosed_subset (isClosed_tsupport _) (OAI.Analysis.Fourier.WavePackets.tsupport_slice_subset hS.isClosed hs q)
  have hqa : Integrable (fun ξ ↦ a (q, ξ)) :=
    (ha.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport hslice
  have hi : Integrable (fun x : Space n ↦ ∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * a (q, ξ)) :=
    hw.mono' (continuous_positive_fourier_integral hqa).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ hb q hq x)
  exact ⟨hi, integral_mono_ae hi.norm hw (Filter.Eventually.of_forall fun x ↦ hb q hq x)⟩

end OAI.Analysis.Fourier.BochnerRiesz
