import OAI.Analysis.Fourier.WavePackets.Oscillatory

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped RealInnerProductSpace ContDiff

section JointAmplitudes

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def jointAmplitudeStep (d : P × E → ℂ) (v : P → E)
    (a : P × E → ℂ) (q : P × E) : ℂ :=
  fderiv ℝ (quotientAmplitude d a) q (0, v q.1)

theorem tsupport_jointAmplitudeStep_subset (d : P × E → ℂ) (v : P → E)
    (a : P × E → ℂ) : tsupport (jointAmplitudeStep d v a) ⊆ tsupport a := by
  apply (show tsupport (jointAmplitudeStep d v a) ⊆ tsupport (quotientAmplitude d a) from ?_).trans
    (tsupport_quotientAmplitude_subset d a)
  apply closure_minimal ?_ (isClosed_tsupport _)
  intro q hq
  by_contra h
  have hz := fderiv_of_notMem_tsupport ℝ h
  exact hq (by simp [jointAmplitudeStep, hz])

theorem joint_quotient_contDiffOn {U : Set P} (hU : IsOpen U)
    {S : Set E} {a d : P × E → ℂ}
    (ha : ContDiffOn ℝ ∞ a (U ×ˢ Set.univ))
    (hs : tsupport a ⊆ Set.univ ×ˢ S)
    (hd : ∀ q ∈ U ×ˢ S, ContDiffAt ℝ ∞ d q)
    (hd₀ : ∀ q ∈ U ×ˢ S, d q ≠ 0) :
    ContDiffOn ℝ ∞ (quotientAmplitude d a) (U ×ˢ Set.univ) := by
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  by_cases hqs : q.2 ∈ S
  · have haq : ContDiffAt ℝ ∞ a q := ha.contDiffAt ((hU.prod isOpen_univ).mem_nhds hq)
    unfold quotientAmplitude
    simp_rw [div_eq_mul_inv]
    exact haq.mul ((hd q ⟨hq.1, hqs⟩).inv (hd₀ q ⟨hq.1, hqs⟩))
  · have hqz : q ∉ tsupport (quotientAmplitude d a) := by
      intro h
      exact hqs (hs (tsupport_quotientAmplitude_subset d a h)).2
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hqz)

theorem jointAmplitudeStep_contDiffOn {U : Set P} (hU : IsOpen U)
    {S : Set E} {a d : P × E → ℂ} {v : P → E}
    (ha : ContDiffOn ℝ ∞ a (U ×ˢ Set.univ)) (hv : ContDiff ℝ ∞ v)
    (hs : tsupport a ⊆ Set.univ ×ˢ S)
    (hd : ∀ q ∈ U ×ˢ S, ContDiffAt ℝ ∞ d q)
    (hd₀ : ∀ q ∈ U ×ˢ S, d q ≠ 0) :
    ContDiffOn ℝ ∞ (jointAmplitudeStep d v a) (U ×ˢ Set.univ) := by
  have hq := joint_quotient_contDiffOn hU ha hs hd hd₀
  apply (hq.fderiv_of_isOpen (hU.prod isOpen_univ) (by simp)).clm_apply
  exact (contDiff_const.prodMk (hv.comp contDiff_fst)).contDiffOn

noncomputable def jointAmplitude (d : P × E → ℂ) (v : P → E)
    (a : P × E → ℂ) : ℕ → P × E → ℂ
  | 0 => a
  | k + 1 => jointAmplitudeStep d v (jointAmplitude d v a k)

theorem jointAmplitude_regular {U : Set P} (hU : IsOpen U)
    {S : Set E} {a d : P × E → ℂ} {v : P → E}
    (ha : ContDiffOn ℝ ∞ a (U ×ˢ Set.univ)) (hv : ContDiff ℝ ∞ v)
    (hs : tsupport a ⊆ Set.univ ×ˢ S)
    (hd : ∀ q ∈ U ×ˢ S, ContDiffAt ℝ ∞ d q)
    (hd₀ : ∀ q ∈ U ×ˢ S, d q ≠ 0) (k : ℕ) :
    ContDiffOn ℝ ∞ (jointAmplitude d v a k) (U ×ˢ Set.univ) ∧
      tsupport (jointAmplitude d v a k) ⊆ Set.univ ×ˢ S := by
  induction k with
  | zero => exact ⟨ha, hs⟩
  | succ k ih =>
    exact ⟨jointAmplitudeStep_contDiffOn hU ih.1 hv ih.2 hd hd₀,
      (tsupport_jointAmplitudeStep_subset d v _).trans ih.2⟩

theorem contDiff_slice {U : Set P} (hU : IsOpen U) {a : P × E → ℂ}
    (ha : ContDiffOn ℝ ∞ a (U ×ˢ Set.univ)) {p : P} (hp : p ∈ U) :
    ContDiff ℝ ∞ (fun ξ => a (p, ξ)) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  exact (ha.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hp, trivial⟩)).comp ξ
    (contDiffAt_const.prodMk contDiffAt_id)

omit [NormedSpace ℝ P] [NormedSpace ℝ E] in
theorem tsupport_slice_subset {S : Set E} (hS : IsClosed S) {a : P × E → ℂ}
    (ha : tsupport a ⊆ Set.univ ×ˢ S) (p : P) :
    tsupport (fun ξ => a (p, ξ)) ⊆ S := by
  apply closure_minimal ?_ hS
  intro ξ hξ
  exact (ha (subset_tsupport _ hξ)).2

end JointAmplitudes

theorem integral_norm_le_of_compact_support_bound
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [T2Space E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {S : Set E} (hS : IsCompact S)
    {f : E → ℂ} (hf : Function.support f ⊆ S) {C : ℝ}
    (hC : ∀ ξ ∈ S, ‖f ξ‖ ≤ C) : (∫ ξ, ‖f ξ‖ ∂μ) ≤ C * μ.real S := by
  have heq : (∫ ξ, ‖f ξ‖ ∂μ) = ∫ ξ in S, ‖f ξ‖ ∂μ := by
    rw [← integral_indicator hS.measurableSet]
    congr 1
    ext ξ
    by_cases hξ : ξ ∈ S
    · simp [hξ]
    · have hz : f ξ = 0 := by
        by_contra hn
        exact hξ (hf hn)
      simp [hξ, hz]
  rw [heq]
  have hb := norm_setIntegral_le_of_norm_le_const_ae' (μ := μ) (s := S) (f := fun ξ => ‖f ξ‖)
    hS.measure_lt_top (Filter.Eventually.of_forall fun ξ hξ => by simpa using hC ξ hξ)
  have hn : 0 ≤ ∫ ξ in S, ‖f ξ‖ ∂μ := integral_nonneg (fun ξ => norm_nonneg (f ξ))
  simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using hb

/-- Compact parameter sets give uniform constants for repeated nonstationary
phase integration. The same compact frequency support is used at every stage. -/
theorem uniform_rapid_decay_of_nonstationary_phase
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {U K : Set P} {S : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hS : IsCompact S) {φ : P → E → ℝ} {d : P × E → ℝ} {v : P → E} {a : E → ℂ}
    (hφc : ∀ p ∈ U, Continuous (φ p)) (hv : ContDiff ℝ ∞ v)
    (hφ : ∀ p ∈ U, ∀ ξ ∈ S, HasLineDerivAt ℝ (φ p) (d (p, ξ)) ξ (v p))
    (hd : ∀ q ∈ U ×ˢ S, ContDiffAt ℝ ∞ (fun q => (d q : ℂ)) q)
    (hd₀ : ∀ q ∈ U ×ˢ S, d q ≠ 0)
    (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ S) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ h : ℝ, 0 < h →
      ‖∫ ξ, oscillation (φ p) h ξ * a ξ ∂μ‖ ≤ h ^ N * C := by
  let A := jointAmplitude (fun q => (d q : ℂ)) v (fun q : P × E => a q.2)
  let B := fun k => quotientAmplitude (fun q => (d q : ℂ)) (A k)
  have hdn : ∀ q ∈ U ×ˢ S, (d q : ℂ) ≠ 0 := by
    intro q hq
    exact_mod_cast hd₀ q hq
  have hstart : tsupport (fun q : P × E => a q.2) ⊆ Set.univ ×ˢ S := by
    intro q hq
    exact ⟨trivial, hs (tsupport_comp_subset_preimage a continuous_snd hq)⟩
  have hA (k : ℕ) : ContDiffOn ℝ ∞ (A k) (U ×ˢ Set.univ) ∧
      tsupport (A k) ⊆ Set.univ ×ˢ S :=
    jointAmplitude_regular hU (ha.comp contDiff_snd).contDiffOn hv hstart hd hdn k
  have hB (k : ℕ) : ContDiffOn ℝ ∞ (B k) (U ×ˢ Set.univ) ∧
      tsupport (B k) ⊆ Set.univ ×ˢ S :=
    ⟨joint_quotient_contDiffOn hU (hA k).1 (hA k).2 hd hdn,
      (tsupport_quotientAmplitude_subset _ _).trans (hA k).2⟩
  have hcont : ContinuousOn (A N) (K ×ˢ S) :=
    (hA N).1.continuousOn.mono (fun q hq => ⟨hKU hq.1, trivial⟩)
  obtain ⟨C, hCp, hC⟩ := ((hK.prod hS).image_of_continuousOn hcont).isBounded.exists_pos_norm_le
  refine ⟨C * μ.real S, mul_nonneg hCp.le ENNReal.toReal_nonneg, ?_⟩
  intro p hp h hh
  have hpU := hKU hp
  have hslice (k : ℕ) : tsupport (fun ξ => A k (p, ξ)) ⊆ S :=
    tsupport_slice_subset hS.isClosed (hA k).2 p
  have hbslice (k : ℕ) : tsupport (fun ξ => B k (p, ξ)) ⊆ S :=
    tsupport_slice_subset hS.isClosed (hB k).2 p
  have hdecay : ‖∫ ξ, oscillation (φ p) h ξ * a ξ ∂μ‖ ≤
      h ^ N * ∫ ξ, ‖A N (p, ξ)‖ ∂μ := by
    apply norm_integral_oscillation_mul_le (a := fun k ξ => A k (p, ξ))
      (b := fun k ξ => B k (p, ξ)) (d := fun ξ => d (p, ξ)) hh (v p) N
    · intro k _ ξ hξ
      exact hφ p hpU ξ (hbslice k hξ)
    · intro k _ ξ
      have hdiff := ((hB k).1.contDiffAt
        ((hU.prod isOpen_univ).mem_nhds (show (p, ξ) ∈ U ×ˢ Set.univ from ⟨hpU, trivial⟩))).differentiableAt (by simp)
      simpa [HasLineDerivAt, A, jointAmplitude, jointAmplitudeStep] using
        hdiff.hasFDerivAt.hasLineDerivAt (0, v p)
    · intro k _ ξ
      dsimp [B, quotientAmplitude]
      by_cases hξ : ξ ∈ S
      · field_simp [hdn (p, ξ) ⟨hpU, hξ⟩]
      · have hz : A k (p, ξ) = 0 := image_eq_zero_of_notMem_tsupport
          (fun hmem => hξ ((hA k).2 hmem).2)
        simp [hz]
    · intro k _
      have hsa : HasCompactSupport (fun ξ => A k (p, ξ)) :=
        hS.of_isClosed_subset (isClosed_tsupport _) (hslice k)
      exact ((continuous_oscillation (hφc p hpU) h).mul
        (contDiff_slice hU (hA k).1 hpU).continuous).integrable_of_hasCompactSupport
        hsa.mul_left
    · intro k _
      have hsb : HasCompactSupport (fun ξ => B k (p, ξ)) :=
        hS.of_isClosed_subset (isClosed_tsupport _) (hbslice k)
      exact ((continuous_oscillation (hφc p hpU) h).mul
        (contDiff_slice hU (hB k).1 hpU).continuous).integrable_of_hasCompactSupport
        hsb.mul_left
  apply hdecay.trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hh.le N)
  apply integral_norm_le_of_compact_support_bound hS
    (subset_trans (subset_tsupport _) (hslice N))
  intro ξ hξ
  exact hC _ ⟨(p, ξ), ⟨hp, hξ⟩, rfl⟩

section WaveParameters

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def waveParameterDomain : Set (E × ℝ) :=
  {p | (3 : ℝ) / 4 < ‖p.1‖ ∧ |p.2| < (7 : ℝ) / 10}

def waveParameterCompact : Set (E × ℝ) :=
  Metric.sphere 0 1 ×ˢ Set.Icc 0 ((2 : ℝ) / 3)

noncomputable def jointWaveSlope (q : (E × ℝ) × E) : ℝ :=
  ‖q.1.1‖ ^ 2 - q.1.2 * (⟪q.2, q.1.1⟫ / ‖q.2‖)

omit [InnerProductSpace ℝ E] in
theorem isOpen_waveParameterDomain : IsOpen (waveParameterDomain (E := E)) := by
  apply (isOpen_lt continuous_const (continuous_norm.comp continuous_fst)).inter
  exact isOpen_lt (continuous_abs.comp continuous_snd) continuous_const

omit [InnerProductSpace ℝ E] in
theorem waveParameterCompact_subset_domain :
    waveParameterCompact (E := E) ⊆ waveParameterDomain := by
  intro p hp
  have hn : ‖p.1‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hp.1
  change (3 : ℝ) / 4 < ‖p.1‖ ∧ |p.2| < (7 : ℝ) / 10
  rw [hn, abs_of_nonneg hp.2.1]
  constructor <;> linarith [hp.2.2]

theorem jointWaveSlope_pos {p : E × ℝ} (hp : p ∈ waveParameterDomain) (ξ : E) :
    0 < jointWaveSlope (p, ξ) := by
  have hr : |⟪ξ, p.1⟫ / ‖ξ‖| ≤ ‖p.1‖ := by
    by_cases hz : ξ = 0
    · simp [hz]
    · rw [abs_div, abs_of_pos (norm_pos_iff.mpr hz)]
      apply (div_le_iff₀ (norm_pos_iff.mpr hz)).mpr
      simpa only [mul_comm] using abs_real_inner_le_norm ξ p.1
  have hm := mul_le_mul_of_nonneg_left hr (abs_nonneg p.2)
  have ht : p.2 * (⟪ξ, p.1⟫ / ‖ξ‖) ≤ |p.2| * ‖p.1‖ := by
    calc
      _ ≤ |p.2 * (⟪ξ, p.1⟫ / ‖ξ‖)| := le_abs_self _
      _ ≤ _ := by simpa only [abs_mul] using hm
  have hn : 0 < ‖p.1‖ := by have := hp.1; linarith
  have hd : |p.2| < ‖p.1‖ := by have := hp.1; have := hp.2; linarith
  have hprod := mul_lt_mul_of_pos_right hd hn
  dsimp [jointWaveSlope]
  nlinarith

theorem jointWaveSlope_contDiffAt {q : (E × ℝ) × E} (hq : q.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => (jointWaveSlope q : ℂ)) q := by
  have hw : ContDiffAt ℝ ∞ (fun q : (E × ℝ) × E => q.1.1) q := contDiffAt_fst.fst
  have ht : ContDiffAt ℝ ∞ (fun q : (E × ℝ) × E => q.1.2) q := contDiffAt_fst.snd
  have hξ : ContDiffAt ℝ ∞ (fun q : (E × ℝ) × E => q.2) q := contDiffAt_snd
  have hn := (contDiffAt_norm ℝ hq).comp q hξ
  have hs : ContDiffAt ℝ ∞ jointWaveSlope q :=
    (hw.norm_sq ℝ).sub (ht.mul ((hξ.inner ℝ hw).div hn (norm_ne_zero_iff.mpr hq)))
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp q hs

theorem uniform_normalized_wave_decay [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {a : E → ℂ} (ha : ContDiff ℝ ∞ a) (hzero : (0 : E) ∉ tsupport a)
    (hs : HasCompactSupport a) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (omega : E) (t : ℝ), ‖omega‖ = 1 → 0 ≤ t → t ≤ (2 : ℝ) / 3 →
      ∀ h : ℝ, 0 < h →
        ‖∫ ξ, oscillation (euclideanWavePhase omega t) h ξ * a ξ ∂μ‖ ≤ h ^ N * C := by
  have hk : IsCompact (waveParameterCompact (E := E)) :=
    (isCompact_sphere 0 1).prod isCompact_Icc
  obtain ⟨C, hC, hb⟩ := uniform_rapid_decay_of_nonstationary_phase
    (μ := μ) (φ := fun p => euclideanWavePhase p.1 p.2) (d := jointWaveSlope)
    (v := fun p : E × ℝ => p.1) isOpen_waveParameterDomain hk
    waveParameterCompact_subset_domain hs
    (by intro p _; unfold euclideanWavePhase; fun_prop) contDiff_fst
    (by
      intro p _ ξ hξ
      have hξ₀ : ξ ≠ 0 := by intro hz; exact hzero (hz ▸ hξ)
      simpa only [jointWaveSlope, real_inner_self_eq_norm_sq] using
        hasLineDerivAt_euclideanWavePhase p.1 ξ p.1 p.2 hξ₀)
    (by
      intro q hq
      apply jointWaveSlope_contDiffAt
      intro hz
      exact hzero (hz ▸ hq.2))
    (by intro q hq; exact (jointWaveSlope_pos hq.1 q.2).ne') ha (Set.Subset.refl _) N
  refine ⟨C, hC, ?_⟩
  intro omega t homega ht₀ ht₁ h hh
  apply hb (omega, t) ?_ h hh
  exact ⟨by simpa [Metric.mem_sphere, dist_zero_right] using homega, ht₀, ht₁⟩

/-- Uniform off-cone decay, before inserting the semiclassical kernel's
Jacobian prefactor. The constant is independent of `X`, `T`, and `h`. -/
theorem uniform_wave_integral_off_cone [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {a : E → ℂ} (ha : ContDiff ℝ ∞ a) (hzero : (0 : E) ∉ tsupport a)
    (hs : HasCompactSupport a) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : E) (T h : ℝ), 3 ≤ ‖X‖ → 0 ≤ T → T ≤ 2 → 0 < h →
      ‖∫ ξ, oscillation (euclideanWavePhase X T) h ξ * a ξ ∂μ‖ ≤ (h / ‖X‖) ^ N * C := by
  obtain ⟨C, hC, hb⟩ := uniform_normalized_wave_decay (μ := μ) ha hzero hs N
  refine ⟨C, hC, ?_⟩
  intro X T h hX hT₀ hT₁ hh
  have hr : 0 < ‖X‖ := by linarith
  let omega : E := ‖X‖⁻¹ • X
  let t : ℝ := T / ‖X‖
  have homega : ‖omega‖ = 1 := by
    simp only [omega, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact inv_mul_cancel₀ hr.ne'
  have ht₀ : 0 ≤ t := div_nonneg hT₀ hr.le
  have ht₁ : t ≤ (2 : ℝ) / 3 := by
    apply (div_le_iff₀ hr).mpr
    nlinarith
  have heq (ξ : E) : oscillation (euclideanWavePhase omega t) (h / ‖X‖) ξ =
      oscillation (euclideanWavePhase X T) h ξ := by
    have hp : euclideanWavePhase omega t ξ / (h / ‖X‖) = euclideanWavePhase X T ξ / h := by
      simp only [euclideanWavePhase, omega, t, real_inner_smul_left]
      field_simp
    simp only [oscillation, hp]
  simpa only [heq] using hb omega t homega ht₀ ht₁ (h / ‖X‖) (div_pos hh hr)

/-- The rescaled Euclidean kernel, with the Fourier normalization absorbed
into the amplitude. -/
noncomputable def semiclassicalWaveKernel [MeasurableSpace E]
    (μ : Measure E) (a : E → ℂ) (h T : ℝ) (X : E) : ℂ :=
  ((h : ℂ) ^ Module.finrank ℝ E)⁻¹ *
    ∫ ξ, oscillation (euclideanWavePhase X T) h ξ * a ξ ∂μ

/-- The full uniform off-cone kernel estimate, in the equivalent decay weight
`(1 + ‖X‖)⁻ᴺ`. This includes the dimension-dependent Jacobian `h⁻ⁿ`. -/
theorem semiclassicalWaveKernel_off_cone [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {a : E → ℂ} (ha : ContDiff ℝ ∞ a) (hzero : (0 : E) ∉ tsupport a)
    (hs : HasCompactSupport a) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : E) (T h : ℝ), 3 ≤ ‖X‖ → 0 ≤ T → T ≤ 2 → 0 < h →
      ‖semiclassicalWaveKernel μ a h T X‖ ≤ C * h ^ N / (1 + ‖X‖) ^ N := by
  let n := Module.finrank ℝ E
  obtain ⟨C, hC, hb⟩ := uniform_wave_integral_off_cone (μ := μ) ha hzero hs (N + n)
  refine ⟨C * 2 ^ N, mul_nonneg hC (by positivity), ?_⟩
  intro X T h hX hT₀ hT₁ hh
  have hr : 0 < ‖X‖ := by linarith
  have hr₁ : 1 ≤ ‖X‖ := by linarith
  have hbase : 1 + ‖X‖ ≤ 2 * ‖X‖ := by linarith
  have hpowers : (1 + ‖X‖) ^ N ≤ 2 ^ N * ‖X‖ ^ (N + n) := by
    calc
      _ ≤ (2 * ‖X‖) ^ N := pow_le_pow_left₀ (by positivity) hbase N
      _ = 2 ^ N * ‖X‖ ^ N := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr₁ (Nat.le_add_right N n)) (by positivity)
  calc
    ‖semiclassicalWaveKernel μ a h T X‖ =
        (h ^ n)⁻¹ * ‖∫ ξ, oscillation (euclideanWavePhase X T) h ξ * a ξ ∂μ‖ := by
      simp only [semiclassicalWaveKernel, n, norm_mul, norm_inv, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
    _ ≤ (h ^ n)⁻¹ * ((h / ‖X‖) ^ (N + n) * C) :=
      mul_le_mul_of_nonneg_left (hb X T h hX hT₀ hT₁ hh) (by positivity)
    _ = C * h ^ N / ‖X‖ ^ (N + n) := by
      rw [div_pow, pow_add h]
      field_simp
    _ ≤ C * 2 ^ N * h ^ N / (1 + ‖X‖) ^ N := by
      apply (div_le_div_iff₀ (pow_pos hr _) (by positivity)).mpr
      convert mul_le_mul_of_nonneg_left hpowers (mul_nonneg hC (pow_nonneg hh.le N)) using 1
      ring

/-- The exact off-cone bound with arbitrary positive real decay exponent and
Japanese-bracket weight from `sections/transfer.tex`. -/
theorem semiclassicalWaveKernel_off_cone_rpow [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {a : E → ℂ} (ha : ContDiff ℝ ∞ a) (hzero : (0 : E) ∉ tsupport a)
    (hs : HasCompactSupport a) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : E) (T h : ℝ), 3 ≤ ‖X‖ → 1 ≤ T → T ≤ 2 →
      0 < h → h ≤ 1 → ‖semiclassicalWaveKernel μ a h T X‖ ≤
        C * h ^ N * (Real.sqrt (1 + ‖X‖ ^ 2)) ^ (-N) := by
  obtain ⟨C, hC, hb⟩ := semiclassicalWaveKernel_off_cone (μ := μ) ha hzero hs ⌈N⌉₊
  refine ⟨C, hC, ?_⟩
  intro X T h hX hT₀ hT₁ hh hh₁
  have hr : 0 < 1 + ‖X‖ := by positivity
  have hq : 0 < h / (1 + ‖X‖) := div_pos hh hr
  have hq₁ : h / (1 + ‖X‖) ≤ 1 := by
    apply (div_le_one hr).mpr
    linarith [norm_nonneg X]
  have hpower : (h / (1 + ‖X‖)) ^ ⌈N⌉₊ ≤ (h / (1 + ‖X‖)) ^ N := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hq hq₁ (Nat.le_ceil N)
  have hsqrt : 0 < Real.sqrt (1 + ‖X‖ ^ 2) := by positivity
  have hsqrtle : Real.sqrt (1 + ‖X‖ ^ 2) ≤ 1 + ‖X‖ := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [norm_nonneg X]
  calc
    ‖semiclassicalWaveKernel μ a h T X‖ ≤ C * h ^ ⌈N⌉₊ / (1 + ‖X‖) ^ ⌈N⌉₊ :=
      hb X T h hX (by linarith) hT₁ hh
    _ = C * (h / (1 + ‖X‖)) ^ ⌈N⌉₊ := by rw [div_pow]; ring
    _ ≤ C * (h / (1 + ‖X‖)) ^ N := mul_le_mul_of_nonneg_left hpower hC
    _ = C * h ^ N / (1 + ‖X‖) ^ N := by rw [Real.div_rpow hh.le hr.le]; ring
    _ ≤ C * h ^ N / (Real.sqrt (1 + ‖X‖ ^ 2)) ^ N :=
      div_le_div_of_nonneg_left (mul_nonneg hC (Real.rpow_nonneg hh.le _))
        (Real.rpow_pos_of_pos hsqrt _) (Real.rpow_le_rpow hsqrt.le hsqrtle hN.le)
    _ = C * h ^ N * (Real.sqrt (1 + ‖X‖ ^ 2)) ^ (-N) := by
      rw [Real.rpow_neg hsqrt.le, div_eq_mul_inv]

end WaveParameters

end OAI.Analysis.Fourier.WavePackets
