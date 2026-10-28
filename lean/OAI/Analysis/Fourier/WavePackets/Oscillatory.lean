import Mathlib

/-!
Integration by parts for the oscillatory kernels in `sections/transfer.tex`.
The derivative and integrability hypotheses below are the explicit analytic
conditions to be checked for each amplitude; the identities themselves are proved.
-/

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped RealInnerProductSpace ContDiff

theorem hasLineDerivAt_euclidean_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ξ v : E) (hξ : ξ ≠ 0) :
    HasLineDerivAt ℝ (fun y : E => ‖y‖) (⟪ξ, v⟫ / ‖ξ‖) ξ v := by
  have hline : HasDerivAt (fun t : ℝ => ξ + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add ξ
  have hnorm := hline.norm_sq
  have hsqrt := hnorm.sqrt (by simp [hξ])
  change HasDerivAt (fun t : ℝ => ‖ξ + t • v‖) _ 0
  convert hsqrt using 1
  · ext t
    simp
  · simp
    ring

/-- The phase in the semiclassically rescaled Euclidean half-wave kernel. -/
noncomputable def euclideanWavePhase {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X : E) (T : ℝ) (ξ : E) : ℝ :=
  ⟪X, ξ⟫ - T * ‖ξ‖

theorem hasLineDerivAt_euclideanWavePhase {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X ξ v : E) (T : ℝ) (hξ : ξ ≠ 0) :
    HasLineDerivAt ℝ (euclideanWavePhase X T)
      (⟪X, v⟫ - T * (⟪ξ, v⟫ / ‖ξ‖)) ξ v := by
  have hline : HasDerivAt (fun t : ℝ => ξ + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add ξ
  have hi := (innerSL ℝ X).hasFDerivAt.comp_hasDerivAt 0 hline
  have hn := hasLineDerivAt_euclidean_norm ξ v hξ
  change HasDerivAt (fun t : ℝ => ‖ξ + t • v‖) _ 0 at hn
  change HasDerivAt (fun t : ℝ => ⟪X, ξ + t • v⟫ - T * ‖ξ + t • v‖) _ 0
  exact hi.sub (hn.const_mul T)

/-- Any unit direction aligned with `X` gives a uniformly nonzero phase
derivative away from the cone. -/
theorem euclideanWavePhase_slope_lower_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X ξ v : E) {T : ℝ} (hξ : ξ ≠ 0)
    (hv : ‖v‖ = 1) (halign : ⟪X, v⟫ = ‖X‖)
    (hT₀ : 0 ≤ T) (hT₁ : T ≤ 2) (hX : 3 ≤ ‖X‖) :
    ‖X‖ / 3 ≤ ⟪X, v⟫ - T * (⟪ξ, v⟫ / ‖ξ‖) := by
  have hξp : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hinner : ⟪ξ, v⟫ ≤ ‖ξ‖ := by
    simpa only [hv, mul_one] using real_inner_le_norm ξ v
  have hdiv : ⟪ξ, v⟫ / ‖ξ‖ ≤ 1 := (div_le_one hξp).mpr hinner
  have hmul := mul_le_mul_of_nonneg_left hdiv hT₀
  rw [halign]
  linarith

/-- The required direction always exists: choose the unit vector pointing
towards the observation point. Its derivative lower bound is uniform over
all nonzero frequencies and all observation times in `[0,2]`. -/
theorem exists_off_cone_direction {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X : E) (hX : 3 ≤ ‖X‖) :
    ∃ v : E, ‖v‖ = 1 ∧ ⟪X, v⟫ = ‖X‖ ∧ ∀ (ξ : E) (T : ℝ), ξ ≠ 0 → 0 ≤ T → T ≤ 2 →
      ‖X‖ / 3 ≤ ⟪X, v⟫ - T * (⟪ξ, v⟫ / ‖ξ‖) := by
  have hx : 0 < ‖X‖ := by linarith
  let v : E := ‖X‖⁻¹ • X
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx)]
    exact inv_mul_cancel₀ hx.ne'
  have ha : ⟪X, v⟫ = ‖X‖ := by
    simp only [v, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  refine ⟨v, hv, ha, ?_⟩
  intro ξ T hξ hT₀ hT₁
  exact euclideanWavePhase_slope_lower_bound X ξ v hξ hv ha hT₀ hT₁ hX

noncomputable def oscillation {E : Type*} (φ : E → ℝ) (h : ℝ) (x : E) : ℂ :=
  Complex.exp (((φ x / h : ℝ) : ℂ) * Complex.I)

theorem continuous_oscillation {E : Type*} [TopologicalSpace E]
    {φ : E → ℝ} (hφ : Continuous φ) (h : ℝ) : Continuous (oscillation φ h) := by
  unfold oscillation
  fun_prop

theorem norm_oscillation {E : Type*} (φ : E → ℝ) (h : ℝ) (x : E) :
    ‖oscillation φ h x‖ = 1 := by
  simp [oscillation, Complex.norm_exp]

theorem hasLineDerivAt_oscillation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {φ : E → ℝ} {d h : ℝ} {x v : E}
    (hφ : HasLineDerivAt ℝ φ d x v) :
    HasLineDerivAt ℝ (oscillation φ h)
      ((Complex.I / (h : ℂ)) * (d : ℂ) * oscillation φ h x) x v := by
  change HasDerivAt (fun t : ℝ => oscillation φ h (x + t • v)) _ 0
  change HasDerivAt (fun t : ℝ => φ (x + t • v)) d 0 at hφ
  convert ((hφ.div_const h).ofReal_comp.mul_const Complex.I).cexp using 1
  · ext t
    rfl
  · simp [oscillation, Complex.ofReal_div]
    ring

/-- One integration by parts in a fixed direction, with the amplitude written
as the directional phase derivative times `b`. This is the division by the
nonstationary phase gradient used in the off-cone argument. -/
theorem oscillatory_integration_by_parts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {φ d : E → ℝ} {b b' : E → ℂ} {h : ℝ} (hh : h ≠ 0) (v : E)
    (hφ : ∀ x ∈ tsupport b, HasLineDerivAt ℝ φ (d x) x v)
    (hb : ∀ x, HasLineDerivAt ℝ b (b' x) x v)
    (hint : Integrable (fun x => oscillation φ h x * ((d x : ℂ) * b x)) μ)
    (hint' : Integrable (fun x => oscillation φ h x * b' x) μ)
    (hintb : Integrable (fun x => oscillation φ h x * b x) μ) :
    (∫ x, oscillation φ h x * ((d x : ℂ) * b x) ∂μ) =
      Complex.I * (h : ℂ) * ∫ x, oscillation φ h x * b' x ∂μ := by
  have hleft : Integrable
      (fun x => ((Complex.I / (h : ℂ)) * (d x : ℂ) * oscillation φ h x) * b x) μ := by
    convert hint.const_mul (Complex.I / (h : ℂ)) using 1
    ext x
    ring
  have hi := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℂ) hleft hint' hintb
    (fun x hx => hasLineDerivAt_oscillation (hφ x hx)) (fun x _ => hb x)
  change (∫ x, oscillation φ h x * b' x ∂μ) =
    -(∫ x, ((Complex.I / (h : ℂ)) * (d x : ℂ) * oscillation φ h x) * b x ∂μ) at hi
  have hi' : (∫ x, oscillation φ h x * b' x ∂μ) =
      -(Complex.I / (h : ℂ) * ∫ x, oscillation φ h x * ((d x : ℂ) * b x) ∂μ) := by
    rw [← integral_const_mul]
    convert hi using 2
    congr 1
    ext x
    ring
  rw [hi']
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  field_simp
  simp [Complex.I_sq]

/-- Repeated integration by parts with explicit amplitude recursion. At each
stage `a k = d * b k` and `a (k+1)` is the derivative of `b k`. -/
theorem iterated_oscillatory_integration_by_parts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {φ d : E → ℝ} {a b : ℕ → E → ℂ} {h : ℝ} (hh : h ≠ 0) (v : E) (N : ℕ)
    (hφ : ∀ k < N, ∀ x ∈ tsupport (b k), HasLineDerivAt ℝ φ (d x) x v)
    (hb : ∀ k < N, ∀ x, HasLineDerivAt ℝ (b k) (a (k + 1) x) x v)
    (ha : ∀ k < N, ∀ x, a k x = (d x : ℂ) * b k x)
    (hinta : ∀ k ≤ N, Integrable (fun x => oscillation φ h x * a k x) μ)
    (hintb : ∀ k < N, Integrable (fun x => oscillation φ h x * b k x) μ) :
    (∫ x, oscillation φ h x * a 0 x ∂μ) =
      (Complex.I * (h : ℂ)) ^ N * ∫ x, oscillation φ h x * a N x ∂μ := by
  have step (k : ℕ) (hk : k < N) :
      (∫ x, oscillation φ h x * a k x ∂μ) =
        Complex.I * (h : ℂ) * ∫ x, oscillation φ h x * a (k + 1) x ∂μ := by
    have hi := oscillatory_integration_by_parts hh v (hφ k hk) (hb k hk)
      (by simpa only [← ha k hk] using hinta k hk.le)
      (hinta (k + 1) hk) (hintb k hk)
    simpa only [← ha k hk] using hi
  have induction_step : ∀ k, k ≤ N →
      (∫ x, oscillation φ h x * a 0 x ∂μ) =
        (Complex.I * (h : ℂ)) ^ k * ∫ x, oscillation φ h x * a k x ∂μ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      rw [ih (Nat.le_of_succ_le hk), step k hk, pow_succ]
      ring
  exact induction_step N le_rfl

/-- The explicit decay bound obtained after `N` integrations by parts. -/
theorem norm_integral_oscillation_mul_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {φ d : E → ℝ} {a b : ℕ → E → ℂ} {h : ℝ} (hh : 0 < h) (v : E) (N : ℕ)
    (hφ : ∀ k < N, ∀ x ∈ tsupport (b k), HasLineDerivAt ℝ φ (d x) x v)
    (hb : ∀ k < N, ∀ x, HasLineDerivAt ℝ (b k) (a (k + 1) x) x v)
    (ha : ∀ k < N, ∀ x, a k x = (d x : ℂ) * b k x)
    (hinta : ∀ k ≤ N, Integrable (fun x => oscillation φ h x * a k x) μ)
    (hintb : ∀ k < N, Integrable (fun x => oscillation φ h x * b k x) μ) :
    ‖∫ x, oscillation φ h x * a 0 x ∂μ‖ ≤ h ^ N * ∫ x, ‖a N x‖ ∂μ := by
  rw [iterated_oscillatory_integration_by_parts hh.ne' v N hφ hb ha hinta hintb]
  simp only [norm_mul, norm_pow, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hh]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hh.le _)
  simpa only [norm_mul, norm_oscillation, one_mul] using
    norm_integral_le_integral_norm (fun x => oscillation φ h x * a N x)

/-- Applied to the Euclidean wave phase, the integration-by-parts estimate
requires only the amplitude recursion and its integrability. The phase
derivative is computed by the preceding theorem, not assumed. -/
theorem norm_wave_integral_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    (X v : E) (T : ℝ) {a b : ℕ → E → ℂ} {h : ℝ} (hh : 0 < h) (N : ℕ)
    (hsupp : ∀ k < N, (0 : E) ∉ tsupport (b k))
    (hb : ∀ k < N, ∀ ξ, HasLineDerivAt ℝ (b k) (a (k + 1) ξ) ξ v)
    (ha : ∀ k < N, ∀ ξ,
      a k ξ = ((⟪X, v⟫ - T * (⟪ξ, v⟫ / ‖ξ‖) : ℝ) : ℂ) * b k ξ)
    (hinta : ∀ k ≤ N, Integrable
      (fun ξ => oscillation (euclideanWavePhase X T) h ξ * a k ξ) μ)
    (hintb : ∀ k < N, Integrable
      (fun ξ => oscillation (euclideanWavePhase X T) h ξ * b k ξ) μ) :
    ‖∫ ξ, oscillation (euclideanWavePhase X T) h ξ * a 0 ξ ∂μ‖ ≤
      h ^ N * ∫ ξ, ‖a N ξ‖ ∂μ := by
  apply norm_integral_oscillation_mul_le hh v N ?_ hb ha hinta hintb
  intro k hk ξ hξ
  apply hasLineDerivAt_euclideanWavePhase
  intro hzero
  apply hsupp k hk
  simpa only [hzero] using hξ

/-- Compactly supported continuous amplitudes automatically satisfy all the
integrability conditions in the repeated wave-kernel estimate. -/
theorem norm_wave_integral_le_of_compactSupport
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    (X v : E) (T : ℝ) {a b : ℕ → E → ℂ} {h : ℝ} (hh : 0 < h) (N : ℕ)
    (hsupp : ∀ k < N, (0 : E) ∉ tsupport (b k))
    (hb : ∀ k < N, ∀ ξ, HasLineDerivAt ℝ (b k) (a (k + 1) ξ) ξ v)
    (ha : ∀ k < N, ∀ ξ,
      a k ξ = ((⟪X, v⟫ - T * (⟪ξ, v⟫ / ‖ξ‖) : ℝ) : ℂ) * b k ξ)
    (hca : ∀ k ≤ N, Continuous (a k)) (hsa : ∀ k ≤ N, HasCompactSupport (a k))
    (hcb : ∀ k < N, Continuous (b k)) (hsb : ∀ k < N, HasCompactSupport (b k)) :
    ‖∫ ξ, oscillation (euclideanWavePhase X T) h ξ * a 0 ξ ∂μ‖ ≤
      h ^ N * ∫ ξ, ‖a N ξ‖ ∂μ := by
  have hc : Continuous (oscillation (euclideanWavePhase X T) h) := by
    apply continuous_oscillation
    unfold euclideanWavePhase
    fun_prop
  apply norm_wave_integral_le X v T hh N hsupp hb ha
  · intro k hk
    exact (hc.mul (hca k hk)).integrable_of_hasCompactSupport (hsa k hk).mul_left
  · intro k hk
    exact (hc.mul (hcb k hk)).integrable_of_hasCompactSupport (hsb k hk).mul_left

noncomputable def quotientAmplitude {E : Type*} (d : E → ℂ) (a : E → ℂ) : E → ℂ :=
  fun ξ => a ξ / d ξ

theorem tsupport_quotientAmplitude_subset {E : Type*} [TopologicalSpace E]
    (d a : E → ℂ) : tsupport (quotientAmplitude d a) ⊆ tsupport a := by
  unfold quotientAmplitude
  simp_rw [div_eq_mul_inv]
  exact tsupport_mul_subset_left

theorem hasCompactSupport_quotientAmplitude {E : Type*} [TopologicalSpace E]
    (d : E → ℂ) {a : E → ℂ} (ha : HasCompactSupport a) :
    HasCompactSupport (quotientAmplitude d a) :=
  ha.of_isClosed_subset (isClosed_tsupport _) (tsupport_quotientAmplitude_subset d a)

/-- The apparent singularity of the radial phase at zero is harmless for a
smooth amplitude supported away from zero. -/
theorem contDiff_quotientAmplitude {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {d a : E → ℂ}
    (ha : ContDiff ℝ ∞ a) (hzero : (0 : E) ∉ tsupport a)
    (hd : ∀ ξ ≠ 0, ContDiffAt ℝ ∞ d ξ) (hd₀ : ∀ ξ, d ξ ≠ 0) :
    ContDiff ℝ ∞ (quotientAmplitude d a) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ξ = 0
  · subst ξ
    have hz : (0 : E) ∉ tsupport (quotientAmplitude d a) :=
      fun h => hzero (tsupport_quotientAmplitude_subset d a h)
    exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hz)
  · unfold quotientAmplitude
    simp_rw [div_eq_mul_inv]
    exact ha.contDiffAt.mul ((hd ξ hξ).inv (hd₀ ξ))

noncomputable def differentiateAmplitude {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (d : E → ℂ) (v : E) (a : E → ℂ) : E → ℂ :=
  fun ξ => fderiv ℝ (quotientAmplitude d a) ξ v

theorem differentiateAmplitude_regular {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {d a : E → ℂ} (v : E)
    (ha : ContDiff ℝ ∞ a) (hzero : (0 : E) ∉ tsupport a)
    (hs : HasCompactSupport a)
    (hd : ∀ ξ ≠ 0, ContDiffAt ℝ ∞ d ξ) (hd₀ : ∀ ξ, d ξ ≠ 0) :
    ContDiff ℝ ∞ (differentiateAmplitude d v a) ∧
      (0 : E) ∉ tsupport (differentiateAmplitude d v a) ∧
      HasCompactSupport (differentiateAmplitude d v a) := by
  have hq := contDiff_quotientAmplitude ha hzero hd hd₀
  have ht : tsupport (differentiateAmplitude d v a) ⊆ tsupport a :=
    (tsupport_fderiv_apply_subset ℝ v).trans (tsupport_quotientAmplitude_subset d a)
  refine ⟨?_, fun hz => hzero (ht hz), ?_⟩
  · exact (hq.fderiv_right (by simp)).clm_apply contDiff_const
  · exact (hasCompactSupport_quotientAmplitude d hs).fderiv_apply ℝ v

noncomputable def iteratedAmplitude {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (d : E → ℂ) (v : E) (a : E → ℂ) : ℕ → E → ℂ
  | 0 => a
  | k + 1 => differentiateAmplitude d v (iteratedAmplitude d v a k)

theorem iteratedAmplitude_regular {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {d a : E → ℂ} (v : E)
    (ha : ContDiff ℝ ∞ a) (hzero : (0 : E) ∉ tsupport a) (hs : HasCompactSupport a)
    (hd : ∀ ξ ≠ 0, ContDiffAt ℝ ∞ d ξ) (hd₀ : ∀ ξ, d ξ ≠ 0) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedAmplitude d v a k) ∧
      (0 : E) ∉ tsupport (iteratedAmplitude d v a k) ∧
      HasCompactSupport (iteratedAmplitude d v a k) := by
  induction k with
  | zero => exact ⟨ha, hzero, hs⟩
  | succ k ih => exact differentiateAmplitude_regular v ih.1 ih.2.1 ih.2.2 hd hd₀

/-- Full rapid semiclassical decay for a fixed nonstationary phase. The
amplitudes are constructed by division and differentiation, rather than
supplied as hypotheses. The constant is independent of `h`. -/
theorem rapid_decay_of_nonstationary_phase
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {φ d : E → ℝ} {a : E → ℂ} (v : E)
    (hφc : Continuous φ)
    (hφ : ∀ ξ ≠ 0, HasLineDerivAt ℝ φ (d ξ) ξ v)
    (hd : ∀ ξ ≠ 0, ContDiffAt ℝ ∞ (fun ξ => (d ξ : ℂ)) ξ)
    (hd₀ : ∀ ξ, d ξ ≠ 0)
    (ha : ContDiff ℝ ∞ a) (hzero : (0 : E) ∉ tsupport a) (hs : HasCompactSupport a)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h →
      ‖∫ ξ, oscillation φ h ξ * a ξ ∂μ‖ ≤ h ^ N * C := by
  let A := iteratedAmplitude (fun ξ => (d ξ : ℂ)) v a
  let B := fun k => quotientAmplitude (fun ξ => (d ξ : ℂ)) (A k)
  have hdn : ∀ ξ, (d ξ : ℂ) ≠ 0 := by intro ξ; exact_mod_cast hd₀ ξ
  have hA (k : ℕ) := iteratedAmplitude_regular v ha hzero hs hd hdn k
  have hBc (k : ℕ) : ContDiff ℝ ∞ (B k) :=
    contDiff_quotientAmplitude (hA k).1 (hA k).2.1 hd hdn
  have hBs (k : ℕ) : HasCompactSupport (B k) :=
    hasCompactSupport_quotientAmplitude _ (hA k).2.2
  refine ⟨∫ ξ, ‖A N ξ‖ ∂μ, integral_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro h hh
  apply norm_integral_oscillation_mul_le (a := A) (b := B) hh v N
  · intro k _ ξ hξ
    apply hφ ξ
    intro hz
    have hξA := tsupport_quotientAmplitude_subset (fun ξ => (d ξ : ℂ)) (A k) hξ
    exact (hA k).2.1 (hz ▸ hξA)
  · intro k _ ξ
    exact ((hBc k).differentiable (by simp) ξ).hasFDerivAt.hasLineDerivAt v
  · intro k _ ξ
    dsimp [B, quotientAmplitude]
    field_simp [hdn ξ]
  · intro k _
    exact ((continuous_oscillation hφc h).mul (hA k).1.continuous).integrable_of_hasCompactSupport
      (hA k).2.2.mul_left
  · intro k _
    exact ((continuous_oscillation hφc h).mul (hBc k).continuous).integrable_of_hasCompactSupport
      (hBs k).mul_left

/-- The Euclidean wave integral is rapidly decreasing as `h → 0` at every
fixed observation point outside the cone. The next step toward the uniform
kernel lemma is to make `C` uniform in `(X,T)` with spatial decay. -/
theorem rapid_decay_euclidean_wave_off_cone
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    (X : E) (T : ℝ) {a : E → ℂ}
    (hX : 3 ≤ ‖X‖) (hT₀ : 0 ≤ T) (hT₁ : T ≤ 2)
    (ha : ContDiff ℝ ∞ a) (hzero : (0 : E) ∉ tsupport a) (hs : HasCompactSupport a)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h →
      ‖∫ ξ, oscillation (euclideanWavePhase X T) h ξ * a ξ ∂μ‖ ≤ h ^ N * C := by
  obtain ⟨v, hv, halign, hbound⟩ := exists_off_cone_direction X hX
  let d : E → ℝ := fun ξ => ⟪X, v⟫ - T * (⟪ξ, v⟫ / ‖ξ‖)
  have hd₀ : ∀ ξ, d ξ ≠ 0 := by
    intro ξ
    apply ne_of_gt
    by_cases hξ : ξ = 0
    · subst ξ
      simp only [d, inner_zero_left, norm_zero, div_zero, mul_zero, sub_zero, halign]
      linarith
    · have hb := hbound ξ T hξ hT₀ hT₁
      dsimp [d]
      linarith
  apply rapid_decay_of_nonstationary_phase (d := d) v ?_ ?_ ?_ hd₀ ha hzero hs N
  · unfold euclideanWavePhase
    fun_prop
  · intro ξ hξ
    exact hasLineDerivAt_euclideanWavePhase X ξ v T hξ
  · intro ξ hξ
    have hn : ContDiffAt ℝ ∞ (fun y : E => ‖y‖) ξ := contDiffAt_norm ℝ hξ
    have hi : ContDiffAt ℝ ∞ (fun y : E => ⟪y, v⟫) ξ := by
      simpa only [coe_innerSL_apply, real_inner_comm] using (innerSL ℝ v).contDiff.contDiffAt
    have hreal : ContDiffAt ℝ ∞ d ξ :=
      contDiffAt_const.sub (contDiffAt_const.mul (hi.div hn (norm_ne_zero_iff.mpr hξ)))
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp ξ hreal

end OAI.Analysis.Fourier.WavePackets
