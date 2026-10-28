import OAI.Analysis.Fourier.SquareFunction.EuclideanMaximal

open OAI.Analysis.Fourier.Wave

/-! Finite-vector estimates for the middle-frequency term in the
combining-dilates lemma from `stein_square.tex`. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory
open scoped ENNReal

theorem sum_rpow_le_rpow_sum {I : Type*} (s : Finset I) (a : I → ℝ≥0∞)
    {q : ℝ} (hq : 1 ≤ q) : ∑ i ∈ s, a i ^ q ≤ (∑ i ∈ s, a i) ^ q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      simp only [Finset.sum_insert his]
      exact (add_le_add le_rfl ih).trans (ENNReal.add_rpow_le_rpow_add _ _ hq)

/-- Sequence Hölder at precisely the logarithmic-loss exponent of the source. -/
theorem finite_middle_holder {I : Type*} (s : Finset I) (a : I → ℝ≥0∞)
    {p : ℝ} (hp : 2 ≤ p) :
    (∑ i ∈ s, a i) ^ (1 / 2 : ℝ) ≤
      (s.card : ℝ≥0∞) ^ (1 / 2 - 1 / p) * (∑ i ∈ s, a i ^ (p / 2)) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hq : 0 ≤ 1 / p := (one_div_pos.mpr hp0).le
  have h := ENNReal.rpow_le_rpow
    (ENNReal.rpow_sum_le_const_mul_sum_rpow (s := s) (f := a) (by linarith : 1 ≤ p / 2)) hq
  rw [← ENNReal.rpow_mul, ENNReal.mul_rpow_of_nonneg _ _ hq,
    ← ENNReal.rpow_mul] at h
  have h1 : p / 2 * (1 / p) = (1 / 2 : ℝ) := by field_simp
  have h2 : (p / 2 - 1) * (1 / p) = 1 / 2 - 1 / p := by field_simp
  simpa only [h1, h2] using h

/-- Maximal functions of the squares, summed in `ℓ^(p/2)`, are controlled by
the input square envelope. This is the maximal estimate for the source's
middle group of scales; the number of scales occurs only in Holder above. -/
theorem maximal_squares_sum_moment {n : ℕ} {I : Type*} (s : Finset I)
    (b : I → Space n → ℝ) (hb : ∀ i ∈ s, Measurable (b i))
    (hbn : ∀ i ∈ s, ∀ x, 0 ≤ b i x) {p : ℝ} (hp : 2 < p) :
    (∫⁻ x, ∑ i ∈ s,
      ballMaximal volume (fun y => ENNReal.ofReal ((b i y) ^ 2)) x ^ (p / 2)) ≤
      ((2 : ℝ≥0∞) ^ (p / 2) * ENNReal.ofReal ((5 : ℝ) ^ n * (p / 2) / (p / 2 - 1))) *
        ∫⁻ x, (∑ i ∈ s, ENNReal.ofReal (b i x) ^ (2 : ℝ)) ^ (p / 2) := by
  have hp0 : 0 < p := by linarith
  have he (i : I) (hi : i ∈ s) (x : Space n) :
      ENNReal.ofReal ((b i x) ^ 2) ^ (p / 2) = ENNReal.ofReal (b i x) ^ p := by
    rw [ENNReal.ofReal_pow (hbn i hi x), ← ENNReal.rpow_two,
      ← ENNReal.rpow_mul]
    congr 1
    ring
  calc
    _ = ∑ i ∈ s, ∫⁻ x,
        ballMaximal volume (fun y => ENNReal.ofReal ((b i y) ^ 2)) x ^ (p / 2) :=
      lintegral_finsetSum s (fun i hi => (measurable_ballMaximal volume _).pow_const _)
    _ ≤ ∑ i ∈ s, ((2 : ℝ≥0∞) ^ (p / 2) *
        ENNReal.ofReal ((5 : ℝ) ^ n * (p / 2) / (p / 2 - 1))) *
        ∫⁻ x, ENNReal.ofReal (b i x) ^ p := by
      apply Finset.sum_le_sum
      intro i hi
      have h := ballMaximal_strong_moment volume ((hb i hi).pow_const 2)
        (fun x => sq_nonneg (b i x)) (by linarith : 1 < p / 2)
        (D := (5 : ℝ) ^ n) (by positivity)
        (fun x r hr => euclidean_ball_finite_pos x hr)
        (fun x r hr => (euclidean_ball_five x r).le)
      simpa only [he i hi] using h
    _ = ((2 : ℝ≥0∞) ^ (p / 2) * ENNReal.ofReal ((5 : ℝ) ^ n * (p / 2) / (p / 2 - 1))) *
        ∫⁻ x, ∑ i ∈ s, ENNReal.ofReal (b i x) ^ p := by
      rw [lintegral_finsetSum s (fun i hi => (hb i hi).ennreal_ofReal.pow_const p), Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_right
      apply lintegral_mono
      intro x
      have h := sum_rpow_le_rpow_sum s (fun i => ENNReal.ofReal (b i x) ^ (2 : ℝ))
        (by linarith : 1 ≤ p / 2)
      simpa only [← ENNReal.rpow_mul, show (2 : ℝ) * (p / 2) = p by ring] using h

/-- The `Lᵖ` estimate for the global envelope of the middle-scale terms. -/
theorem eLpNorm_maximal_squares_envelope_le {n : ℕ} {I : Type*} (s : Finset I)
    (b : I → Space n → ℝ) (hb : ∀ i ∈ s, Measurable (b i))
    (hbn : ∀ i ∈ s, ∀ x, 0 ≤ b i x) {p : ℝ} (hp : 2 < p) :
    eLpNorm (fun x => (∑ i ∈ s,
      ballMaximal volume (fun y => ENNReal.ofReal ((b i y) ^ 2)) x ^ (p / 2)) ^ (1 / p))
      (ENNReal.ofReal p) volume ≤
      (((2 : ℝ≥0∞) ^ (p / 2) * ENNReal.ofReal ((5 : ℝ) ^ n * (p / 2) / (p / 2 - 1))) ^ (1 / p)) *
        eLpNorm (fun x => (∑ i ∈ s, ENNReal.ofReal (b i x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
          (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hm : Measurable (fun x => (∑ i ∈ s,
      ballMaximal volume (fun y => ENNReal.ofReal ((b i y) ^ 2)) x ^ (p / 2)) ^ (1 / p)) :=
    (Finset.measurable_sum s (fun i hi => (measurable_ballMaximal volume _).pow_const _)).pow_const _
  have hw : Measurable (fun x => (∑ i ∈ s, ENNReal.ofReal (b i x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) :=
    (Finset.measurable_sum s (fun i hi => (hb i hi).ennreal_ofReal.pow_const _)).pow_const _
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hm.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hw.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hp0.le, enorm_eq_self, ← ENNReal.rpow_mul,
    one_div_mul_cancel (ne_of_gt hp0), ENNReal.rpow_one,
    show (1 / 2 : ℝ) * p = p / 2 by ring]
  have h := ENNReal.rpow_le_rpow (maximal_squares_sum_moment s b hb hbn hp)
    (one_div_pos.mpr hp0).le
  rwa [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hp0).le] at h

/-- The middle-frequency maximal estimate before applying the scalar
operator bound to each component. This form avoids any circular use of the
unknown output square-function norm. -/
theorem maximal_squares_sum_moment_raw {n : ℕ} {I : Type*} (s : Finset I)
    (b : I → Space n → ℝ) (hb : ∀ i ∈ s, Measurable (b i))
    (hbn : ∀ i ∈ s, ∀ x, 0 ≤ b i x) {p : ℝ} (hp : 2 < p) :
    (∫⁻ x, ∑ i ∈ s,
      ballMaximal volume (fun y => ENNReal.ofReal ((b i y) ^ 2)) x ^ (p / 2)) ≤
      ((2 : ℝ≥0∞) ^ (p / 2) * ENNReal.ofReal ((5 : ℝ) ^ n * (p / 2) / (p / 2 - 1))) *
        ∑ i ∈ s, ∫⁻ x, ENNReal.ofReal (b i x) ^ p := by
  rw [lintegral_finsetSum s (fun i hi => (measurable_ballMaximal volume _).pow_const _),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h := ballMaximal_strong_moment volume ((hb i hi).pow_const 2)
    (fun x => sq_nonneg (b i x)) (by linarith : 1 < p / 2)
    (D := (5 : ℝ) ^ n) (by positivity)
    (fun x r hr => euclidean_ball_finite_pos x hr)
    (fun x r hr => (euclidean_ball_five x r).le)
  have he (x : Space n) : ENNReal.ofReal ((b i x) ^ 2) ^ (p / 2) =
      ENNReal.ofReal (b i x) ^ p := by
    rw [ENNReal.ofReal_pow (hbn i hi x), ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    congr 1
    ring
  simpa only [he] using h

/-- Scalar `p`-moment bounds for the individual operators control the
middle-frequency maximal envelope by the input square envelope. -/
theorem maximal_squares_sum_moment_of_scalar_bounds {n : ℕ} {I : Type*} (s : Finset I)
    (b f : I → Space n → ℝ) (hb : ∀ i ∈ s, Measurable (b i))
    (hbn : ∀ i ∈ s, ∀ x, 0 ≤ b i x) (hf : ∀ i ∈ s, Measurable (f i))
    {p : ℝ} (hp : 2 < p) {B : ℝ≥0∞}
    (hbp : ∀ i ∈ s, (∫⁻ x, ENNReal.ofReal (b i x) ^ p) ≤
      B * ∫⁻ x, ENNReal.ofReal (f i x) ^ p) :
    (∫⁻ x, ∑ i ∈ s,
      ballMaximal volume (fun y => ENNReal.ofReal ((b i y) ^ 2)) x ^ (p / 2)) ≤
      (((2 : ℝ≥0∞) ^ (p / 2) * ENNReal.ofReal ((5 : ℝ) ^ n * (p / 2) / (p / 2 - 1))) * B) *
        ∫⁻ x, (∑ i ∈ s, ENNReal.ofReal (f i x) ^ (2 : ℝ)) ^ (p / 2) := by
  have h := maximal_squares_sum_moment_raw s b hb hbn hp
  refine h.trans ?_
  conv_rhs => rw [mul_assoc]
  apply mul_le_mul_right
  calc
    _ ≤ ∑ i ∈ s, B * ∫⁻ x, ENNReal.ofReal (f i x) ^ p := Finset.sum_le_sum hbp
    _ = B * ∫⁻ x, ∑ i ∈ s, ENNReal.ofReal (f i x) ^ p := by
      rw [lintegral_finsetSum s (fun i hi => (hf i hi).ennreal_ofReal.pow_const p), Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_right
      apply lintegral_mono
      intro x
      have h := sum_rpow_le_rpow_sum s (fun i => ENNReal.ofReal (f i x) ^ (2 : ℝ))
        (by linarith : 1 ≤ p / 2)
      simpa only [← ENNReal.rpow_mul, show (2 : ℝ) * (p / 2) = p by ring] using h

theorem eLpNorm_rpow_eq_moment {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) {f : X → E} (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    eLpNorm f (ENNReal.ofReal p) μ ^ p = ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

theorem moment_le_of_eLpNorm_le {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (μ : Measure X) {f : X → E} {g : X → F}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    {p : ℝ} (hp : 0 < p) {B : ℝ≥0∞}
    (h : eLpNorm f (ENNReal.ofReal p) μ ≤ B * eLpNorm g (ENNReal.ofReal p) μ) :
    (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ≤ B ^ p * ∫⁻ x, ‖g x‖ₑ ^ p ∂μ := by
  have hh := ENNReal.rpow_le_rpow h hp.le
  rwa [ENNReal.mul_rpow_of_nonneg _ _ hp.le,
    eLpNorm_rpow_eq_moment μ hf hp, eLpNorm_rpow_eq_moment μ hg hp] at hh

/-- The full middle-envelope `Lᵖ` bound from scalar operator norm estimates,
before the finite-window Holder factor is inserted. -/
theorem eLpNorm_middle_envelope_le {n : ℕ} {I : Type*} (s : Finset I)
    (b f : I → Space n → ℝ) (hb : ∀ i ∈ s, Measurable (b i))
    (hbn : ∀ i ∈ s, ∀ x, 0 ≤ b i x) (hf : ∀ i ∈ s, Measurable (f i))
    (hfn : ∀ i ∈ s, ∀ x, 0 ≤ f i x) {p : ℝ} (hp : 2 < p) {B : ℝ≥0∞}
    (hbp : ∀ i ∈ s, eLpNorm (b i) (ENNReal.ofReal p) volume ≤
      B * eLpNorm (f i) (ENNReal.ofReal p) volume) :
    eLpNorm (fun x => (∑ i ∈ s,
      ballMaximal volume (fun y => ENNReal.ofReal ((b i y) ^ 2)) x ^ (p / 2)) ^ (1 / p))
      (ENNReal.ofReal p) volume ≤
      ((((2 : ℝ≥0∞) ^ (p / 2) * ENNReal.ofReal ((5 : ℝ) ^ n * (p / 2) / (p / 2 - 1))) ^ (1 / p)) * B) *
        eLpNorm (fun x => (∑ i ∈ s, ENNReal.ofReal (f i x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
          (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 ≤ 1 / p := (one_div_pos.mpr hp0).le
  have hm : Measurable (fun x => (∑ i ∈ s,
      ballMaximal volume (fun y => ENNReal.ofReal ((b i y) ^ 2)) x ^ (p / 2)) ^ (1 / p)) :=
    (Finset.measurable_sum s (fun i hi => (measurable_ballMaximal volume _).pow_const _)).pow_const _
  have hw : Measurable (fun x => (∑ i ∈ s, ENNReal.ofReal (f i x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) :=
    (Finset.measurable_sum s (fun i hi => (hf i hi).ennreal_ofReal.pow_const _)).pow_const _
  have hbound : ∀ i ∈ s, (∫⁻ x, ENNReal.ofReal (b i x) ^ p) ≤
      B ^ p * ∫⁻ x, ENNReal.ofReal (f i x) ^ p := by
    intro i hi
    simpa only [Real.enorm_eq_ofReal (hbn i hi _), Real.enorm_eq_ofReal (hfn i hi _)] using
      moment_le_of_eLpNorm_le volume (hb i hi).aestronglyMeasurable
        (hf i hi).aestronglyMeasurable hp0 (hbp i hi)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hm.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hw.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hp0.le, enorm_eq_self, ← ENNReal.rpow_mul,
    one_div_mul_cancel hp0.ne', ENNReal.rpow_one,
    show (1 / 2 : ℝ) * p = p / 2 by ring]
  have h := ENNReal.rpow_le_rpow
    (maximal_squares_sum_moment_of_scalar_bounds s b f hb hbn hf hp hbound) hp1
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp1, ENNReal.mul_rpow_of_nonneg _ _ hp1,
    ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one] at h
  exact h

end OAI.Analysis.Fourier.SquareFunction
