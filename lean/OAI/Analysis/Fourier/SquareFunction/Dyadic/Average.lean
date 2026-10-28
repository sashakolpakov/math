import OAI.Analysis.Fourier.SquareFunction.Dyadic.Cover

/-! Actual averages, oscillations, and localized weak estimates for the dyadic
sharp-function argument. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal

noncomputable def positiveSetMean {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (Q : Set X) : ℝ≥0∞ :=
  (∫⁻ x in Q, ENNReal.ofReal (f x) ∂μ) / μ Q

noncomputable def setOscillation {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (Q : Set X) : ℝ≥0∞ :=
  (∫⁻ x in Q, ‖f x - (positiveSetMean μ f Q).toReal‖ₑ ∂μ) / μ Q

noncomputable def familySup {X : Type*} (s : Finset (Set X))
    (a : Set X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  ⨆ Q : s, Q.val.indicator (fun _ => a Q.val) x

theorem familySup_superlevel {X : Type*} (s : Finset (Set X))
    (a : Set X → ℝ≥0∞) (t : ℝ≥0∞) :
    {x | t < familySup s a x} = ⋃ Q ∈ s.filter (fun Q => t < a Q), Q := by
  classical
  ext x
  simp only [familySup, Set.mem_ofPred_eq, lt_iSup_iff, mem_iUnion, Finset.mem_filter]
  constructor
  · rintro ⟨Q, hQ⟩
    have hx : x ∈ Q.val := by
      by_contra h
      simp [Set.indicator_of_notMem h] at hQ
    exact ⟨Q.val, ⟨Q.property, by simpa [Set.indicator_of_mem hx] using hQ⟩, hx⟩
  · rintro ⟨Q, ⟨hQ, ht⟩, hx⟩
    exact ⟨⟨Q, hQ⟩, by simpa [Set.indicator_of_mem hx] using ht⟩

theorem measurable_familySup {X : Type*} [MeasurableSpace X]
    (s : Finset (Set X)) (hm : ∀ Q ∈ s, MeasurableSet Q)
    (a : Set X → ℝ≥0∞) : Measurable (familySup s a) := by
  classical
  exact Measurable.iSup fun Q : s => measurable_const.indicator (hm Q.val Q.property)

theorem le_familySup_of_mem {X : Type*} {s : Finset (Set X)} {a : Set X → ℝ≥0∞}
    {Q : Set X} (hQ : Q ∈ s) {x : X} (hx : x ∈ Q) : a Q ≤ familySup s a x := by
  classical
  exact (by simpa only [familySup, Set.indicator_of_mem hx] using
    (le_iSup (fun R : s => R.val.indicator (fun _ => a R.val) x) ⟨Q, hQ⟩))

theorem familySup_le_sum {X : Type*} (s : Finset (Set X)) (a : Set X → ℝ≥0∞)
    (x : X) : familySup s a x ≤ ∑ Q ∈ s, a Q := by
  classical
  apply iSup_le
  intro Q
  exact (Set.indicator_le_self Q.val (fun _ => a Q.val) x).trans
    (Finset.single_le_sum (fun R _ => bot_le) Q.property)

theorem familySup_mono {X : Type*} {s t : Finset (Set X)} (hst : s ⊆ t)
    (a : Set X → ℝ≥0∞) (x : X) : familySup s a x ≤ familySup t a x := by
  apply iSup_le
  intro Q
  exact le_iSup (fun R : t => R.val.indicator (fun _ => a R.val) x) ⟨Q.val, hst Q.property⟩

theorem familySup_ne_top {X : Type*} (s : Finset (Set X)) (a : Set X → ℝ≥0∞)
    (ha : ∀ Q ∈ s, a Q ≠ ∞) (x : X) : familySup s a x ≠ ∞ := by
  classical
  have hsum : (∑ Q ∈ s, a Q) ≠ ∞ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert Q s hQ ih =>
      rw [Finset.sum_insert hQ]
      exact ENNReal.add_ne_top.mpr ⟨ha Q (Finset.mem_insert_self Q s),
        ih (fun R hR => ha R (Finset.mem_insert_of_mem hR))⟩
  exact ne_top_of_le_ne_top hsum (familySup_le_sum s a x)

theorem familySup_power_integral_lt_top {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (s : Finset (Set X)) (a : Set X → ℝ≥0∞)
    (ha : ∀ Q ∈ s, a Q ≠ ∞) {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ x, familySup s a x ^ p ∂μ) < ∞ := by
  classical
  have hsum : (∑ Q ∈ s, a Q) ≠ ∞ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert Q s hQ ih =>
      rw [Finset.sum_insert hQ]
      exact ENNReal.add_ne_top.mpr ⟨ha Q (Finset.mem_insert_self Q s),
        ih (fun R hR => ha R (Finset.mem_insert_of_mem hR))⟩
  have hb : (∫⁻ x, familySup s a x ^ p ∂μ) ≤
      (∑ Q ∈ s, a Q) ^ p * μ univ := by
    calc
      _ ≤ ∫⁻ _ : X, (∑ Q ∈ s, a Q) ^ p ∂μ :=
        lintegral_mono (fun x => ENNReal.rpow_le_rpow (familySup_le_sum s a x) hp)
      _ = _ := lintegral_const _
  exact hb.trans_lt (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hp hsum)
    (measure_lt_top μ univ))

theorem positiveSetMean_ne_top {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (Q : Set X) (hfn : ∀ x, 0 ≤ f x)
    (hf : IntegrableOn f Q μ) (hQ0 : μ Q ≠ 0) : positiveSetMean μ f Q ≠ ∞ := by
  have hi := hf.hasFiniteIntegral
  change (∫⁻ x in Q, ‖f x‖ₑ ∂μ) < ∞ at hi
  simp only [Real.enorm_eq_ofReal (hfn _)] at hi
  exact ENNReal.div_ne_top hi.ne hQ0

theorem setOscillation_ne_top {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (Q : Set X)
    (hf : IntegrableOn f Q μ) (hQ0 : μ Q ≠ 0) (hQtop : μ Q ≠ ∞) :
    setOscillation μ f Q ≠ ∞ := by
  have hc : IntegrableOn (fun _ : X => (positiveSetMean μ f Q).toReal) Q μ :=
    integrableOn_const (by simpa using hQtop)
  have hi := (hf.sub hc).hasFiniteIntegral
  change (∫⁻ x in Q, ‖f x - (positiveSetMean μ f Q).toReal‖ₑ ∂μ) < ∞ at hi
  exact ENNReal.div_ne_top hi.ne hQ0

theorem positiveSetMean_mul_measure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (Q : Set X) (hQ0 : μ Q ≠ 0) (hQtop : μ Q ≠ ∞) :
    positiveSetMean μ f Q * μ Q = ∫⁻ x in Q, ENNReal.ofReal (f x) ∂μ := by
  rw [positiveSetMean, div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel hQ0 hQtop, mul_one]

theorem setOscillation_mul_measure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (Q : Set X) (hQ0 : μ Q ≠ 0) (hQtop : μ Q ≠ ∞) :
    setOscillation μ f Q * μ Q =
      ∫⁻ x in Q, ‖f x - (positiveSetMean μ f Q).toReal‖ₑ ∂μ := by
  rw [setOscillation, div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel hQ0 hQtop, mul_one]

/-- Integrating the triangle inequality around an arbitrary finite center. -/
theorem lintegral_le_oscillation_add {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (R : Set X) (hfn : ∀ x, 0 ≤ f x)
    {c : ℝ≥0∞} (hc : c ≠ ∞) :
    (∫⁻ x in R, ENNReal.ofReal (f x) ∂μ) ≤
      (∫⁻ x in R, ‖f x - c.toReal‖ₑ ∂μ) + c * μ R := by
  calc
    _ ≤ ∫⁻ x in R, ‖f x - c.toReal‖ₑ + c ∂μ := by
      apply lintegral_mono
      intro x
      have h := enorm_add_le (f x - c.toReal) c.toReal
      simpa only [sub_add_cancel, Real.enorm_eq_ofReal (hfn x),
        Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hc] using h
    _ = _ := by rw [lintegral_add_right _ measurable_const, setLIntegral_const]

/-- A large mean relative to a finite center forces a large mean oscillation. -/
theorem mean_gap_le_oscillation {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (R : Set X) (hfn : ∀ x, 0 ≤ f x)
    (hR0 : μ R ≠ 0) (hRtop : μ R ≠ ∞)
    {c t : ℝ≥0∞} (hc : c ≠ ∞) (hgap : c + t ≤ positiveSetMean μ f R) :
    t * μ R ≤ ∫⁻ x in R, ‖f x - c.toReal‖ₑ ∂μ := by
  have h : c * μ R + t * μ R ≤
      c * μ R + ∫⁻ x in R, ‖f x - c.toReal‖ₑ ∂μ := by
    calc
      _ = (c + t) * μ R := (add_mul _ _ _).symm
      _ ≤ positiveSetMean μ f R * μ R := mul_le_mul_left hgap _
      _ = _ := positiveSetMean_mul_measure μ f R hR0 hRtop
      _ ≤ _ := by simpa only [add_comm] using lintegral_le_oscillation_add μ f R hfn hc
  exact ENNReal.le_of_add_le_add_left (ENNReal.mul_ne_top hc hRtop) h

/-- Localized weak estimate for descendants whose means exceed a fixed center.
This is the oscillation estimate used inside each stopping cube. -/
theorem laminar_mean_gap_weak {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hfn : ∀ x, 0 ≤ f x)
    {s : Finset (Set X)} (hs : IsLaminar s)
    (hm : ∀ R ∈ s, MeasurableSet R) (hR0 : ∀ R ∈ s, μ R ≠ 0)
    (hRtop : ∀ R ∈ s, μ R ≠ ∞) {Q : Set X} (hsub : ∀ R ∈ s, R ⊆ Q)
    {c t : ℝ≥0∞} (hc : c ≠ ∞)
    (hgap : ∀ R ∈ s, c + t ≤ positiveSetMean μ f R) :
    t * μ (⋃ R ∈ s, R) ≤ ∫⁻ x in Q, ‖f x - c.toReal‖ₑ ∂μ := by
  refine (laminar_weak_bound μ hs hm (fun x => ‖f x - c.toReal‖ₑ) t
    (fun R hR => mean_gap_le_oscillation μ f R hfn (hR0 R hR) (hRtop R hR) hc
      (hgap R hR))).trans ?_
  exact lintegral_mono_set (iUnion₂_subset hsub)

end OAI.Analysis.Fourier.SquareFunction
