import OAI.Analysis.Fourier.SquareFunction.Maximal

/-! The actual uncentered Hardy--Littlewood maximal operator used in the
combining-dilates argument, with its weak bound proved by Vitali covering. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set Metric
open scoped ENNReal

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Ball averages of a nonnegative function. -/
noncomputable def ballAverage (μ : Measure X) (f : X → ℝ≥0∞) (z : X × ℝ) : ℝ≥0∞ :=
  (∫⁻ y in ball z.1 z.2, f y ∂μ) / μ (ball z.1 z.2)

/-- Uncentered Hardy--Littlewood maximal function, over all open metric balls. -/
noncomputable def ballMaximal (μ : Measure X) (f : X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  ⨆ z : X × ℝ, ⨆ (_ : x ∈ ball z.1 z.2), ballAverage μ f z

omit [BorelSpace X] in
theorem ballMaximal_superlevel (μ : Measure X) (f : X → ℝ≥0∞) (t : ℝ≥0∞) :
    {x | t < ballMaximal μ f x} =
      ⋃ z ∈ {z : X × ℝ | 0 < z.2 ∧ t < ballAverage μ f z}, ball z.1 z.2 := by
  ext x
  simp only [Set.mem_ofPred_eq, ballMaximal, lt_iSup_iff, mem_iUnion]
  constructor
  · rintro ⟨z, hx, hz⟩
    exact ⟨z, ⟨nonempty_ball.mp ⟨x, hx⟩, hz⟩, hx⟩
  · rintro ⟨z, ⟨hr, hz⟩, hx⟩
    exact ⟨z, hx, hz⟩

/-- Arbitrary ball suprema are measurable here because their superlevel sets are open. -/
theorem measurable_ballMaximal (μ : Measure X) (f : X → ℝ≥0∞) :
    Measurable (ballMaximal μ f) := by
  apply measurable_of_Ioi
  intro t
  change MeasurableSet {x | t < ballMaximal μ f x}
  rw [ballMaximal_superlevel]
  exact (isOpen_iUnion fun z => isOpen_iUnion fun hz => isOpen_ball).measurableSet

/-- The weak `(1,1)` bound for the actual maximal operator.  `D` is the
five-fold ball-volume ratio; in Euclidean dimension `n`, it is `5^n`. -/
theorem ballMaximal_weak [TopologicalSpace.SeparableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) {D : ℝ≥0∞}
    (hball : ∀ x r, 0 < r → μ (ball x r) ≠ 0 ∧ μ (ball x r) ≠ ∞)
    (hdbl : ∀ x r, 0 < r → μ (ball x (5 * r)) ≤ D * μ (ball x r))
    {t : ℝ≥0∞} (ht0 : t ≠ 0) (httop : t ≠ ∞) :
    μ {x | t < ballMaximal μ f x} ≤ D * t⁻¹ * ∫⁻ x, f x ∂μ := by
  rw [ballMaximal_superlevel]
  apply measure_ball_union_le_of_integral_unbounded μ f
    {z : X × ℝ | 0 < z.2 ∧ t < ballAverage μ f z} Prod.fst Prod.snd
    (fun z hz => hz.1) (fun z hz => hdbl z.1 z.2 hz.1)
  intro z hz
  have hb := hball z.1 z.2 hz.1
  have hi : t * μ (ball z.1 z.2) < ∫⁻ y in ball z.1 z.2, f y ∂μ :=
    (ENNReal.lt_div_iff_mul_lt (.inl hb.1) (.inl hb.2)).mp hz.2
  rw [mul_comm t⁻¹, ← div_eq_mul_inv]
  apply (ENNReal.le_div_iff_mul_le (.inl ht0) (.inl httop)).mpr
  simpa only [mul_comm] using hi.le

omit [BorelSpace X] in
theorem ballMaximal_mono (μ : Measure X) {f g : X → ℝ≥0∞} (hfg : f ≤ g) :
    ballMaximal μ f ≤ ballMaximal μ g := by
  intro x
  apply iSup_le
  intro z
  apply iSup_le
  intro hx
  apply le_iSup_of_le z
  apply le_iSup_of_le hx
  exact ENNReal.div_le_div_right (lintegral_mono hfg) _

omit [BorelSpace X] in
theorem ballMaximal_add_le (μ : Measure X) {f g : X → ℝ≥0∞}
    (hf : Measurable f) (_ : Measurable g) (x : X) :
    ballMaximal μ (fun y => f y + g y) x ≤ ballMaximal μ f x + ballMaximal μ g x := by
  apply iSup_le
  intro z
  apply iSup_le
  intro hx
  change ((∫⁻ y in ball z.1 z.2, f y + g y ∂μ) / μ (ball z.1 z.2)) ≤ _
  rw [lintegral_add_left hf, ENNReal.add_div]
  exact add_le_add (le_iSup_of_le z (le_iSup_of_le hx le_rfl))
    (le_iSup_of_le z (le_iSup_of_le hx le_rfl))

omit [BorelSpace X] in
theorem ballMaximal_const_le (μ : Measure X) (a : ℝ≥0∞)
    (hball : ∀ x r, 0 < r → μ (ball x r) ≠ 0 ∧ μ (ball x r) ≠ ∞) (x : X) :
    ballMaximal μ (fun _ => a) x ≤ a := by
  apply iSup_le
  intro z
  apply iSup_le
  intro hx
  have hb := hball z.1 z.2 (nonempty_ball.mp ⟨x, hx⟩)
  simp only [ballAverage, setLIntegral_const]
  rw [mul_div_assoc, ENNReal.div_self hb.1 hb.2, mul_one]

/-- Truncating the input sharpens weak `(1,1)` to the tail estimate needed for
strong `(p,p)`, without assuming that the maximal function is integrable. -/
theorem ballMaximal_truncated_weak [TopologicalSpace.SeparableSpace X]
    (μ : Measure X) {f : X → ℝ≥0∞} (hf : Measurable f) {D : ℝ≥0∞}
    (hball : ∀ x r, 0 < r → μ (ball x r) ≠ 0 ∧ μ (ball x r) ≠ ∞)
    (hdbl : ∀ x r, 0 < r → μ (ball x (5 * r)) ≤ D * μ (ball x r))
    {t : ℝ≥0∞} (ht0 : t ≠ 0) (httop : t ≠ ∞) :
    μ {x | t + t < ballMaximal μ f x} ≤
      D * t⁻¹ * ∫⁻ x in {x | t < f x}, f x ∂μ := by
  let g := {x | t < f x}.indicator f
  have hg : Measurable g := hf.indicator (measurableSet_lt measurable_const hf)
  have hfg : f ≤ fun x => t + g x := by
    intro x
    by_cases hx : t < f x
    · simp only [g, Set.indicator, Set.mem_ofPred_eq, ite_eq_left hx]
      exact le_add_left le_rfl
    · simp only [g, Set.indicator, Set.mem_ofPred_eq, ite_eq_right hx, add_zero]
      exact le_of_not_gt hx
  have hsub : {x | t + t < ballMaximal μ f x} ⊆ {x | t < ballMaximal μ g x} := by
    intro x hx
    have h := (ballMaximal_mono μ hfg x).trans
      (ballMaximal_add_le μ measurable_const hg x)
    have hbound : ballMaximal μ f x ≤ t + ballMaximal μ g x :=
      h.trans (add_le_add (ballMaximal_const_le μ t hball x) le_rfl)
    by_contra hnot
    exact (not_lt_of_ge (hbound.trans (add_le_add le_rfl (le_of_not_gt hnot)))) hx
  have hw := (measure_mono hsub).trans (ballMaximal_weak μ g hball hdbl ht0 httop)
  simpa only [g, lintegral_indicator (measurableSet_lt measurable_const hf)] using hw

/-- Strong `(p,p)` for the genuine all-balls maximal operator.  The factor two
is placed on the left to keep the constant transparent.  No finiteness of the
maximal function, nor even finiteness of the input moment, is assumed. -/
theorem ballMaximal_strong_scaled [TopologicalSpace.SeparableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ} (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) {p D : ℝ} (hp : 1 < p) (hD : 0 ≤ D)
    (hball : ∀ x r, 0 < r → μ (ball x r) ≠ 0 ∧ μ (ball x r) ≠ ∞)
    (hdbl : ∀ x r, 0 < r → μ (ball x (5 * r)) ≤ ENNReal.ofReal D * μ (ball x r)) :
    (∫⁻ x, (ballMaximal μ (fun y => ENNReal.ofReal (f y)) x / 2) ^ p ∂μ) ≤
      ENNReal.ofReal (D * p / (p - 1)) * ∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ := by
  let M := ballMaximal μ (fun y => ENNReal.ofReal (f y))
  let U : ℕ → X → ℝ≥0∞ := fun N x => min (M x / 2) N
  have hp0 : 0 < p := by linarith
  have hM : Measurable M := measurable_ballMaximal μ _
  have hU (N : ℕ) : Measurable (U N) := (hM.div_const 2).min measurable_const
  have hUtop (N : ℕ) (x : X) : U N x ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (min_le_right _ _) (by simp))
  have hN (N : ℕ) : (∫⁻ x, U N x ^ p ∂μ) ≤
      ENNReal.ofReal (D * p / (p - 1)) * ∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ := by
    have hu : Measurable (fun x => (U N x).toReal) := (hU N).ennreal_toReal
    have hw (t : ℝ) (ht : 0 < t) : μ {x | t < (U N x).toReal} ≤
        ENNReal.ofReal D / ENNReal.ofReal t *
          ∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ∂μ := by
      have hsub : {x | t < (U N x).toReal} ⊆
          {x | ENNReal.ofReal t + ENNReal.ofReal t < M x} := by
        intro x hx
        have htU : ENNReal.ofReal t < U N x := by
          rw [← ENNReal.ofReal_toReal (hUtop N x)]
          exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mpr hx
        have htM := htU.trans_le (min_le_left (M x / 2) (N : ℝ≥0∞))
        have htM' := (ENNReal.lt_div_iff_mul_lt
          (b := (2 : ℝ≥0∞)) (Or.inl (by norm_num)) (Or.inl (by norm_num))).mp htM
        change ENNReal.ofReal t + ENNReal.ofReal t < M x
        simpa only [mul_two] using htM'
      have hw' := (measure_mono hsub).trans
        (ballMaximal_truncated_weak μ hf.ennreal_ofReal hball hdbl
          (ENNReal.ofReal_ne_zero_iff.mpr ht) ENNReal.ofReal_ne_top)
      have hs : {x | ENNReal.ofReal t < ENNReal.ofReal (f x)} = {x | t < f x} := by
        ext x
        exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le
      simpa only [hs, div_eq_mul_inv] using hw'
    have h := power_moment_le_of_truncated_weak_bound μ hu hf
      (fun x => ENNReal.toReal_nonneg) hfn hp hD hw
    simpa only [ENNReal.ofReal_toReal (hUtop N _)] using h
  have hlim (x : X) : (⨆ N, U N x ^ p) = (M x / 2) ^ p := by
    have hh := (ENNReal.orderIsoRpow p hp0).map_iSup (fun N => U N x)
    change (⨆ N, U N x) ^ p = ⨆ N, U N x ^ p at hh
    rw [← hh]
    change (⨆ N : ℕ, (M x / 2) ⊓ (N : ℝ≥0∞)) ^ p = _
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  calc
    _ = ∫⁻ x, ⨆ N, U N x ^ p ∂μ := by simp_rw [hlim]; rfl
    _ = ⨆ N, ∫⁻ x, U N x ^ p ∂μ := by
      apply lintegral_iSup (fun N => (hU N).pow_const p)
      intro N K hNK x
      apply ENNReal.rpow_le_rpow _ hp0.le
      exact min_le_min le_rfl (by exact_mod_cast hNK)
    _ ≤ _ := iSup_le hN

theorem ballMaximal_strong_moment [TopologicalSpace.SeparableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ} (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) {p D : ℝ} (hp : 1 < p) (hD : 0 ≤ D)
    (hball : ∀ x r, 0 < r → μ (ball x r) ≠ 0 ∧ μ (ball x r) ≠ ∞)
    (hdbl : ∀ x r, 0 < r → μ (ball x (5 * r)) ≤ ENNReal.ofReal D * μ (ball x r)) :
    (∫⁻ x, ballMaximal μ (fun y => ENNReal.ofReal (f y)) x ^ p ∂μ) ≤
      (2 : ℝ≥0∞) ^ p * ENNReal.ofReal (D * p / (p - 1)) *
        ∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ := by
  have hp0 : 0 ≤ p := by linarith
  have he (a : ℝ≥0∞) : a ^ p = (2 : ℝ≥0∞) ^ p * (a / 2) ^ p := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0,
      ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
  conv_lhs => arg 2; ext x; rw [he]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0 (by norm_num))]
  have h := ballMaximal_strong_scaled μ hf hfn hp hD hball hdbl
  calc
    _ ≤ (2 : ℝ≥0∞) ^ p * (ENNReal.ofReal (D * p / (p - 1)) *
        ∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ) := by gcongr
    _ = _ := (mul_assoc _ _ _).symm

/-- Strong `Lᵖ` operator bound for all ball averages. -/
theorem eLpNorm_ballMaximal_le [TopologicalSpace.SeparableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ} (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) {p D : ℝ} (hp : 1 < p) (hD : 0 ≤ D)
    (hball : ∀ x r, 0 < r → μ (ball x r) ≠ 0 ∧ μ (ball x r) ≠ ∞)
    (hdbl : ∀ x r, 0 < r → μ (ball x (5 * r)) ≤ ENNReal.ofReal D * μ (ball x r)) :
    eLpNorm (ballMaximal μ (fun y => ENNReal.ofReal (f y))) (ENNReal.ofReal p) μ ≤
      (2 * ENNReal.ofReal (D * p / (p - 1)) ^ (1 / p)) * eLpNorm f (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := by linarith
  have hq : 0 ≤ 1 / p := (one_div_pos.mpr hp0).le
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
      (measurable_ballMaximal μ _).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
      hf.aestronglyMeasurable]
  simp only [enorm_eq_self, ENNReal.toReal_ofReal hp0.le]
  simp_rw [Real.enorm_eq_ofReal (hfn _)]
  have h := ENNReal.rpow_le_rpow (ballMaximal_strong_moment μ hf hfn hp hD hball hdbl) hq
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq, ENNReal.mul_rpow_of_nonneg _ _ hq,
    ← ENNReal.rpow_mul, show p * (1 / p) = 1 by field_simp, ENNReal.rpow_one] at h
  exact h

theorem memLp_ballMaximal [TopologicalSpace.SeparableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ} (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) {p D : ℝ} (hp : 1 < p) (hD : 0 ≤ D)
    (hball : ∀ x r, 0 < r → μ (ball x r) ≠ 0 ∧ μ (ball x r) ≠ ∞)
    (hdbl : ∀ x r, 0 < r → μ (ball x (5 * r)) ≤ ENNReal.ofReal D * μ (ball x r))
    (hfp : MemLp f (ENNReal.ofReal p) μ) :
    MemLp (ballMaximal μ (fun y => ENNReal.ofReal (f y))) (ENNReal.ofReal p) μ := by
  apply (eLpNorm_ballMaximal_le μ hf hfn hp hD hball hdbl).trans_lt
  apply ENNReal.mul_lt_top _ hfp
  have hq : 0 ≤ 1 / p := by positivity
  exact ENNReal.mul_lt_top (by norm_num)
    (ENNReal.rpow_lt_top_of_nonneg hq ENNReal.ofReal_ne_top)

end OAI.Analysis.Fourier.SquareFunction
