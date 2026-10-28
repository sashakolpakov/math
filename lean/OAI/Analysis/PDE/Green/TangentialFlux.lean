import OAI.Analysis.PDE.Green.CutoffIntegral

/-! Tangential-flux integration by parts from smooth cutoffs and dominated
convergence, without postulating a surface divergence theorem. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory Measure
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_boundaryCutoff {r : E → ℝ} (hr : ContDiff ℝ 1 r) (k : ℕ) :
    ContDiff ℝ 1 (fun x ↦ boundaryCutoff (r x) k) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul hr)

theorem fderiv_boundaryCutoff {r : E → ℝ} (hr : ContDiff ℝ 1 r)
    (k : ℕ) (x v : E) :
    fderiv ℝ (fun y ↦ boundaryCutoff (r y) k) x v =
      (-((k : ℝ) + 1) * deriv Real.smoothTransition (-((k : ℝ) + 1) * r x)) *
        fderiv ℝ r x v := by
  have hi := ((hr.differentiable (by norm_num)) x).hasFDerivAt.const_mul (-((k : ℝ) + 1))
  have ho := ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
    (-((k : ℝ) + 1) * r x)).hasDerivAt
  have he := congrArg (fun L : E →L[ℝ] ℝ ↦ L v) (ho.comp_hasFDerivAt x hi).fderiv
  simpa only [boundaryCutoff, Function.comp_def, _root_.smul_apply,
    smul_eq_mul, mul_assoc, mul_left_comm]
    using he

theorem hasCompactSupport_boundaryCutoff [FiniteDimensional ℝ E]
    {r : E → ℝ} (hb : Bornology.IsBounded {x | r x < 0}) (k : ℕ) :
    HasCompactSupport (fun x ↦ boundaryCutoff (r x) k) := by
  have hs : Function.support (fun x ↦ boundaryCutoff (r x) k) ⊆ {x | r x < 0} := by
    intro x hx
    by_contra hn
    exact hx (boundaryCutoff_zero (le_of_not_gt hn) k)
  exact Metric.isCompact_of_isClosed_isBounded isClosed_closure (hb.subset hs).closure

/-- A vector field has zero total divergence when its defining-function normal
component is `r` times an integrable quotient. The quotient condition is the
Hadamard-division form of boundary tangency, not a Green-identity assumption. -/
theorem integral_divergence_zero_of_normal_factor [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)]
    {I : Type*} [Fintype I] (d : I → E) (F : I → E → ℝ)
    (hF : ∀ i, ContDiff ℝ 1 (F i)) {r b : E → ℝ} (hr : ContDiff ℝ 1 r)
    (hb : Bornology.IsBounded {x | r x < 0})
    (hbi : IntegrableOn b {x | r x < 0})
    (hfactor : ∀ x, (∑ i, fderiv ℝ r x (d i) * F i x) = r x * b x) :
    (∫ x in {x | r x < 0}, ∑ i, fderiv ℝ (F i) x (d i)) = 0 := by
  let S := {x : E | r x < 0}
  have hS : MeasurableSet S := isOpen_lt hr.continuous continuous_const |>.measurableSet
  let divF := fun x ↦ ∑ i, fderiv ℝ (F i) x (d i)
  have hdc : Continuous divF := continuous_finsetSum _ (fun i _ ↦ continuous_directional (hF i) (d i))
  have hdi : IntegrableOn divF S := OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb hdc
  have hpath (k : ℕ) :
      (∫ x in S, boundaryCutoff (r x) k * divF x) =
        -(∫ x in S, transitionSlope (-((k : ℝ) + 1) * r x) * b x) := by
    have hg := integral_divergence_by_parts (μ := volume) (contDiff_boundaryCutoff hr k)
      (hasCompactSupport_boundaryCutoff hb k) d F hF
    have hflux (x : E) :
        (∑ i, fderiv ℝ (fun y ↦ boundaryCutoff (r y) k) x (d i) * F i x) =
          transitionSlope (-((k : ℝ) + 1) * r x) * b x := by
      simp_rw [fderiv_boundaryCutoff hr]
      calc
        _ = (-((k : ℝ) + 1) * deriv Real.smoothTransition (-((k : ℝ) + 1) * r x)) *
            (∑ i, fderiv ℝ r x (d i) * F i x) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [hfactor]; unfold transitionSlope; ring
    simp_rw [hflux] at hg
    have hleft : (∫ x, boundaryCutoff (r x) k * divF x) =
        ∫ x in S, boundaryCutoff (r x) k * divF x := by
      rw [← integral_indicator hS]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      by_cases hx : x ∈ S
      · simp [hx]
      · have hrx : 0 ≤ r x := le_of_not_gt hx
        simp [hx, boundaryCutoff_zero hrx k]
    have hright : (∫ x, transitionSlope (-((k : ℝ) + 1) * r x) * b x) =
        ∫ x in S, transitionSlope (-((k : ℝ) + 1) * r x) * b x := by
      rw [← integral_indicator hS]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      by_cases hx : x ∈ S
      · simp [hx]
      · have hrx : 0 ≤ r x := le_of_not_gt hx
        have ht : -((k : ℝ) + 1) * r x ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hrx
        simp only [Set.indicator_of_notMem hx, transitionSlope_zero_nonpos ht, zero_mul]
    change (∫ x, boundaryCutoff (r x) k * divF x) = _ at hg
    rw [hleft, hright] at hg
    exact hg
  have hlimit := integral_boundaryCutoff_tendsto hr.continuous hdc hdi (fun _ hx ↦ hx) hS
  have hzero := (integral_transitionSlope_tendsto_zero hr.continuous hbi).neg
  have ht : Tendsto (fun k : ℕ ↦ ∫ x in S, boundaryCutoff (r x) k * divF x) atTop (𝓝 0) := by
    simpa only [hpath, neg_zero] using hzero
  exact tendsto_nhds_unique hlimit ht

theorem integrableOn_div_of_bound [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)]
    {S : Set E} (hS : MeasurableSet S) (hb : Bornology.IsBounded S)
    {r q : E → ℝ} (hr : Continuous r) (hq : Continuous q) (C : ℝ)
    (hrne : ∀ x ∈ S, r x ≠ 0) (hbound : ∀ x ∈ S, ‖q x‖ ≤ C * ‖r x‖) :
    IntegrableOn (fun x ↦ q x / r x) S := by
  have hsc : IsCompact (closure S) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  have : IsFiniteMeasure (volume.restrict S) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono subset_closure) hsc.measure_lt_top⟩
  apply (integrable_const C).mono' (hq.measurable.div hr.measurable).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hS] with x hx
  change ‖q x / r x‖ ≤ C
  rw [norm_div]
  exact (div_le_iff₀ (norm_pos_iff.mpr (hrne x hx))).mpr (hbound x hx)

/-- A quantitative vanishing bound for the normal flux suffices; no
continuity of its quotient is assumed. -/
theorem integral_divergence_zero_of_normal_bound [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)]
    {I : Type*} [Fintype I] (d : I → E) (F : I → E → ℝ)
    (hF : ∀ i, ContDiff ℝ 1 (F i)) {r : E → ℝ} (hr : ContDiff ℝ 1 r)
    (hb : Bornology.IsBounded {x | r x < 0}) (C : ℝ)
    (hzero : ∀ x, r x = 0 → (∑ i, fderiv ℝ r x (d i) * F i x) = 0)
    (hbound : ∀ x, r x < 0 → ‖∑ i, fderiv ℝ r x (d i) * F i x‖ ≤ C * ‖r x‖) :
    (∫ x in {x | r x < 0}, ∑ i, fderiv ℝ (F i) x (d i)) = 0 := by
  let q := fun x ↦ ∑ i, fderiv ℝ r x (d i) * F i x
  have hq : Continuous q := continuous_finsetSum _ (fun i _ ↦
    (continuous_directional hr (d i)).mul (hF i).continuous)
  have hS : MeasurableSet {x | r x < 0} :=
    (isOpen_lt hr.continuous continuous_const).measurableSet
  have hbi := integrableOn_div_of_bound hS hb hr.continuous hq C
    (fun _ hx ↦ ne_of_lt hx) hbound
  apply integral_divergence_zero_of_normal_factor d F hF hr hb hbi
  intro x
  change q x = r x * (q x / r x)
  by_cases hx : r x = 0
  · simp only [hx, zero_mul]
    exact hzero x hx
  · field_simp

end OAI.Analysis.PDE.Green
